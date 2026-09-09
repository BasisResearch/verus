#![feature(rustc_private)]
#![cfg(unix)]

use serde_json::{Value, json};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::time::{Duration, Instant};
use tempfile::TempDir;

const SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    spec fn recursive(n: nat) -> nat
        decreases n,
    {
        if n == 0 { 0 } else { recursive((n - 1) as nat) }
    }

    proof fn failing(x: int) { assert(x > 0); }

    proof fn passing() { assert(recursive(0) == 0); }
}
"#;

// Keep the protocol subprocess bounded even when a regression stops it from
// producing a reply. stderr goes to a file so diagnostics cannot fill a pipe.
struct Worker {
    child: Child,
    input: Option<ChildStdin>,
    replies: Receiver<String>,
    dir: TempDir,
}

impl Worker {
    fn start(source: &str, options: &[&str]) -> Self {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join("fixture.rs"), source).unwrap();
        let current = std::env::current_exe().unwrap();
        let binary = current.parent().unwrap().parent().unwrap().join("rust_verify");
        let solver = PathBuf::from(std::env::var_os("VERUS_CVC5_PATH").expect("cvc5 path"));
        let solver = fs::canonicalize(solver).unwrap();
        let wrapper = dir.path().join("solver.sh");
        fs::write(
            &wrapper,
            "#!/bin/sh\nset -eu\nprintf '%s\\n' \"$$\" >> \"$RESIDENT_LAUNCH_LOG\"\nexec \"$RESIDENT_SOLVER\" \"$@\"\n",
        )
        .unwrap();
        fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o700)).unwrap();
        let mut child = Command::new(binary)
            .args(["--mcp", "-V", "cvc5", "--resident", "--crate-type=lib"])
            .arg(dir.path().join("fixture.rs"))
            .args(["--log-all", "--log-dir"])
            .arg(dir.path().join("logs"))
            .args(options)
            .env("VERUS_CVC5_PATH", wrapper)
            .env("RESIDENT_SOLVER", solver)
            .env("RESIDENT_LAUNCH_LOG", dir.path().join("launches"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(fs::File::create(dir.path().join("stderr")).unwrap())
            .spawn()
            .unwrap();
        let input = child.stdin.take();
        let stdout = child.stdout.take().unwrap();
        let (sender, replies) = mpsc::channel();
        std::thread::spawn(move || {
            for line in BufReader::new(stdout).lines() {
                if sender.send(line.unwrap()).is_err() {
                    break;
                }
            }
        });
        Self { child, input, replies, dir }
    }

    fn receive(&self) -> Value {
        let line = self
            .replies
            .recv_timeout(Duration::from_secs(60))
            .unwrap_or_else(|error| panic!("resident reply: {error}; stderr: {}", self.stderr()));
        let reply: Value =
            serde_json::from_str(&line).expect("stdout must contain only JSON lines");
        eprintln!("{reply}");
        reply
    }

    fn send(&mut self, request: Value) -> Value {
        self.raw(&format!("{request}\n"));
        self.receive()
    }

    fn raw(&mut self, text: &str) {
        let input = self.input.as_mut().unwrap();
        input.write_all(text.as_bytes()).unwrap();
        input.flush().unwrap();
    }

    fn stderr(&self) -> String {
        fs::read_to_string(self.dir.path().join("stderr")).unwrap()
    }

    fn finish(&mut self, success: bool) {
        self.input.take();
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                assert_eq!(status.success(), success, "{}", self.stderr());
                break;
            }
            assert!(Instant::now() < deadline, "resident failed to exit");
            std::thread::sleep(Duration::from_millis(10));
        }
        assert!(self.replies.recv_timeout(Duration::from_secs(1)).is_err());
        self.assert_solvers_gone();
    }

    fn assert_solvers_gone(&self) {
        if let Ok(launches) = fs::read_to_string(self.dir.path().join("launches")) {
            for pid in launches.lines() {
                let alive =
                    Command::new("kill").args(["-0", pid]).output().unwrap().status.success();
                assert!(!alive, "solver {} survived shutdown", pid);
            }
        }
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn query_id(ready: &Value, name: &str) -> Value {
    ready["buckets"][0]["queries"]
        .as_array()
        .unwrap()
        .iter()
        .find(|query| query["function"].as_str().unwrap().ends_with(name))
        .unwrap_or_else(|| panic!("missing {}: {}", name, ready))["id"]
        .clone()
}

#[test]
fn resident_rechecks_preserve_query_scopes_and_solver_process() {
    let mut worker = Worker::start(SOURCE, &[]);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready");
    assert_eq!(ready["protocol"], 2);
    assert_eq!(ready["invocation_succeeded"], false);
    assert_eq!(ready["process_id"], worker.child.id());
    let session = ready["session"].clone();
    let listed = worker.send(json!({"command": "list"}));
    assert_eq!(listed["buckets"], ready["buckets"]);
    for (name, expected) in [
        ("::failing", "invalid"),
        ("::passing", "valid"),
        ("::recursive", "valid"),
        ("::passing", "valid"),
        ("::failing", "invalid"),
    ] {
        let query = query_id(&ready, name);
        let result = worker
            .send(json!({"command": "check", "session": session, "bucket": 0, "query": query}));
        assert_eq!(result["event"], "checked");
        assert_eq!(result["session"], session);
        assert_eq!(result["query"], query);
        assert_eq!(result["result"], expected);
        if expected == "invalid" {
            assert!(!result["diagnostics"].as_array().unwrap().is_empty());
            assert!(result["assert_id"].is_array());
            assert!(result.to_string().contains("fixture.rs"));
        }
    }
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.assert_solvers_gone();
    // The original fixture fails verification; successful rechecks do not
    // overwrite the original crate result or process exit status.
    worker.finish(false);
    let launches = fs::read_to_string(worker.dir.path().join("launches")).unwrap();
    assert_eq!(launches.lines().count(), 1, "{launches}");
    let mut checks = 0;
    for entry in fs::read_dir(worker.dir.path().join("logs")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|ext| ext == "smt2") {
            let log = fs::read_to_string(path).unwrap();
            assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
            checks += log.matches("(check-sat)").count();
        }
    }
    assert!(checks >= 8, "expected initial checks and five resident rechecks, got {}", checks);
    eprintln!("one verifier process, one cvc5 launch, {checks} checks, balanced scopes");
}

#[test]
fn resident_rejects_bad_requests_and_accepts_eof() {
    let mut worker = Worker::start("use vstd::prelude::*; verus! { proof fn passing() {} }", &[]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    worker.raw("not json\n");
    assert_eq!(worker.receive()["event"], "error");
    for request in [
        json!({"command": "check", "session": "stale", "bucket": 0, "query": 0}),
        json!({"command": "close", "session": "stale"}),
        json!({"command": "check", "session": session, "bucket": 0, "query": 99999}),
        json!({"command": "check", "session": session, "bucket": 0, "query": -1}),
        json!({"command": "check", "session": session, "bucket": 0, "query": 0, "assertion": "false"}),
        json!({"command": "check", "session": session, "bucket": 99999, "query": 0}),
        json!({"command": "check", "session": session, "query": 0}),
        json!({"command": "list", "session": "stale"}),
    ] {
        assert_eq!(worker.send(request)["event"], "error");
    }
    // A session token is optional on list, and honoured when one is sent.
    assert_eq!(worker.send(json!({"command": "list"}))["event"], "queries");
    assert_eq!(worker.send(json!({"command": "list", "session": session}))["event"], "queries");
    let checked =
        worker.send(json!({"command": "check", "session": session, "bucket": 0, "query": 0}));
    assert_eq!(checked["result"], "valid");
    // Restoration is reported apart from the check it precedes.
    assert!(checked["restore_ms"].is_number(), "{}", checked);
    worker.finish(true);
}

#[test]
fn resident_rejects_unsupported_modes() {
    for options in [
        vec!["--output-json"],
        vec!["--smt-option", "global-declarations=true"],
        vec!["-V", "provenance"],
    ] {
        let mut worker = Worker::start(SOURCE, &options);
        worker.finish(false);
        assert!(worker.stderr().contains("--resident requires"), "{}", worker.stderr());
        assert!(!worker.dir.path().join("launches").exists());
    }
}

#[test]
fn resident_rejects_incomplete_preparation_cleanly() {
    for (source, expected) in [
        (
            "use vstd::prelude::*; verus! { proof fn broken() { missing(); } }",
            "cannot find function",
        ),
        (
            "use vstd::prelude::*; verus! { mod a { proof fn ok() {} } mod b { use super::*; proof fn f(x: u32) { assert(x & 0 == 0) by(bit_vector); } } }",
            "--resident does not support specialised prover queries",
        ),
    ] {
        for threads in ["1", "2"] {
            let mut worker = Worker::start(source, &["--num-threads", threads]);
            worker.finish(false);
            assert!(worker.stderr().contains(expected), "{}", worker.stderr());
            assert!(!worker.stderr().contains("panicked"), "{}", worker.stderr());
        }
    }
}

const MULTI_BUCKET_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    mod a {
        use super::*;
        spec fn value() -> int { 1 }
        proof fn check() { assert(value() == 1); }
    }
    mod b {
        use super::*;
        spec fn value() -> int { 2 }
        proof fn check() { assert(value() == 1); }
        proof fn extra() {}
    }
}
"#;

#[test]
fn resident_routes_all_buckets_after_serial_and_parallel_preparation() {
    let mut catalogue = None;
    for threads in ["1", "2"] {
        let mut worker = Worker::start(MULTI_BUCKET_SOURCE, &["--num-threads", threads]);
        let ready = worker.receive();
        let session = &ready["session"];
        let buckets = ready["buckets"].as_array().unwrap();
        assert_eq!(buckets.len(), 2);
        assert_eq!(buckets[0]["name"], "module a");
        assert_eq!(buckets[1]["name"], "module b");
        // Both modules have query ordinal zero. Its meaning is bucket-local.
        for (bucket, expected) in [(0, "valid"), (1, "invalid"), (0, "valid"), (1, "invalid")] {
            let result = worker.send(
                json!({"command": "check", "session": session, "bucket": bucket, "query": 0}),
            );
            assert_eq!(result["bucket"], bucket);
            assert_eq!(result["result"], expected);
        }
        let extra = buckets[1]["queries"]
            .as_array()
            .unwrap()
            .iter()
            .find(|query| query["function"].as_str().unwrap().ends_with("::extra"))
            .unwrap()["id"]
            .clone();
        assert_eq!(
            worker
                .send(json!({"command": "check", "session": session, "bucket": 0, "query": extra}))
                ["event"],
            "error"
        );
        assert_eq!(
            worker
                .send(json!({"command": "check", "session": session, "bucket": 1, "query": extra}))
                ["result"],
            "valid"
        );
        // Stable catalogue despite different worker completion order. Source
        // span filenames contain temporary directories, so compare identities.
        let identities: Vec<_> = buckets
            .iter()
            .map(|bucket| {
                (
                    bucket["id"].clone(),
                    bucket["name"].clone(),
                    bucket["queries"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|query| {
                            (query["id"].clone(), query["function"].clone(), query["kind"].clone())
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .collect();
        if let Some(previous) = &catalogue {
            assert_eq!(previous, &identities);
        }
        catalogue = Some(identities);
        assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
        worker.assert_solvers_gone();
        worker.finish(false);
        let launches = fs::read_to_string(worker.dir.path().join("launches")).unwrap();
        assert_eq!(launches.lines().count(), 2);
        eprintln!(
            "{threads} compilation threads: two buckets, two solver launches, five rechecks, all children closed"
        );
    }
}

#[test]
fn resident_filters_buckets_and_closes_all_on_eof() {
    let mut worker = Worker::start(MULTI_BUCKET_SOURCE, &["--verify-module", "a"]);
    let ready = worker.receive();
    assert_eq!(ready["buckets"].as_array().unwrap().len(), 1);
    assert_eq!(ready["buckets"][0]["name"], "module a");
    assert_eq!(ready["invocation_succeeded"], true);
    worker.finish(true);

    let mut worker = Worker::start(MULTI_BUCKET_SOURCE, &["--num-threads", "2"]);
    assert_eq!(worker.receive()["buckets"].as_array().unwrap().len(), 2);
    worker.finish(false);
}

#[test]
fn resident_retains_function_buckets_alongside_module_buckets() {
    let source = r#"
        use vstd::prelude::*;
        verus! {
            proof fn regular() {}
            #[verifier::spinoff_prover]
            proof fn isolated() {}
        }
    "#;
    let mut worker = Worker::start(source, &["--num-threads", "2"]);
    let ready = worker.receive();
    let buckets = ready["buckets"].as_array().unwrap();
    assert_eq!(buckets.len(), 2);
    assert_eq!(buckets[0]["name"], "root module");
    assert!(buckets[1]["name"].as_str().unwrap().contains("function fixture::isolated"));
    for bucket in buckets {
        assert_eq!(worker.send(json!({"command": "check", "session": ready["session"], "bucket": bucket["id"], "query": 0}))["result"], "valid");
    }
    worker.finish(true);
    assert_eq!(fs::read_to_string(worker.dir.path().join("launches")).unwrap().lines().count(), 2);
}
