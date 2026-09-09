#![feature(rustc_private)]
#![cfg(unix)]

use serde_json::{Value, json};
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::Shutdown;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
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

/// The harness's write half of the worker's protocol channel.
///
/// Ending a session means EOF at the worker, and the two transports reach that
/// differently, so the write half cannot just be a `Write`. Taking `self` by
/// value keeps a closed endpoint from being written to again, which also means
/// this trait is not object safe: `Worker` takes it as a type parameter rather
/// than boxing it.
trait Endpoint: Write {
    fn close(self);
}

impl Endpoint for ChildStdin {
    /// Dropping the pipe closes the worker's stdin.
    fn close(self) {}
}

impl Endpoint for UnixStream {
    /// The reader thread holds a `try_clone` of this same connection, so
    /// dropping this handle closes nothing and the worker would wait forever.
    /// A session ended with `close` has already gone; the shutdown then fails
    /// having reached the state it wanted, and `finish` asserts on the exit
    /// that actually matters.
    fn close(self) {
        let _ = self.shutdown(Shutdown::Write);
    }
}

// Keep the protocol subprocess bounded even when a regression stops it from
// producing a reply. stderr goes to a file so diagnostics cannot fill a pipe.
struct Worker<E: Endpoint> {
    child: Child,
    input: Option<E>,
    replies: Receiver<String>,
    dir: TempDir,
}

/// Everything both transports set up before they diverge.
struct Spawned {
    child: Child,
    dir: TempDir,
    listener: Option<UnixListener>,
}

impl Worker<ChildStdin> {
    fn start(source: &str, options: &[&str]) -> Self {
        let Spawned { mut child, dir, .. } = spawn(source, options, false);
        let input = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        Self::assemble(child, dir, input, Box::new(stdout))
    }
}

impl Worker<UnixStream> {
    fn start_socket(source: &str, options: &[&str]) -> Self {
        let Spawned { mut child, dir, listener } = spawn(source, options, true);
        let stream = accept(listener.expect("socket transport binds a listener"), &mut child, &dir);
        let input = stream.try_clone().unwrap();
        Self::assemble(child, dir, input, Box::new(stream))
    }
}

/// Wait for the worker to dial back, failing fast if it dies while we wait.
fn accept(listener: UnixListener, child: &mut Child, dir: &TempDir) -> UnixStream {
    listener.set_nonblocking(true).unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        match listener.accept() {
            Ok((stream, _)) => {
                stream.set_nonblocking(false).unwrap();
                return stream;
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                assert!(
                    child.try_wait().unwrap().is_none(),
                    "{}",
                    fs::read_to_string(dir.path().join("stderr")).unwrap()
                );
                if Instant::now() >= deadline {
                    child.kill().unwrap();
                    child.wait().unwrap();
                    panic!("socket startup timeout");
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            Err(e) => panic!("socket accept: {}", e),
        }
    }
}

fn spawn(source: &str, options: &[&str], socket: bool) -> Spawned {
    let dir = tempfile::tempdir().unwrap();
    let socket_path = dir.path().join("worker.sock");
    let listener = socket.then(|| UnixListener::bind(&socket_path).unwrap());
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
    let mut command = Command::new(binary);
    command
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
        .stderr(fs::File::create(dir.path().join("stderr")).unwrap());
    if socket {
        command
            .env("VERUS_RESIDENT_SOCKET", &socket_path)
            .stdin(Stdio::null())
            .stdout(fs::File::create(dir.path().join("stdout")).unwrap());
    }
    let child = command.spawn().unwrap();
    Spawned { child, dir, listener }
}

impl<E: Endpoint> Worker<E> {
    fn assemble(
        child: Child,
        dir: TempDir,
        input: E,
        stdout: Box<dyn std::io::Read + Send>,
    ) -> Self {
        let (sender, replies) = mpsc::channel();
        std::thread::spawn(move || {
            for line in BufReader::new(stdout).lines() {
                if sender.send(line.unwrap()).is_err() {
                    break;
                }
            }
        });
        Self { child, input: Some(input), replies, dir }
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
        if let Some(input) = self.input.take() {
            input.close();
        }
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

impl<E: Endpoint> Drop for Worker<E> {
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
            let diagnostics = result["diagnostics"].as_array().unwrap();
            assert!(!diagnostics.is_empty());
            // Severity is the level the original invocation reports at, spelled
            // the way every other enum in the protocol is spelled.
            assert_eq!(diagnostics[0]["level"], "error", "{}", result);
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

/// Each spawned context must survive initial verification and be reused even
/// when checks alternate between termination, body and failed queries.
#[test]
fn resident_spinoff_all_reuses_original_solvers() {
    for eof in [false, true] {
        let mut worker = Worker::start(SOURCE, &["-V", "spinoff-all"]);
        let ready = worker.receive();
        assert_eq!(ready["spinoff_all"], true);
        let launches = fs::read_to_string(worker.dir.path().join("launches")).unwrap();
        assert!(launches.lines().count() >= 3, "{}", launches);
        for (name, expected) in [
            ("::passing", "valid"),
            ("::failing", "invalid"),
            ("::recursive", "valid"),
            ("::failing", "invalid"),
            ("::passing", "valid"),
        ] {
            let result = worker.send(json!({
                "command": "check", "session": ready["session"],
                "bucket": 0, "query": query_id(&ready, name),
            }));
            assert_eq!(result["result"], expected, "{result}");
            assert!(result["provenance"].is_null());
        }
        if !eof {
            assert_eq!(
                worker.send(json!({"command":"close","session":ready["session"]}))["event"],
                "closed"
            );
            worker.assert_solvers_gone();
        }
        worker.finish(false);
        worker.assert_solvers_gone();
        assert_eq!(fs::read_to_string(worker.dir.path().join("launches")).unwrap(), launches);
    }
}

/// Identical local hypothesis and quantifier ordinals in different buckets
/// must resolve through that bucket's source maps after the compiler exits.
#[test]
fn resident_provenance_keeps_bucket_symbols_with_and_without_spinoff() {
    let module = r#"
        use super::*;
        pub uninterp spec fn f(i: int) -> int;
        pub uninterp spec fn g(i: int) -> int;
        pub broadcast proof fn ax_f_nonneg(i: int)
            ensures #[trigger] f(i) >= 0,
        { admit(); }
        proof fn check(x: int, y: int)
            requires x > 3, y == f(x),
                forall|j: int| 0 <= j < x ==> #[trigger] g(j) >= j,
        {
            broadcast use ax_f_nonneg;
            assert(x > 2);
            assert(y >= 1);
            assert(g(2) >= 2);
        }
        proof fn passing(x: int) requires x > 3, { assert(x > 2); }
    "#;
    let source =
        format!("use vstd::prelude::*; verus! {{ mod a {{{module}}} mod b {{{module}}} }}");
    for threads in ["1", "2"] {
        for spinoff in [false, true] {
            let mut options = vec!["-V", "provenance", "--num-threads", threads];
            if spinoff {
                options.extend(["-V", "spinoff-all"]);
            }
            let mut worker = Worker::start(&source, &options);
            let ready = worker.receive();
            assert_eq!(ready["provenance"], true, "{ready}");
            assert_eq!(ready["spinoff_all"], spinoff);
            let buckets = ready["buckets"].as_array().unwrap();
            assert_eq!(buckets.len(), 2, "{ready}");
            let launches = fs::read_to_string(worker.dir.path().join("launches")).unwrap();
            for (bucket, name, expected) in [
                (1, "check", "invalid"),
                (0, "passing", "valid"),
                (0, "check", "invalid"),
                (1, "passing", "valid"),
                (1, "check", "invalid"),
            ] {
                let function = format!("::{}::{name}", if bucket == 0 { "a" } else { "b" });
                let query = buckets[bucket]["queries"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|q| {
                        q["function"].as_str().unwrap().ends_with(&function) && q["kind"] == "body"
                    })
                    .unwrap();
                let checked = worker.send(json!({"command":"check", "session":ready["session"], "bucket":bucket, "query":query["id"]}));
                assert_eq!(checked["result"], expected, "{checked}");
                let provenance = &checked["provenance"];
                assert_eq!(provenance["result"], expected, "{checked}");
                assert_eq!(provenance["round"], 0);
                assert_eq!(provenance["span"], query["span"]);
                let requires: Vec<_> = provenance["hypotheses"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .filter(|h| h["kind"] == "requires")
                    .collect();
                assert!(!requires.is_empty(), "{}", checked);
                for hyp in requires {
                    assert!(hyp["owner"].as_str().unwrap().ends_with(&function), "{}", hyp);
                    assert!(hyp["span"].as_str().unwrap().contains("fixture.rs"), "{}", hyp);
                }
                if name == "check" {
                    let axiom = format!("::{}::ax_f_nonneg", if bucket == 0 { "a" } else { "b" });
                    let instantiations = provenance["instantiations"].as_array().unwrap();
                    let inst = instantiations
                        .iter()
                        .find(|i| i["fun"].as_str().is_some_and(|f| f.ends_with(&axiom)))
                        .unwrap_or_else(|| panic!("no broadcast axiom: {}", checked));
                    assert!(inst["site"].as_str().unwrap().contains(&axiom), "{}", inst);
                    assert_eq!(inst["inside"]["owner"], inst["fun"]);
                    assert!(
                        inst["terms"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .any(|t| t.as_str().unwrap().contains("x")),
                        "{}",
                        inst
                    );
                }
            }
            assert_eq!(
                worker.send(json!({"command":"close", "session":ready["session"]}))["event"],
                "closed"
            );
            worker.finish(false);
            worker.assert_solvers_gone();
            assert_eq!(fs::read_to_string(worker.dir.path().join("launches")).unwrap(), launches);
        }
    }
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
        vec!["--no-verify"],
    ] {
        let mut worker = Worker::start(SOURCE, &options);
        worker.finish(false);
        assert!(worker.stderr().contains("--resident"), "{}", worker.stderr());
        assert!(!worker.dir.path().join("launches").exists());
    }
}

// Compilation reports a failed recommends check as a warning, so a recheck of
// the retained query reports one too. `invalid` is the right AIR verdict for an
// unproved recommendation; only its severity was wrong.
#[test]
fn resident_recheck_keeps_recommends_at_warning_severity() {
    let source = r#"
        use vstd::prelude::*;
        verus! {
            spec fn positive(x: int) -> int
                recommends x > 0,
            {
                x
            }

            spec(checked) fn warning_only() -> int {
                positive(0)
            }
        }
    "#;
    let mut worker = Worker::start(source, &[]);
    let ready = worker.receive();
    // A warning is not an error, so the original invocation still succeeded.
    assert_eq!(ready["invocation_succeeded"], true, "{}", worker.stderr());
    let query = ready["buckets"][0]["queries"]
        .as_array()
        .unwrap()
        .iter()
        .find(|query| query["kind"] == "recommends")
        .unwrap_or_else(|| panic!("no recommends query: {}", ready))["id"]
        .clone();
    let checked = worker.send(
        json!({"command": "check", "session": ready["session"], "bucket": 0, "query": query}),
    );
    assert_eq!(checked["result"], "invalid", "{}", checked);
    assert_eq!(checked["diagnostics"][0]["level"], "warning", "{}", checked);
    worker.finish(true);
}

// A specialised prover in a function the filter excludes is not this session's
// problem: its query is neither checked nor retained, so preparation must
// still succeed. Without the filter, the same file is rejected (above).
#[test]
fn resident_ignores_specialised_provers_in_filtered_out_functions() {
    let source = r#"
        use vstd::prelude::*;
        verus! {
            mod a {
                use super::*;
                proof fn plain() { assert(1int + 1 == 2); }
                proof fn bits(x: u32) { assert(x & 0 == 0) by(bit_vector); }
            }
        }
    "#;
    let mut worker =
        Worker::start(source, &["--verify-only-module", "a", "--verify-function", "plain"]);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready", "{}", worker.stderr());
    let queries = ready["buckets"][0]["queries"].as_array().unwrap();
    assert_eq!(queries.len(), 1, "{}", ready);
    assert!(queries[0]["function"].as_str().unwrap().ends_with("::plain"), "{}", ready);
    let checked = worker
        .send(json!({"command": "check", "session": ready["session"], "bucket": 0, "query": 0}));
    assert_eq!(checked["result"], "valid");
    worker.finish(true);
}

#[test]
fn resident_socket_separates_output_and_reports_inputs() {
    let mut worker = Worker::start_socket(SOURCE, &["--output-json", "--time"]);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready");
    assert!(
        ready["input_files"]
            .as_array()
            .unwrap()
            .iter()
            .any(|p| p.as_str().unwrap().ends_with("fixture.rs")),
        "{}",
        ready
    );
    let session = ready["session"].clone();
    let query = query_id(&ready, "::passing");
    assert_eq!(
        worker.send(json!({"command":"check", "session":session,"bucket":0,"query":query}))["result"],
        "valid"
    );
    assert_eq!(worker.send(json!({"command":"close", "session":session}))["event"], "closed");
    worker.finish(false);
    let stdout = fs::read_to_string(worker.dir.path().join("stdout")).unwrap();
    let output: Value =
        serde_json::from_str(&stdout).expect("ordinary JSON output remains separate");
    assert!(output.is_object());
}

// EOF releases every bucket over either transport. The socket needs a real
// shutdown to produce it: the reader thread holds a second handle on the same
// connection, so dropping the write half closes nothing.
#[test]
fn resident_socket_closes_on_eof() {
    let mut worker = Worker::start_socket(SOURCE, &[]);
    assert_eq!(worker.receive()["event"], "ready");
    worker.finish(false);
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
