#![feature(rustc_private)]
#![cfg(unix)]

use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::Shutdown;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
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
        Self::start_with_solver(source, options, DEFAULT_SOLVER_WRAPPER)
    }

    fn start_with_env(source: &str, options: &[&str], envs: &[(&str, &str)]) -> Self {
        let Spawned { mut child, dir, .. } =
            spawn(source, options, false, DEFAULT_SOLVER_WRAPPER, envs);
        let input = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        Self::assemble(child, dir, input, Box::new(stdout))
    }

    fn start_with_solver(source: &str, options: &[&str], solver_wrapper: &str) -> Self {
        let Spawned { mut child, dir, .. } = spawn(source, options, false, solver_wrapper, &[]);
        let input = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();
        Self::assemble(child, dir, input, Box::new(stdout))
    }
}

impl Worker<UnixStream> {
    fn start_socket(source: &str, options: &[&str]) -> Self {
        let Spawned { mut child, dir, listener } =
            spawn(source, options, true, DEFAULT_SOLVER_WRAPPER, &[]);
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

const DEFAULT_SOLVER_WRAPPER: &str = "#!/bin/sh\nset -eu\nprintf '%s\\n' \"$$\" >> \"$RESIDENT_LAUNCH_LOG\"\nexec \"$RESIDENT_SOLVER\" \"$@\"\n";

fn spawn(
    source: &str,
    options: &[&str],
    socket: bool,
    solver_wrapper: &str,
    envs: &[(&str, &str)],
) -> Spawned {
    let dir = tempfile::tempdir().unwrap();
    let socket_path = dir.path().join("worker.sock");
    let listener = socket.then(|| UnixListener::bind(&socket_path).unwrap());
    fs::write(dir.path().join("fixture.rs"), source).unwrap();
    let current = std::env::current_exe().unwrap();
    let binary = current.parent().unwrap().parent().unwrap().join("rust_verify");
    let solver = PathBuf::from(std::env::var_os("VERUS_CVC5_PATH").expect("cvc5 path"));
    let solver = fs::canonicalize(solver).unwrap();
    let wrapper = dir.path().join("solver.sh");
    fs::write(&wrapper, solver_wrapper).unwrap();
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
        .envs(envs.iter().copied())
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

/// With instantiation replay, every resident check that proves its query
/// saves its instantiations, and a recheck of a query with saved ones first
/// tries them alone (`:only`), falling back to the ordinary check unless that
/// proves the query. A failed check saves nothing, so the failing query's
/// rechecks search as usual. The reply says which checks tried a certificate
/// and whether it closed the query.
#[test]
fn resident_instantiation_replay_keeps_verdicts() {
    let mut worker = Worker::start_with_env(SOURCE, &[], &[("VERUS_RESIDENT_INST_REPLAY", "1")]);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready");
    assert_eq!(ready["instantiation_replay"], true);
    let session = ready["session"].clone();
    // (query, verdict, certificate closed it), the last `None` when no
    // certificate was tried.
    let checks = [
        ("::failing", "invalid", None),
        ("::passing", "valid", None),
        ("::failing", "invalid", None),
        ("::passing", "valid", Some(true)),
        ("::passing", "valid", Some(true)),
    ];
    for (name, expected, closed) in checks {
        let query = query_id(&ready, name);
        let result = worker
            .send(json!({"command": "check", "session": session, "bucket": 0, "query": query}));
        assert_eq!(result["event"], "checked", "{result}");
        assert_eq!(result["result"], expected, "{result}");
        match closed {
            None => assert!(result["certificate"].is_null(), "{}", result),
            Some(closed) => {
                assert_eq!(result["certificate"]["source"], "session", "{result}");
                assert_eq!(result["certificate"]["closed"], closed, "{result}");
            }
        }
    }
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
    let logs = smt_logs(worker.dir.path());
    let saves: usize = logs.iter().map(|log| log.matches("(save-instantiations c").count()).sum();
    let restores: usize = logs.iter().map(|log| log.matches(":only)").count()).sum();
    // One save per valid check; a certificate attempt for the two rechecks of
    // the passing query.
    assert_eq!((saves, restores), (3, 2));
    // Replay's solvers run with full proofs, so they get twice the budget a
    // plain session's solvers do.
    let mut plain = Worker::start(SOURCE, &[]);
    let ready = plain.receive();
    assert_eq!(ready["instantiation_replay"], false);
    let session = ready["session"].clone();
    let query = query_id(&ready, "::passing");
    let result =
        plain.send(json!({"command": "check", "session": session, "bucket": 0, "query": query}));
    assert_eq!(result["result"], "valid", "{result}");
    assert_eq!(plain.send(json!({"command": "close", "session": session}))["event"], "closed");
    plain.finish(false);
    let plain_budgets = resource_budgets(&smt_logs(plain.dir.path()));
    assert!(!plain_budgets.is_empty());
    let doubled: BTreeSet<u64> = plain_budgets.iter().map(|budget| budget * 2).collect();
    assert_eq!(resource_budgets(&logs), doubled);
}

/// Two quantifiers that feed each other: each instance of one introduces the
/// trigger of the other, so e-matching never stops (a matching loop).
const LOOP_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    uninterp spec fn enc(x: int) -> int;
    uninterp spec fn dec(x: int) -> int;

    proof fn roundtrip(a: int)
        requires
            forall|x: int| #[trigger] enc(x) > dec(enc(x)),
            forall|y: int| #[trigger] dec(y) > enc(dec(y)),
    {
        assert(enc(a) == 0);
    }

    proof fn passing() { assert(1 + 1 == 2); }
}
"#;

/// With `VERUS_RESIDENT_INST_GRAPH`, each check keeps its query's cvc5
/// instantiation graph, and `inst_graph` requests answer from it with source
/// spans. The loop's two quantifiers form the only cycle.
///
/// Needs a cvc5 with `--inst-graph` (BasisResearch/cvc5 `inst-graph/query`);
/// run with `--ignored` and `VERUS_CVC5_PATH` pointing at it until the pinned
/// release has it.
#[test]
#[ignore]
fn resident_inst_graph_finds_the_matching_loop() {
    let mut worker = Worker::start_with_env(
        LOOP_SOURCE,
        &["--rlimit", "1", "-V", "no-solver-version-check"],
        &[("VERUS_RESIDENT_INST_GRAPH", "1")],
    );
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready", "{ready}");
    assert_eq!(ready["inst_graph"], true);
    let session = ready["session"].clone();
    let looping = query_id(&ready, "::roundtrip");
    let passing = query_id(&ready, "::passing");
    let graph = |worker: &mut Worker<ChildStdin>, query: &Value, op: Value| {
        let mut request =
            json!({"command": "inst_graph", "session": session, "bucket": 0, "query": query});
        request.as_object_mut().unwrap().extend(op.as_object().unwrap().clone());
        worker.send(request)
    };
    // No graph before the query is checked.
    let early = graph(&mut worker, &passing, json!({"op": "cycles"}));
    assert_eq!(early["event"], "error", "{early}");

    let checked =
        worker.send(json!({"command": "check", "session": session, "bucket": 0, "query": looping}));
    assert_eq!(checked["event"], "checked", "{checked}");
    assert_ne!(checked["result"], "valid", "{checked}");
    let summary = &checked["inst_graph"];
    assert!(summary["instantiations"].as_u64().unwrap() > 10, "{checked}");
    assert!(summary["edges"].as_u64().unwrap() > 5, "{checked}");
    assert!(summary["max_depth"].as_u64().unwrap() > 2, "{checked}");

    let cycles = graph(&mut worker, &looping, json!({"op": "cycles"}));
    assert_eq!(cycles["event"], "inst_graph", "{cycles}");
    let result = &cycles["result"];
    assert_eq!(result["op"], "cycles");
    let found = result["cycles"].as_array().unwrap();
    assert_eq!(found.len(), 1, "{result}");
    assert_eq!(found[0]["length"], 2, "{result}");
    assert!(found[0]["repetitions"].as_u64().unwrap() > 5, "{result}");
    for node in found[0]["nodes"].as_array().unwrap() {
        assert!(node["function"].as_str().unwrap().ends_with("::roundtrip"), "{node}");
        assert!(node["source_span"].as_str().unwrap().contains("fixture.rs"), "{node}");
    }
    // Each unrolling is one deeper than the last.
    let depths: Vec<u64> = found[0]["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|n| n["depth"].as_u64().unwrap())
        .collect();
    assert!(depths.windows(2).all(|pair| pair[1] == pair[0] + 1), "{depths:?}");

    // The loop's quantifiers are the costliest, and a filter on another
    // function leaves nothing to report.
    let cost = graph(&mut worker, &looping, json!({"op": "top_cost", "limit": 2}));
    let ranked = cost["result"]["quantifiers"].as_array().unwrap();
    let loop_qids: BTreeSet<&str> =
        found[0]["quantifiers"].as_array().unwrap().iter().map(|q| q.as_str().unwrap()).collect();
    let top: BTreeSet<&str> = ranked.iter().map(|q| q["qid"].as_str().unwrap()).collect();
    assert_eq!(top, loop_qids, "{cost}");
    let elsewhere = graph(
        &mut worker,
        &looping,
        json!({"op": "cycles", "filter": {"source_fn": "no_such_crate::"}}),
    );
    assert!(elsewhere["result"]["cycles"].as_array().unwrap().is_empty(), "{elsewhere}");

    // The deepest instantiation descends from a root through the loop.
    let deepest = found[0]["nodes"].as_array().unwrap().last().unwrap()["inst"].clone();
    let path =
        graph(&mut worker, &looping, json!({"op": "path", "to_inst": deepest, "limit": 1000}));
    let chain = path["result"]["nodes"].as_array().unwrap();
    assert_eq!(chain.last().unwrap()["inst"], deepest, "{path}");
    assert_eq!(chain[0]["depth"], 0, "{path}");
    let growth = graph(&mut worker, &looping, json!({"op": "growth"}));
    assert_eq!(growth["result"]["step"], "round", "{growth}");
    assert!(!growth["result"]["per_round"].as_array().unwrap().is_empty(), "{growth}");
    let pathless = graph(&mut worker, &looping, json!({"op": "path"}));
    assert_eq!(pathless["event"], "error", "{pathless}");

    // A healthy query records its own, smaller graph.
    let healthy =
        worker.send(json!({"command": "check", "session": session, "bucket": 0, "query": passing}));
    assert_eq!(healthy["result"], "valid", "{healthy}");
    assert!(healthy["inst_graph"].is_object(), "{healthy}");
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);

    // Without the variable, no graph is recorded or served.
    let mut plain = Worker::start(LOOP_SOURCE, &["--rlimit", "1", "-V", "no-solver-version-check"]);
    let ready = plain.receive();
    assert_eq!(ready["inst_graph"], false);
    let session = ready["session"].clone();
    let checked =
        plain.send(json!({"command": "check", "session": session, "bucket": 0, "query": passing}));
    assert!(checked["inst_graph"].is_null(), "{checked}");
    let refused = plain.send(
        json!({"command": "inst_graph", "session": session, "bucket": 0, "query": passing, "op": "cycles"}),
    );
    assert_eq!(refused["event"], "error", "{refused}");
    assert_eq!(plain.send(json!({"command": "close", "session": session}))["event"], "closed");
    plain.finish(false);
}

/// The contents of a worker's SMT logs.
fn smt_logs(worker_dir: &Path) -> Vec<String> {
    fs::read_dir(worker_dir.join("logs"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "smt2"))
        .map(|path| fs::read_to_string(path).unwrap())
        .collect()
}

/// The nonzero per-check resource budgets the logged solvers were given.
fn resource_budgets(logs: &[String]) -> BTreeSet<u64> {
    logs.iter()
        .flat_map(|log| log.lines())
        .filter_map(|line| {
            line.trim()
                .strip_prefix("(set-option :reproducible-resource-limit ")?
                .strip_suffix(')')?
                .parse()
                .ok()
        })
        .filter(|budget| *budget != 0)
        .collect()
}

/// Check each `(query, verdict, closed)` in a new session over `source`, where
/// `closed` is `None` when no certificate may be tried, and otherwise whether
/// an imported one closed the query. Returns how many certificates the
/// session's solvers were sent.
fn check_session(
    source: &str,
    envs: &[(&str, &str)],
    checks: &[(&str, &str, Option<bool>)],
) -> usize {
    let mut worker = Worker::start_with_env(source, &[], envs);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready");
    let session = ready["session"].clone();
    for (name, expected, closed) in checks {
        let query = query_id(&ready, name);
        let result = worker
            .send(json!({"command": "check", "session": session, "bucket": 0, "query": query}));
        assert_eq!(result["event"], "checked", "{result}");
        assert_eq!(result["result"], *expected, "{result}");
        match closed {
            None => assert!(result["certificate"].is_null(), "{}", result),
            Some(closed) => {
                assert_eq!(result["certificate"]["source"], "imported", "{result}");
                assert_eq!(result["certificate"]["closed"], *closed, "{result}");
            }
        }
    }
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
    smt_logs(worker.dir.path())
        .iter()
        .map(|log| log.matches("(import-instantiations c").count())
        .sum()
}

/// The files in a certificate directory.
fn certificate_files(dir: &Path) -> Vec<PathBuf> {
    fs::read_dir(dir).unwrap().map(|entry| entry.unwrap().path()).collect()
}

/// A certificate exported by one session is imported by the next, a fresh
/// compilation and solver, before its first check of the same query. Only
/// the passing query exports one. After an edit that breaks the passing
/// proof, the same query imports that certificate, which must not turn the
/// failure into a pass, and the failed check must not replace it.
#[test]
fn resident_instantiation_certificates_survive_a_new_session() {
    let certificates = tempfile::tempdir().unwrap();
    let dir = certificates.path().to_str().unwrap().to_owned();
    let envs = [("VERUS_RESIDENT_INST_REPLAY", "1"), ("VERUS_RESIDENT_INST_DIR", dir.as_str())];
    // The same function, kind and description as `passing`, so the same
    // certificate key, but its assertion is false.
    let broken = SOURCE.replace("assert(recursive(0) == 0)", "assert(recursive(0) == 1)");
    assert_ne!(broken, SOURCE);
    let first = [("::passing", "valid", None), ("::failing", "invalid", None)];
    assert_eq!(check_session(SOURCE, &envs, &first), 0);
    let exported = certificate_files(certificates.path());
    assert_eq!(exported.len(), 1, "{exported:?}");
    let name = exported[0].file_name().unwrap().to_str().unwrap();
    assert!(name.starts_with('c') && name.ends_with(".smt2"), "{name}");
    let certificate = fs::read_to_string(&exported[0]).unwrap();
    // A new session: the solver has saved nothing, so the passing query's
    // first check imports the file the previous session exported.
    let second = [("::passing", "valid", Some(true)), ("::failing", "invalid", None)];
    assert_eq!(check_session(SOURCE, &envs, &second), 1);
    // The broken edit imports it too, and still fails.
    assert_eq!(check_session(&broken, &envs, &[("::passing", "invalid", Some(false))]), 1);
    assert_eq!(fs::read_to_string(&exported[0]).unwrap(), certificate);
}

/// A file in the certificate directory reaches a solver only if it is exactly
/// a certificate for its query's key. Anything else is ignored: the check
/// searches as usual and the session survives. A planted `(assert false)`
/// must not prove the broken assertion, and a truncated file, a literal cvc5
/// cannot lex, or a FIFO must not stop the solver or stall the server. A
/// passing check then replaces the file with a certificate the next session
/// imports.
#[test]
fn resident_instantiation_certificates_ignore_foreign_files() {
    let certificates = tempfile::tempdir().unwrap();
    let dir = certificates.path().to_str().unwrap().to_owned();
    let envs = [("VERUS_RESIDENT_INST_REPLAY", "1"), ("VERUS_RESIDENT_INST_DIR", dir.as_str())];
    let broken = SOURCE.replace("assert(recursive(0) == 0)", "assert(recursive(0) == 1)");
    assert_eq!(check_session(SOURCE, &envs, &[("::passing", "valid", None)]), 0);
    let exported = certificate_files(certificates.path());
    assert_eq!(exported.len(), 1, "{exported:?}");
    let path = &exported[0];
    let key = path.file_stem().unwrap().to_str().unwrap().to_owned();
    let planted = [
        "(assert false)".to_owned(),
        format!("(import-instantiations {key} \"(a)\")\n(assert false)"),
        format!("(import-instantiations {key} \"(abc"),
        "xyz".to_owned(),
        format!("(import-instantiations {key} \"\u{e9}\")"),
        format!("(import-instantiations {key} \"(a \u{1})\")"),
    ];
    for text in &planted {
        fs::write(path, text).unwrap();
        assert_eq!(check_session(&broken, &envs, &[("::passing", "invalid", None)]), 0, "{text}");
        assert_eq!(&fs::read_to_string(path).unwrap(), text);
    }
    #[cfg(unix)]
    {
        fs::remove_file(path).unwrap();
        assert!(std::process::Command::new("mkfifo").arg(path).status().unwrap().success());
        assert_eq!(check_session(&broken, &envs, &[("::passing", "invalid", None)]), 0);
        fs::remove_file(path).unwrap();
    }
    assert_eq!(check_session(SOURCE, &envs, &[("::passing", "valid", None)]), 0);
    assert_eq!(check_session(SOURCE, &envs, &[("::passing", "valid", Some(true))]), 1);
    assert_eq!(certificate_files(certificates.path()), exported);
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
fn resident_provenance_describes_the_first_error_round() {
    let source =
        "use vstd::prelude::*; verus! { proof fn check(x: int) { assert(x > 0); assert(x > 1); } }";
    // Tag each real solver round in the provenance parser's lossless
    // `unparsed` field. Ordinary fixtures can yield identical source sets
    // across rounds, hiding replacement of the first round by the last.
    let wrapper = r#"#!/bin/sh
set -eu
"$RESIDENT_SOLVER" "$@" | awk '
/^(sat|unsat|unknown)$/ {
    ++round;
    print round > (ENVIRON["RESIDENT_LAUNCH_LOG"] ".rounds");
    close(ENVIRON["RESIDENT_LAUNCH_LOG"] ".rounds");
    print "resident-round-" round;
}
{ print; fflush(); }
'
"#;
    for errors in ["0", "2"] {
        let mut worker = Worker::start_with_solver(
            source,
            &["-V", "provenance", "--multiple-errors", errors],
            wrapper,
        );
        let ready = worker.receive();
        for _ in 0..2 {
            let previous: usize = fs::read_to_string(worker.dir.path().join("launches.rounds"))
                .unwrap()
                .trim()
                .parse()
                .unwrap();
            let checked = worker.send(
                json!({"command":"check", "session":ready["session"], "bucket":0, "query":0}),
            );
            assert_eq!(checked["result"], "invalid");
            assert_eq!(checked["provenance"]["round"], 0);
            assert_eq!(
                checked["provenance"]["unparsed"],
                json!([format!("resident-round-{}", previous + 1)]),
                "additional error searches must not replace round-zero provenance"
            );
        }
        assert_eq!(
            worker.send(json!({"command":"close", "session":ready["session"]}))["event"],
            "closed"
        );
        worker.finish(false);
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

#[test]
fn resident_custom_options_survive_bucket_switches_and_spinoffs() {
    let settings = [
        ("random-seed", "7"),
        ("random-seed", "17"),
        ("mbqi", "false"),
        ("tlimit-per", "10000"),
        // Verus's per-query budget overrides this, in batch and resident mode.
        ("rlimit-per", "1"),
    ];
    let arguments: Vec<_> =
        settings.iter().map(|(name, value)| format!("{name}={value}")).collect();
    for provenance in [false, true] {
        for spinoff in [false, true] {
            let mut options = vec!["--num-threads", "2"];
            for argument in &arguments {
                options.extend(["--smt-option", argument.as_str()]);
            }
            if provenance {
                options.extend(["-V", "provenance"]);
            }
            if spinoff {
                options.extend(["-V", "spinoff-all"]);
            }
            let mut worker = Worker::start(MULTI_BUCKET_SOURCE, &options);
            let ready = worker.receive();
            assert_eq!(ready["event"], "ready");
            assert_eq!(ready["smt_options"], json!(settings));
            assert_eq!(ready["invocation_succeeded"], false);
            assert_eq!(ready["buckets"].as_array().unwrap().len(), 2);
            let launches = fs::read_to_string(worker.dir.path().join("launches")).unwrap();
            for (bucket, expected) in [(1, "invalid"), (0, "valid"), (1, "invalid"), (0, "valid")] {
                let checked = worker.send(json!({"command":"check", "session":ready["session"], "bucket":bucket, "query":0}));
                assert_eq!(checked["result"], expected, "{checked}");
                assert_eq!(!checked["provenance"].is_null(), provenance);
            }
            assert_eq!(
                worker.send(json!({"command":"close", "session":ready["session"]}))["event"],
                "closed"
            );
            worker.finish(false);
            worker.assert_solvers_gone();
            assert_eq!(fs::read_to_string(worker.dir.path().join("launches")).unwrap(), launches);
            let mut solver_logs = 0;
            for entry in fs::read_dir(worker.dir.path().join("logs")).unwrap() {
                let path = entry.unwrap().path();
                if path.extension().is_some_and(|ext| ext == "smt2") {
                    solver_logs += 1;
                    let log = fs::read_to_string(&path).unwrap();
                    let mut previous = 0;
                    for (name, value) in settings {
                        let command = format!("(set-option :{name} {value})");
                        assert_eq!(
                            log.matches(&command).count(),
                            1,
                            "{}: {command}",
                            path.display()
                        );
                        let position = log.find(&command).unwrap();
                        assert!(position >= previous);
                        previous = position;
                    }
                    if let Some(check) = log.find("(check-sat)") {
                        assert!(previous < check);
                    }
                }
            }
            assert!(solver_logs >= 2);
        }
    }
}

#[test]
fn resident_rejects_options_that_break_scopes_or_smuggle_commands() {
    for setting in [
        "incremental=false",
        "global-declarations=true",
        "single_check_query=true",
        "random-seed=7) (assert false",
        "incremental false) (set-option :random-seed=7",
    ] {
        let mut worker = Worker::start(SOURCE, &["--smt-option", setting]);
        worker.finish(false);
        assert!(worker.stderr().contains("resident"), "{}", worker.stderr());
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

// Filtering excludes specialised queries and their separate solver contexts
// from the catalogue alongside ordinary queries.
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

// A recheck looks for as many errors as the original invocation did, and says
// so when it stopped looking before running out of them. The limit comes from
// the invocation, so a function with two failing assertions reports a different
// number under each setting of --multiple-errors.
#[test]
fn resident_recheck_reports_as_many_errors_as_the_batch_run() {
    let source = r#"
        use vstd::prelude::*;
        verus! {
            proof fn two_failures(x: int) {
                assert(x > 0);
                assert(x < 0);
            }
        }
    "#;
    // Options, errors expected, and whether the search was cut short.
    for (options, failures, truncated) in [
        (&[][..], 2, true),                          // the default of 2
        (&["--multiple-errors", "0"][..], 1, true),  // the first failure only
        (&["--multiple-errors", "3"][..], 2, false), // more headroom than errors
    ] {
        let mut worker = Worker::start(source, options);
        let ready = worker.receive();
        let query = query_id(&ready, "::two_failures");
        let checked = worker.send(
            json!({"command": "check", "session": ready["session"], "bucket": 0, "query": query}),
        );
        assert_eq!(checked["result"], "invalid", "{:?} {}", options, checked);
        let diagnostics = checked["diagnostics"].as_array().unwrap();
        let reported = diagnostics.iter().filter(|d| d["level"] == "error").count();
        assert_eq!(reported, failures, "{:?} {}", options, checked);
        let note = diagnostics.iter().any(|d| {
            d["level"] == "note"
                && d["message"].as_str().unwrap().contains("not all errors may have been reported")
        });
        assert_eq!(note, truncated, "{:?} {}", options, checked);
        worker.finish(false);
    }
}

// Preparation that fails after the driver returns still tells the caller, so
// an empty stdout is never mistaken for a crash.
#[test]
fn resident_reports_that_no_session_is_available() {
    let source = "use vstd::prelude::*; verus! { proof fn f() { missing(); } }";
    let mut worker = Worker::start_socket(source, &[]);
    let reply = worker.receive();
    assert_eq!(reply["event"], "error", "{}", reply);
    assert!(reply["message"].as_str().unwrap().contains("no session is available"), "{}", reply);
    worker.finish(false);
}

// An oversized frame closes the session, and says so first.
#[test]
fn resident_reports_an_oversized_request_before_closing() {
    let mut worker = Worker::start(SOURCE, &[]);
    assert_eq!(worker.receive()["event"], "ready");
    worker.raw(&format!("{}\n", "x".repeat(70000)));
    let reply = worker.receive();
    assert_eq!(reply["event"], "error", "{}", reply);
    assert!(reply["message"].as_str().unwrap().contains("64 KiB"), "{}", reply);
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
            "use vstd::prelude::*; verus! { mod a { proof fn ok() {} } mod b { use super::*; proof fn f(x: int) by(integer_ring) ensures x * x == x * x, {} } }",
            "singular",
        ),
    ] {
        for threads in ["1", "2"] {
            let mut worker = Worker::start(source, &["--num-threads", threads]);
            // No catalogue is published, and the caller is told that rather
            // than left to infer it from an empty stdout.
            let reply = worker.receive();
            assert_eq!(reply["event"], "error", "{}", reply);
            assert!(
                reply["message"].as_str().unwrap().contains("no session is available"),
                "{}",
                reply
            );
            worker.finish(false);
            assert!(worker.stderr().to_lowercase().contains(expected), "{}", worker.stderr());
            assert!(!worker.stderr().contains("panicked"), "{}", worker.stderr());
        }
    }
}

#[test]
fn resident_specialised_preparation_matches_ordinary_verification() {
    let source = include_str!("fixtures/resident_specialised.rs");
    for provenance in [false, true] {
        let mut options = vec!["--output-json"];
        if provenance {
            options.extend(["-V", "provenance"]);
        }
        let mut worker = Worker::start_socket(source, &options);
        let ready = worker.receive();
        assert_eq!(ready["event"], "ready");
        assert_eq!(
            worker.send(json!({"command":"close", "session":ready["session"]}))["event"],
            "closed"
        );
        worker.finish(false);
        let retained: Value =
            serde_json::from_str(&fs::read_to_string(worker.dir.path().join("stdout")).unwrap())
                .unwrap();
        let current = std::env::current_exe().unwrap();
        let ordinary =
            Command::new(current.parent().unwrap().parent().unwrap().join("rust_verify"))
                .args(["--mcp", "-V", "cvc5", "--crate-type=lib"])
                .arg(worker.dir.path().join("fixture.rs"))
                .args(&options)
                .output()
                .unwrap();
        assert!(!ordinary.status.success());
        let ordinary: Value = serde_json::from_slice(&ordinary.stdout).unwrap();
        assert_eq!(retained["verification-results"]["errors"], 2);
        assert_eq!(retained["verification-results"], ordinary["verification-results"]);
    }
}

#[test]
fn resident_specialised_queries_reuse_scoped_solvers() {
    let source = include_str!("fixtures/resident_specialised.rs");
    for (threads, provenance, spinoff) in [
        ("1", false, false),
        ("2", false, false),
        ("2", true, false),
        ("2", false, true),
        ("2", true, true),
    ] {
        let mut options = vec!["--num-threads", threads];
        if provenance {
            options.extend(["-V", "provenance"]);
        }
        if spinoff {
            options.extend(["-V", "spinoff-all"]);
        }
        let mut worker = Worker::start(source, &options);
        let ready = worker.receive();
        assert_eq!(ready["event"], "ready");
        assert_eq!(ready["invocation_succeeded"], false);
        let buckets = ready["buckets"].as_array().unwrap();
        assert_eq!(buckets.len(), 2);
        let launches = fs::read_to_string(worker.dir.path().join("launches")).unwrap();
        let mut queries = Vec::new();
        for bucket in buckets {
            for query in bucket["queries"].as_array().unwrap() {
                let function = query["function"].as_str().unwrap();
                let prover = query["prover"].as_str().unwrap();
                if prover == "default" {
                    continue;
                }
                let expected_prover =
                    if function.contains("::bits_") { "bit_vector" } else { "nonlinear" };
                assert_eq!(prover, expected_prover);
                queries.push((bucket["id"].clone(), query));
            }
        }
        assert!(queries.len() >= 9, "{}", ready);
        // Reverse the initial order, cross buckets, then repeat forwards.
        for (bucket, query) in queries.iter().rev().chain(queries.iter()) {
            let checked = worker.send(json!({"command":"check", "session":ready["session"], "bucket":bucket, "query":query["id"]}));
            let expected = if query["function"].as_str().unwrap().ends_with("_bad") {
                "invalid"
            } else {
                "valid"
            };
            assert_eq!(checked["result"], expected, "{checked}");
            assert_eq!(!checked["provenance"].is_null(), provenance);
            if provenance {
                assert_eq!(checked["provenance"]["span"], query["span"]);
                assert_eq!(checked["provenance"]["result"], expected);
            }
            if expected == "invalid" {
                if query["prover"] != "bit_vector" {
                    assert!(checked["assert_id"].is_array(), "{}", checked);
                }
                let diagnostics = checked["diagnostics"].as_array().unwrap();
                assert!(!diagnostics.is_empty(), "{}", checked);
                assert_eq!(diagnostics[0]["level"], "error");
                assert!(diagnostics[0].to_string().contains("fixture.rs"));
            }
        }
        if !provenance && spinoff {
            // EOF owns the same cleanup obligation as an explicit close.
            worker.finish(false);
        } else {
            assert_eq!(
                worker.send(json!({"command":"close", "session":ready["session"]}))["event"],
                "closed"
            );
            worker.finish(false);
        }
        worker.assert_solvers_gone();
        assert_eq!(fs::read_to_string(worker.dir.path().join("launches")).unwrap(), launches);
        let mut bitvector_logs = 0;
        let mut nonlinear_logs = 0;
        for entry in fs::read_dir(worker.dir.path().join("logs")).unwrap() {
            let path = entry.unwrap().path();
            if !path.extension().is_some_and(|ext| ext == "smt2") {
                continue;
            }
            let log = fs::read_to_string(path).unwrap();
            if log.contains("query spun off because: bitvector") {
                bitvector_logs += 1;
                assert!(
                    !log.contains("(declare-sort Poly"),
                    "bit-vector context must be prelude-free"
                );
                assert!(log.contains("(set-option :incremental true)"));
                assert!(!log.contains("(set-option :single_check_query true)"));
            } else if log.contains("query spun off because: nonlinear") {
                nonlinear_logs += 1;
            } else {
                continue;
            }
            assert!(log.matches("(check-sat)").count() >= 3);
            assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
        }
        assert!(bitvector_logs >= 5);
        assert!(nonlinear_logs >= 4);
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
