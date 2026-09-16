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

const BISECT_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    uninterp spec fn f(i: int) -> int;
    uninterp spec fn g(i: int) -> int;
    uninterp spec fn a(i: int) -> int;

    // a(0) in the goal seeds the trigger, and each instance adds a(i + 1)
    proof fn looping()
        requires
            forall|i: int| #[trigger] a(i) < a(i + 1),
        ensures
            a(0) > 100,
    {
    }

    proof fn needs_one(x: int, y: int)
        requires
            y > 100,
            x > 3,
    {
        assert(x > 2);
    }

    proof fn fails_one(x: int)
        requires
            x > 3,
    {
        assert(x > 2);
        assert(x > 5);
        assert(x > 1);
    }

    proof fn unprovable(x: int)
        requires
            x > 0,
            forall|i: int| #[trigger] f(i) < f(i + 1),
    {
        assert(g(x) == 0);
    }
}
"#;

const EGRAPH_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    spec fn f(x: int) -> int;
    spec fn g(x: int) -> int;

    proof fn egraph_target(a: int, b: int)
        requires f(a) == g(b), g(b) > 0,
    {
        assert(f(a) > 1);
    }

    proof fn egraph_passing(a: int, b: int)
        requires a == b,
    {
        assert(b == a);
    }

    fn egraph_versions(v: &mut Vec<u64>, x: u64)
        requires old(v).len() > 0, x < 100,
    {
        let y = x + 1;
        v.set(0, y);
        let mut z = y;
        z = z + 1;
        assert(v[0] == z);
    }
}
"#;

/// `fixture.rs:<line>:`, the start of a span on the first line holding `needle`.
fn span_of(needle: &str) -> String {
    let line = BISECT_SOURCE.lines().position(|l| l.contains(needle)).unwrap() + 1;
    format!("fixture.rs:{line}:")
}

/// Bisect finds the failing goal, the one `requires` a proof needs, and the
/// quantifier behind a matching loop, and leaves the retained solver as it
/// was: ordinary rechecks answer as before and every probe scope is popped.
#[test]
fn resident_bisect_localises_and_leaves_the_session_unchanged() {
    let mut worker = Worker::start(BISECT_SOURCE, &["--rlimit", "2"]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    let request = |name: &str, extra: Value| {
        let mut request = json!({
            "command": "bisect", "session": session, "bucket": 0, "query": query_id(&ready, name),
        });
        request.as_object_mut().unwrap().extend(extra.as_object().unwrap().clone());
        request
    };
    let only = |reply: &Value| -> Value {
        let set = reply["minimal_statement_ids"].as_array().unwrap();
        assert_eq!(set.len(), 1, "{reply}");
        set[0].clone()
    };

    // Assuming the one failing assertion makes the rest provable.
    let reply = worker.send(request("::fails_one", json!({"mode": "flip"})));
    assert_eq!(reply["event"], "bisected", "{reply}");
    assert_eq!(reply["status"], "found");
    assert_eq!(reply["target"], "valid");
    // cvc5 answers a failing goal `unknown (incomplete)` rather than `sat`
    // whenever quantified axioms are in scope; Verus reports both as invalid.
    assert_ne!(reply["verdict_before"]["result"], "valid", "{reply}");
    assert_eq!(reply["verdict_after_removal"]["result"], "valid");
    assert_eq!(reply["minimal"], true);
    let goal = only(&reply);
    assert_eq!(goal["kind"], "goal");
    assert!(goal["assert_id"].is_array(), "{}", goal);
    assert!(goal["span"].as_str().unwrap().contains(&span_of("assert(x > 5)")), "{}", goal);
    // Each probe names the units it switched off.
    for probe in reply["probes"].as_array().unwrap() {
        let units = probe["removed_units"].as_array().unwrap();
        assert_eq!(units.len() as u64, probe["removed"].as_u64().unwrap(), "{probe}");
    }
    let removed: Vec<Value> = reply["probes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|probe| probe["removed_units"].clone())
        .collect();
    assert!(removed.contains(&json!([goal["index"]])), "{}", reply);
    assert!(reply["checks_used"].as_u64().unwrap() <= reply["budget_checks"].as_u64().unwrap());

    // The proof of `needs_one` cannot lose `x > 3`, and needs nothing else.
    for mode in ["flip", "core"] {
        let reply = worker.send(request("::needs_one", json!({"mode": mode})));
        assert_eq!(reply["status"], "found", "{reply}");
        assert_eq!(reply["verdict_before"]["result"], "valid");
        assert_eq!(reply["minimal"], true);
        let requires = only(&reply);
        assert_eq!(requires["kind"], "hypothesis");
        assert_eq!(requires["description"], "requires");
        assert!(requires["span"].as_str().unwrap().contains(&span_of("x > 3,")), "{}", requires);
        let valid_after = reply["verdict_after_removal"]["result"] == "valid";
        assert_eq!(valid_after, mode == "core", "{reply}");
    }

    // Only the goal decides `unprovable`: its hypotheses, removed, change
    // nothing, so a search restricted to them finds no set.
    let reply = worker.send(request("::unprovable", json!({"mode": "flip", "target": "changed"})));
    assert_eq!(reply["status"], "found", "{reply}");
    assert_ne!(reply["verdict_before"]["result"], "valid");
    let goal = only(&reply);
    assert_eq!(goal["kind"], "goal");
    assert!(goal["span"].as_str().unwrap().contains(&span_of("assert(g(x) == 0)")), "{}", goal);
    let reply = worker.send(request(
        "::unprovable",
        json!({"mode": "flip", "target": "changed", "kinds": ["hypothesis"]}),
    ));
    assert_eq!(reply["status"], "unreachable", "{reply}");
    assert_eq!(reply["minimal_statement_ids"], json!([]));
    // No set, so no verdict for one; what removing everything answered is
    // reported apart.
    assert!(reply["verdict_after_removal"].is_null(), "{}", reply);
    assert_ne!(reply["verdict_all_removed"]["result"], "valid", "{reply}");
    assert!(reply["verdict_all_removed"]["result"].is_string(), "{}", reply);

    // A matching loop runs the solver out of budget; the one hypothesis whose
    // removal stops that is the self-triggering quantifier.
    let reply = worker.send(request(
        "::looping",
        json!({"mode": "flip", "target": "changed", "kinds": ["hypothesis"]}),
    ));
    assert_eq!(reply["status"], "found", "{reply}");
    assert_eq!(reply["verdict_before"]["reason"], "resourceout");
    assert_ne!(reply["verdict_after_removal"]["reason"], "resourceout");
    let quantifier = only(&reply);
    assert_eq!(quantifier["kind"], "hypothesis");
    assert_eq!(quantifier["description"], "requires");
    assert!(quantifier["span"].as_str().unwrap().contains(&span_of("a(i) < a(i + 1)")));

    // Bad requests are refused without ending the session.
    let refused = worker.send(request("::needs_one", json!({"mode": "core", "target": "valid"})));
    assert_eq!(refused["event"], "error", "{refused}");
    let refused = worker.send(request("::needs_one", json!({"mode": "flip", "budget_checks": 0})));
    assert_eq!(refused["event"], "error", "{refused}");

    // A short budget still returns a verified set, marked not minimal.
    let reply = worker.send(request("::fails_one", json!({"mode": "flip", "budget_checks": 2})));
    assert_eq!(reply["checks_used"], 2, "{reply}");
    assert_eq!(reply["minimal"], false);

    for (name, expected) in [("::fails_one", "invalid"), ("::needs_one", "valid")] {
        let query = query_id(&ready, name);
        let result = worker
            .send(json!({"command": "check", "session": session, "bucket": 0, "query": query}));
        assert_eq!(result["result"], expected, "{result}");
    }
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
    let mut probes = 0;
    for log in smt_logs(worker.dir.path()) {
        assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
        probes += log.matches("(check-sat-assuming").count();
    }
    assert!(probes >= 10, "{}", probes);
}

const ABLATE_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    pub uninterp spec fn h(x: int) -> int;
    pub uninterp spec fn g(x: int) -> int;

    pub broadcast proof fn h_pos(x: int)
        ensures #[trigger] h(x) > 0,
    { admit(); }

    pub broadcast proof fn h_neg(x: int)
        ensures #[trigger] h(x) < 0,
    { admit(); }

    // every instance makes two new terms that trigger it again
    pub broadcast proof fn g_splits(x: int)
        ensures #[trigger] g(x) == g(2 * x) + g(2 * x + 1),
    { admit(); }

    pub uninterp spec fn c(n: int, x: int) -> int;

    spec fn double(x: int) -> int { x + x }
    spec fn quad(x: int) -> int { double(double(x)) }

    proof fn quad_is_four(x: int)
        requires
            x > 0,
    {
        assert(quad(x) == x + x + x + x);
    }

    proof fn contradictory(x: int) {
        broadcast use h_pos, h_neg;
        assert(h(x) == 7);
    }

    // needs ten rounds of instantiation, and the loop lemma outruns them
    proof fn buried(x: int)
        requires
            forall|n: int, x: int| 0 <= n < 10 ==> #[trigger] c(n, x) > c(n + 1, x),
            forall|x: int| #[trigger] c(10, x) >= x,
            g(x) == 0,
    {
        broadcast use g_splits;
        assert(c(0, x) >= x + 10);
    }

    // two goals behind the same loop
    proof fn twice_buried(x: int)
        requires
            forall|n: int, x: int| 0 <= n < 10 ==> #[trigger] c(n, x) > c(n + 1, x),
            forall|x: int| #[trigger] c(10, x) >= x,
            g(x) == 0,
    {
        broadcast use g_splits;
        assert(c(0, x) >= x + 10);
        assert(c(1, x) >= x + 9);
    }
}
"#;

/// `fixture.rs:<line>:` for the ablation fixture.
fn ablate_span_of(needle: &str) -> String {
    let line = ABLATE_SOURCE.lines().position(|l| l.contains(needle)).unwrap() + 1;
    format!("fixture.rs:{line}:")
}

/// Ablation names the broadcast lemma behind a matching loop, the
/// definitions a proof needs, and a contradictory pair of lemmas, confirms
/// each witness with its axioms genuinely absent, and leaves the retained
/// solver as it was.
#[test]
fn resident_ablation_finds_witnesses_and_leaves_the_session_unchanged() {
    let mut worker = Worker::start(ABLATE_SOURCE, &["--rlimit", "2"]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    let check = |name: &str| -> Value {
        json!({"command": "check", "session": session, "bucket": 0, "query": query_id(&ready, name)})
    };
    let ablate_request = |name: &str, extra: Value| -> Value {
        let mut request = json!({
            "command": "ablate", "session": session, "bucket": 0, "query": query_id(&ready, name),
        });
        request.as_object_mut().unwrap().extend(extra.as_object().unwrap().clone());
        request
    };
    macro_rules! ablate {
        ($name:expr, $extra:expr) => {{
            let reply = worker.send(ablate_request($name, $extra));
            assert_eq!(reply["event"], "ablated", "{reply}");
            reply
        }};
    }
    let names = |reply: &Value| -> Vec<String> {
        reply["witness"]
            .as_array()
            .unwrap()
            .iter()
            .map(|unit| unit["name"].as_str().unwrap().to_owned())
            .collect()
    };
    let before: Vec<Value> = ["::quad_is_four", "::contradictory", "::buried"]
        .iter()
        .map(|name| worker.send(check(name))["result"].clone())
        .collect();
    assert_eq!(before[0], "valid");
    assert_eq!(before[1], "valid");
    assert_ne!(before[2], "valid", "the matching loop should hide the proof");

    // A healthy proof needs exactly the two definitions it unfolds.
    let reply = ablate!("::quad_is_four", json!({"mode": "auto"}));
    assert_eq!(reply["mode"], "load_bearing", "{reply}");
    assert_eq!(reply["result"], "load_bearing_set", "{reply}");
    assert_eq!(reply["minimal"], true, "{reply}");
    // The two definitions, and the query's fuel setting that switches them on.
    let groups: Vec<&Value> = reply["witness"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|unit| unit["kind"] == "axiom_group")
        .collect();
    let mut kept: Vec<&str> = groups.iter().map(|unit| unit["name"].as_str().unwrap()).collect();
    kept.sort();
    assert!(
        kept.len() == 2 && kept[0].ends_with("::double") && kept[1].ends_with("::quad"),
        "{}",
        reply
    );
    for unit in groups {
        assert!(unit["span"].as_str().unwrap().contains("fixture.rs:"), "{}", unit);
        assert_eq!(unit["axioms"], 1, "{unit}");
        assert_eq!(unit["roles"], json!(["definition"]), "{unit}");
    }
    for unit in reply["witness"].as_array().unwrap() {
        if unit["kind"] == "hypothesis" {
            assert_eq!(unit["name"], "fuel", "{unit}");
        }
    }
    assert_eq!(reply["vacuity"]["vacuous"], false, "{reply}");
    assert_eq!(reply["absence_check"]["result"], "valid", "{reply}");
    assert_eq!(reply["absence_check"]["agrees"], true, "{reply}");
    assert!(reply["switched_axioms"].as_u64().unwrap() < reply["prefix_axioms"].as_u64().unwrap());
    let fuel_index = reply["witness"]
        .as_array()
        .unwrap()
        .iter()
        .find(|unit| unit["kind"] == "hypothesis")
        .map(|unit| unit["index"].clone())
        .unwrap_or_else(|| panic!("the fuel setting is load-bearing: {}", reply));

    // Nothing to remove from a valid query.
    let reply = ablate!("::quad_is_four", json!({"mode": "minimal_removal"}));
    assert_eq!(reply["status"], "already_at_target", "{reply}");
    assert_eq!(reply["result"], "none");

    // With the hypotheses off limits, only axiom groups are candidates, and
    // the fuel setting stays: the two definitions alone are load-bearing.
    let reply = ablate!("::quad_is_four", json!({"mode": "load_bearing", "hypotheses": false}));
    assert_eq!(reply["result"], "load_bearing_set", "{reply}");
    assert_eq!(reply["candidates"], reply["axiom_groups"], "{reply}");
    let mut kept = names(&reply);
    kept.sort();
    assert_eq!(kept.len(), 2, "{reply}");
    assert!(kept[0].ends_with("::double") && kept[1].ends_with("::quad"), "{}", reply);
    for unit in reply["witness"].as_array().unwrap() {
        assert_eq!(unit["kind"], "axiom_group", "{unit}");
    }
    // A hypothesis is then no candidate, so excluding one is refused.
    let refused = worker.send(ablate_request(
        "::quad_is_four",
        json!({"mode": "load_bearing", "hypotheses": false, "exclude": [fuel_index]}),
    ));
    assert_eq!(refused["event"], "error", "{refused}");

    // Two contradictory lemmas prove anything: the proof is vacuous, and both
    // take part in the contradiction.
    let reply = ablate!("::contradictory", json!({"mode": "auto"}));
    assert_eq!(reply["result"], "load_bearing_set", "{reply}");
    let kept = names(&reply);
    for lemma in ["::h_pos", "::h_neg"] {
        assert!(kept.iter().any(|name| name.ends_with(lemma)), "{}: {}", lemma, reply);
    }
    for unit in reply["witness"].as_array().unwrap() {
        if unit["kind"] == "axiom_group" {
            // the lemma's group also defines its `ens%` predicate; the
            // role is the lemma's
            assert_eq!(unit["roles"], json!(["broadcast"]), "{unit}");
        }
    }
    assert_eq!(reply["vacuity"]["vacuous"], true, "{reply}");
    assert_eq!(reply["vacuity"]["before"]["result"], "valid", "{reply}");
    // The lemmas contradict before any path is taken: every goal is vacuous.
    assert_eq!(reply["vacuity"]["every_goal"]["result"], "valid", "{reply}");
    let participated = reply["vacuity"]["participated"].as_array().unwrap();
    for unit in reply["witness"].as_array().unwrap() {
        if unit["kind"] == "axiom_group" {
            assert!(participated.contains(&unit["index"]), "{}: {}", unit, reply);
        }
    }
    assert_eq!(reply["absence_check"]["agrees"], true, "{reply}");

    // The loop lemma hides a proof that needs a dozen rounds of unfolding:
    // removing it alone makes the query valid, and it is not a vacuity.
    // Removing every candidate loses the proof too, so the search tries one
    // unit at a time, most instantiated first: the loop lemma comes first.
    let reply = ablate!("::buried", json!({"mode": "auto"}));
    assert_eq!(reply["non_monotone"], true, "{reply}");
    assert!(reply["checks_used"].as_u64().unwrap() <= 5, "{}", reply);
    assert_eq!(reply["mode"], "minimal_removal", "{reply}");
    assert_eq!(reply["result"], "minimal_removal_that_proves", "{reply}");
    assert_ne!(reply["verdict_before"]["result"], "valid", "{reply}");
    assert_eq!(reply["verdict_with_witness"]["result"], "valid", "{reply}");
    let removed = reply["witness"].as_array().unwrap();
    assert_eq!(removed.len(), 1, "{reply}");
    assert_eq!(removed[0]["kind"], "axiom_group", "{reply}");
    assert!(removed[0]["name"].as_str().unwrap().ends_with("::g_splits"), "{}", reply);
    assert_eq!(removed[0]["roles"], json!(["broadcast"]), "{reply}");
    let span = removed[0]["span"].as_str().unwrap();
    assert!(span.contains(&ablate_span_of("fn g_splits")), "{}", reply);
    assert!(removed[0]["instantiations_before"].as_u64().unwrap() > 0, "{}", reply);
    assert_eq!(reply["vacuity"]["vacuous"], false, "{reply}");
    assert_eq!(reply["absence_check"]["result"], "valid", "{reply}");
    assert_eq!(reply["absence_check"]["agrees"], true, "{reply}");
    let used = reply["checks_used"].as_u64().unwrap();
    assert!(used <= reply["budget_checks"].as_u64().unwrap(), "{}", reply);
    // Every candidate is named, by the index the probes use.
    let named = reply["candidate_units"].as_array().unwrap();
    assert_eq!(named.len() as u64, reply["candidates"].as_u64().unwrap(), "{reply}");
    let loop_index = removed[0]["index"].clone();
    assert!(
        named.iter().any(|unit| unit["index"] == loop_index && unit["name"] == removed[0]["name"])
    );
    let candidates = reply["candidates"].as_u64().unwrap();

    // Excluded, the loop lemma is no candidate: it is neither tried nor
    // named, whatever else the search finds within its budget.
    let reply = ablate!(
        "::buried",
        json!({"mode": "minimal_removal", "budget_checks": 4, "exclude": [loop_index]})
    );
    assert_eq!(reply["excluded"], json!([loop_index]), "{reply}");
    assert_eq!(reply["candidates"].as_u64().unwrap(), candidates - 1, "{reply}");
    let named = reply["candidate_units"].as_array().unwrap();
    assert!(named.iter().all(|unit| unit["index"] != loop_index), "{}", reply);
    let witness = reply["witness"].as_array().unwrap();
    assert!(witness.iter().all(|unit| unit["index"] != loop_index), "{}", reply);
    for probe in reply["probes"].as_array().unwrap() {
        assert!(!probe["removed_units"].as_array().unwrap().contains(&loop_index), "{}", reply);
    }
    // A unit the query does not have is refused without ending the session.
    let refused =
        worker.send(ablate_request("::buried", json!({"mode": "auto", "exclude": [999]})));
    assert_eq!(refused["event"], "error", "{refused}");

    // A budget of one probe goes to the probe with nothing removed. The
    // vacuity probes, one per goal, are extra; there is no witness to check
    // for absence.
    let reply = ablate!("::buried", json!({"mode": "minimal_removal", "budget_checks": 1}));
    assert_eq!(reply["status"], "budget_exhausted", "{reply}");
    assert_eq!(reply["result"], "none", "{reply}");
    assert_eq!(reply["checks_used"], 1, "{reply}");
    assert_eq!(reply["extra_checks"], reply["vacuity"]["goals"], "{reply}");
    assert!(reply["absence_check"].is_null(), "{}", reply);
    assert!(reply["witness"].as_array().unwrap().is_empty(), "{}", reply);

    // Two goals behind the loop: the vacuity probe of the last runs out of
    // resources, and the scan stops there rather than spend the budget on
    // the first as well.
    let reply = ablate!("::twice_buried", json!({"mode": "minimal_removal", "budget_checks": 1}));
    let vacuity = &reply["vacuity"];
    let goals = vacuity["goals"].as_u64().unwrap();
    assert!(goals >= 2, "{}", reply);
    assert_eq!(vacuity["before"]["result"], "unknown", "{reply}");
    assert!(
        matches!(vacuity["before"]["reason"].as_str(), Some("resourceout" | "timeout")),
        "{}",
        reply
    );
    assert_eq!(vacuity["goals_unchecked"], goals - 1, "{reply}");
    assert_eq!(reply["extra_checks"], 1, "{reply}");

    // Bad requests are refused without ending the session.
    let refused = worker.send(json!({"command": "ablate", "session": session, "bucket": 0,
        "query": query_id(&ready, "::buried"), "mode": "auto", "budget_checks": 0}));
    assert_eq!(refused["event"], "error", "{refused}");

    // Ordinary rechecks answer as before.
    for (name, expected) in
        ["::quad_is_four", "::contradictory", "::buried"].iter().zip(before.iter())
    {
        assert_eq!(&worker.send(check(name))["result"], expected, "{name}");
    }
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
    for log in smt_logs(worker.dir.path()) {
        assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
    }
}

/// Ablation probes take a budget of their own: an `rlimit` for the probes
/// alone, which the absence check and every later request do not see, and a
/// wall-clock cap per probe past which the solver cancels the probe, which
/// is then listed as skipped and marks the reply partial.
#[test]
fn resident_ablation_probes_take_their_own_budget() {
    let mut worker = Worker::start(ABLATE_SOURCE, &["--rlimit", "2"]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    let request = |name: &str, extra: Value| -> Value {
        let mut request = json!({
            "command": "ablate", "session": session, "bucket": 0, "query": query_id(&ready, name),
        });
        request.as_object_mut().unwrap().extend(extra.as_object().unwrap().clone());
        request
    };
    // Both fields are taken; a generous cap skips nothing.
    let reply = worker.send(request(
        "::quad_is_four",
        json!({"mode": "load_bearing", "rlimit": 4.0, "probe_timeout_ms": 600_000}),
    ));
    assert_eq!(reply["event"], "ablated", "{reply}");
    assert_eq!(reply["result"], "load_bearing_set", "{reply}");
    assert_eq!(reply["partial"], false, "{reply}");
    assert!(reply.get("skipped_probes").is_none(), "{reply}");
    // A bad budget is refused without ending the session.
    for extra in [
        json!({"rlimit": 0}),
        json!({"rlimit": 5000}),
        json!({"rlimit": 1e-9}),
        json!({"probe_timeout_ms": 0}),
    ] {
        let refused = worker.send(request("::quad_is_four", extra.clone()));
        assert_eq!(refused["event"], "error", "{extra}: {refused}");
    }
    // A cap of one millisecond: whatever the solver manages in that time,
    // every probe it cancelled is listed, and the reply says it is partial
    // exactly when some probe was.
    let reply = worker.send(request(
        "::buried",
        json!({"mode": "minimal_removal", "budget_checks": 2, "probe_timeout_ms": 1}),
    ));
    assert_eq!(reply["event"], "ablated", "{reply}");
    let skipped = reply["skipped_probes"].as_array().map_or(0, Vec::len);
    assert_eq!(reply["partial"], skipped > 0, "{reply}");
    if skipped > 0 {
        assert!(reply.to_string().contains("timeout"), "{reply}");
    }
    // The session answers as before: the probes' rlimit did not stick.
    let check = worker.send(json!({"command": "check", "session": session, "bucket": 0,
        "query": query_id(&ready, "::quad_is_four")}));
    assert_eq!(check["result"], "valid", "{check}");
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
    // The solvers saw exactly two budgets: the session's, and twice it for
    // the probes that asked for rlimit 4.
    let budgets = resource_budgets(&smt_logs(worker.dir.path()));
    assert_eq!(budgets.len(), 2, "{budgets:?}");
    let (low, high) = (*budgets.iter().next().unwrap(), *budgets.iter().last().unwrap());
    assert_eq!(high, low * 2, "{budgets:?}");
    for log in smt_logs(worker.dir.path()) {
        assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
        // The cap is lifted after every probe it bounded.
        assert_eq!(
            log.matches("(set-option :tlimit-per 1)").count()
                + log.matches("(set-option :tlimit-per 600000)").count(),
            log.matches("(set-option :tlimit-per 0)").count()
        );
    }
}

const TWIN_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    uninterp spec fn a(i: int) -> int;
    pub uninterp spec fn f(i: int) -> int;

    pub broadcast proof fn f_nonneg(i: int)
        ensures #[trigger] f(i) >= 0,
    { admit(); }

    spec fn sum(n: nat) -> nat
        decreases n,
    {
        if n == 0 { 0 } else { n + sum((n - 1) as nat) }
    }

    // a(0) in the goal seeds the trigger, and each instance adds a(i + 1)
    proof fn looping()
        requires
            forall|i: int| #[trigger] a(i) < a(i + 1),
        ensures
            a(0) > 100,
    {
    }

    proof fn uses_lemma(x: int)
        ensures f(x) >= 0,
    {
        broadcast use f_nonneg;
    }

    pub broadcast group g_nonneg {
        f_nonneg,
    }

    // reveals f_nonneg only through its group
    proof fn uses_group(x: int)
        ensures f(x) >= 0,
    {
        broadcast use g_nonneg;
    }

    proof fn unprovable(x: int)
        requires x > 0,
    {
        assert(x > 7);
    }

    proof fn needs_fuel()
        ensures sum(3) == 6,
    {
    }

    proof fn ordered(x: int)
        requires x > 3,
    {
        assert(x > 5);
        assert(x > 9);
    }

    // sum(0) unfolds once, which the default fuel allows, unless sum is hidden
    proof fn hides_sum()
        ensures sum(0) == 0,
    {
        hide(sum);
    }

    proof fn wants_more(x: int)
        ensures f(x) >= 1,
    {
        broadcast use f_nonneg;
    }

    // Declared after every function above, so its axiom is retained for
    // a later query than theirs. It contradicts f_nonneg wherever f(i) is
    // mentioned, and nothing here uses it.
    pub broadcast proof fn f_neg(i: int)
        ensures #[trigger] f(i) < 0,
    { admit(); }
}
"#;

/// A twin changes one thing about a query, checks both in their own scopes,
/// and reports how the solver's behaviour changed; the session is the same
/// afterwards.
#[test]
fn resident_twin_compares_a_query_with_its_edit() {
    let mut worker = Worker::start(TWIN_SOURCE, &["--rlimit", "2"]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    let twin = |worker: &mut Worker<ChildStdin>, name: &str, edit: Value, extra: Value| {
        let mut request = json!({
            "command": "twin", "session": session, "bucket": 0, "query": query_id(&ready, name),
            "edit": edit,
        });
        request.as_object_mut().unwrap().extend(extra.as_object().unwrap().clone());
        worker.send(request)
    };
    let intact = |reply: &Value| {
        let integrity = &reply["integrity"];
        assert_eq!(integrity["intact"], true, "{reply}");
        assert!(integrity["stack_levels_before"].is_u64(), "{}", reply);
    };

    // More budget for a matching loop: still out of budget, with more of the
    // same instantiations.
    let reply = twin(&mut worker, "::looping", json!({"bump_rlimit": 8}), json!({}));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["edit"]["kind"], "bump_rlimit");
    assert_eq!(reply["base"]["class"], "resource_limit", "{reply}");
    assert_eq!(reply["twin"]["class"], "resource_limit", "{reply}");
    assert_eq!(reply["outcome_flip"]["flipped"], false);
    let delta = &reply["inst_count_delta"];
    assert!(delta["total"].as_i64().unwrap() > 0, "{}", reply);
    // the prelude's boxing axioms ride the loop; the loop's own quantifier
    // is the one written in `looping`
    let looping = delta["by_quantifier"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| q["fun"].as_str().is_some_and(|f| f.ends_with("::looping")))
        .unwrap_or_else(|| panic!("{}", reply));
    assert!(looping["qid"].as_str().unwrap().starts_with("user_"), "{}", reply);
    assert!(looping["span"].as_str().unwrap().contains("fixture.rs"), "{}", reply);
    let qid = looping["qid"].as_str().unwrap().to_owned();
    // outside a difficulty session, the difficulty comparison is unavailable
    assert!(reply["difficulty_delta"].is_null());
    assert!(reply["unavailable"].to_string().contains("difficulty"), "{}", reply);
    intact(&reply);

    // Removing the looping quantifier, named by its qid: the budget is no
    // longer spent, its instantiations are gone, and the verdict changes.
    let reply =
        twin(&mut worker, "::looping", json!({"remove_axiom": qid}), json!({"recheck_base": true}));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["edit"]["axioms"][0]["place"], "query", "{reply}");
    assert_eq!(reply["edit"]["axioms"][0]["tag"]["kind"], "requires", "{reply}");
    assert_eq!(reply["outcome_flip"]["base"], "resource_limit", "{reply}");
    assert_eq!(reply["outcome_flip"]["flipped"], true, "{reply}");
    let delta = &reply["inst_count_delta"];
    assert_eq!(delta["by_quantifier"][0]["qid"], qid.as_str(), "{reply}");
    assert!(delta["by_quantifier"][0]["delta"].as_i64().unwrap() < 0, "{}", reply);
    assert_eq!(delta["by_quantifier"][0]["twin"], 0, "{reply}");
    assert!(delta["stopped"].as_array().unwrap().contains(&json!(qid)), "{}", reply);
    let recheck = &reply["integrity"]["recheck"];
    assert_eq!(recheck["same_result"], true, "{reply}");
    assert!(recheck["instantiations"].is_u64(), "{}", reply);
    intact(&reply);

    // A module-level broadcast axiom, named by its function: the prefix is
    // rebuilt without it, and the lemma's postcondition no longer follows.
    let reply = twin(&mut worker, "::uses_lemma", json!({"remove_axiom": "f_nonneg"}), json!({}));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["edit"]["axioms"][0]["place"], "prefix", "{reply}");
    assert!(reply["edit"]["rebuilt_scopes"].as_u64().unwrap() >= 1, "{}", reply);
    assert_eq!(reply["outcome_flip"]["base"], "valid", "{reply}");
    assert_ne!(reply["outcome_flip"]["twin"], "valid", "{reply}");
    intact(&reply);

    // An added contradiction proves anything, and is flagged as vacuous.
    let reply = twin(&mut worker, "::unprovable", json!({"add_axiom": "(= 1 2)"}), json!({}));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["outcome_flip"]["twin"], "valid", "{reply}");
    let vacuity = &reply["vacuity"];
    // cvc5 answers a satisfiable context with quantifiers `unknown`
    assert_ne!(vacuity["base_goals_off"], "valid", "{reply}");
    assert_eq!(vacuity["twin_goals_off"], "valid", "{reply}");
    assert_eq!(vacuity["inconsistent"], true, "{reply}");
    assert_eq!(vacuity["possibly_vacuous"], true, "{reply}");
    intact(&reply);
    // A harmless one changes nothing and is not flagged.
    let reply = twin(&mut worker, "::unprovable", json!({"add_axiom": "(= 1 1)"}), json!({}));
    assert_eq!(reply["outcome_flip"]["flipped"], false, "{reply}");
    assert_eq!(reply["vacuity"]["possibly_vacuous"], false, "{reply}");

    // A broadcast lemma named instead of an expression applies as
    // `broadcast use` would: its fuel is assumed, and its axiom added when
    // the bucket declared it only for a later query. f_neg contradicts
    // f_nonneg at the goal, where f(x) is mentioned, but not in the
    // hypotheses; the goals-off check catches that.
    let before = |a: &str, b: &str| {
        query_id(&ready, a).as_u64().unwrap() < query_id(&ready, b).as_u64().unwrap()
    };
    assert!(before("::wants_more", "::f_neg"), "{}", ready);
    let reply = twin(&mut worker, "::wants_more", json!({"add_axiom": "f_neg"}), json!({}));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["edit"]["axioms"][0]["place"], "retained", "{reply}");
    assert!(reply["edit"]["fuel_assumed"].as_str().unwrap().ends_with("::f_neg"), "{}", reply);
    assert_ne!(reply["outcome_flip"]["base"], "valid", "{reply}");
    assert_eq!(reply["outcome_flip"]["twin"], "valid", "{reply}");
    assert_eq!(reply["vacuity"]["inconsistent"], true, "{reply}");
    assert_eq!(reply["vacuity"]["possibly_vacuous"], true, "{reply}");
    intact(&reply);
    // One whose axiom the context already holds needs only its fuel.
    let place = if before("::f_nonneg", "::unprovable") { "prefix" } else { "retained" };
    let reply = twin(&mut worker, "::unprovable", json!({"add_axiom": "f_nonneg"}), json!({}));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["edit"]["axioms"][0]["place"], place, "{reply}");
    assert!(reply["edit"]["fuel_assumed"].as_str().unwrap().ends_with("::f_nonneg"), "{}", reply);
    assert_eq!(reply["vacuity"]["inconsistent"], false, "{reply}");

    // Fuel: sum(3) needs more unrolling than the default, and hiding the
    // function takes away even what the default gives.
    let reply = twin(
        &mut worker,
        "::needs_fuel",
        json!({"flip_fuel": {"fn": "sum", "fuel": 4}}),
        json!({}),
    );
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["edit"]["fuel"]["recursive"], true, "{reply}");
    assert_ne!(reply["outcome_flip"]["base"], "valid", "{reply}");
    assert_eq!(reply["outcome_flip"]["twin"], "valid", "{reply}");
    let reply = twin(
        &mut worker,
        "::needs_fuel",
        json!({"flip_fuel": {"fn": "sum", "fuel": 0}}),
        json!({}),
    );
    assert_ne!(reply["outcome_flip"]["twin"], "valid", "{reply}");
    // A function the query hides is revealed again by fuel 1.
    let reply =
        twin(&mut worker, "::hides_sum", json!({"flip_fuel": {"fn": "sum", "fuel": 1}}), json!({}));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["edit"]["fuel"]["hidden_before"], true, "{reply}");
    assert_ne!(reply["outcome_flip"]["base"], "valid", "{reply}");
    assert_eq!(reply["outcome_flip"]["twin"], "valid", "{reply}");

    // Reordering two assertions changes which one fails first.
    let checked = worker.send(
        json!({"command": "check", "session": session, "bucket": 0, "query": query_id(&ready, "::ordered")}),
    );
    let first = checked["assert_id"].as_array().unwrap().clone();
    let mut second = first.clone();
    *second.last_mut().unwrap() = json!(first.last().unwrap().as_u64().unwrap() + 1);
    let reply =
        twin(&mut worker, "::ordered", json!({"reorder_asserts": [second, first]}), json!({}));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["base"]["assert_id"], json!(first), "{reply}");
    assert_eq!(reply["twin"]["assert_id"], json!(second), "{reply}");

    // Refusals leave the session serving.
    for (name, edit, extra, says) in [
        ("::unprovable", json!({"remove_axiom": "no_such_axiom"}), json!({}), "nothing"),
        ("::unprovable", json!({"bump_rlimit": 1000}), json!({}), "at most"),
        (
            "::unprovable",
            json!({"flip_fuel": {"fn": "no_such_fn", "fuel": 1}}),
            json!({}),
            "no function",
        ),
        // already visible: fuel 1 would change nothing
        (
            "::needs_fuel",
            json!({"flip_fuel": {"fn": "sum", "fuel": 1}}),
            json!({}),
            "already visible",
        ),
        // its axiom is in the context and the body reveals it
        ("::uses_lemma", json!({"add_axiom": "f_nonneg"}), json!({}), "already applies"),
        // the body reveals it through a group
        ("::uses_group", json!({"add_axiom": "f_nonneg"}), json!({}), "broadcast group"),
        (
            "::uses_group",
            json!({"flip_fuel": {"fn": "f_nonneg", "fuel": 1}}),
            json!({}),
            "already visible",
        ),
        // the prelude is asserted before the bucket's context
        (
            "::unprovable",
            json!({"remove_axiom": "prelude_fuel_defaults"}),
            json!({}),
            "prelude axiom",
        ),
        ("::unprovable", json!({"add_axiom": "(= no_such_symbol 1)"}), json!({}), "type-check"),
        ("::unprovable", json!({"bump_rlimit": 4}), json!({"limit": 0}), "limit"),
    ] {
        let reply = twin(&mut worker, name, edit, extra);
        assert_eq!(reply["event"], "error", "{reply}");
        assert!(reply["message"].as_str().unwrap().contains(says), "{}", reply);
    }
    // Two edits at once is not a request.
    let reply = twin(
        &mut worker,
        "::unprovable",
        json!({"bump_rlimit": 4, "remove_axiom": "x"}),
        json!({}),
    );
    assert_eq!(reply["message"], "invalid resident request", "{reply}");

    for (name, expected) in [
        ("::uses_lemma", "valid"),
        ("::uses_group", "valid"),
        ("::unprovable", "invalid"),
        ("::needs_fuel", "invalid"),
        ("::wants_more", "invalid"),
        ("::hides_sum", "invalid"),
    ] {
        let query = query_id(&ready, name);
        let result = worker
            .send(json!({"command": "check", "session": session, "bucket": 0, "query": query}));
        assert_eq!(result["result"], expected, "{result}");
    }
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
    for log in smt_logs(worker.dir.path()) {
        assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
    }
}

/// Ablation in a provenance session, where every asserted axiom carries a
/// `:named` tag and the solver dumps instantiations after each check, and in
/// a spinoff-all session, where the query has a solver of its own: the same
/// witness, and rechecks answer as before.
#[test]
fn resident_ablation_works_under_provenance_and_spinoff() {
    for mode in ["provenance", "spinoff-all"] {
        let mut worker = Worker::start(ABLATE_SOURCE, &["--rlimit", "2", "-V", mode]);
        let ready = worker.receive();
        let session = ready["session"].clone();
        let check = |name: &str| -> Value {
            json!({"command": "check", "session": session, "bucket": 0, "query": query_id(&ready, name)})
        };
        let before = worker.send(check("::buried"))["result"].clone();
        assert_ne!(before, "valid", "{}: the matching loop should hide the proof", mode);
        let reply = worker.send(json!({
            "command": "ablate", "session": session, "bucket": 0,
            "query": query_id(&ready, "::buried"), "mode": "auto",
        }));
        assert_eq!(reply["event"], "ablated", "{mode}: {reply}");
        assert_eq!(reply["result"], "minimal_removal_that_proves", "{mode}: {reply}");
        let removed = reply["witness"].as_array().unwrap();
        assert_eq!(removed.len(), 1, "{mode}: {reply}");
        assert!(
            removed[0]["name"].as_str().unwrap().ends_with("::g_splits"),
            "{}: {}",
            mode,
            reply
        );
        assert_eq!(reply["absence_check"]["agrees"], true, "{mode}: {reply}");
        assert_eq!(worker.send(check("::buried"))["result"], before, "{mode}");
        assert_eq!(worker.send(check("::quad_is_four"))["result"], "valid", "{mode}");
        assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
        worker.finish(false);
        for log in smt_logs(worker.dir.path()) {
            let head: Vec<&str> = log.lines().take(12).collect();
            assert_eq!(
                log.matches("(push").count(),
                log.matches("(pop").count(),
                "{mode}: {head:?}"
            );
        }
    }
}

const VACUITY_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    proof fn bad(x: int)
        requires
            x > 0,
        ensures
            false,
    { admit(); }

    // the contradiction arrives after the first goal, bad's precondition
    proof fn late(x: int)
        requires
            x > 0,
    {
        bad(x);
        assert(x == x + 1);
    }

    proof fn consistent(x: int)
        requires
            x > 0,
    {
        assert(x > 0);
        assert(x >= 1);
    }

    // the requires contradict each other before any path is taken
    proof fn impossible(x: int)
        requires
            x > 0,
            x < 0,
    {
        assert(x == 7);
        assert(x == 8);
    }
}
"#;

/// Each function with an edit, next to the function with the same edit made
/// in source.
const DIFFERENTIAL_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    uninterp spec fn a(i: int) -> int;

    spec fn sum(n: nat) -> nat
        decreases n,
    {
        if n == 0 { 0 } else { n + sum((n - 1) as nat) }
    }

    proof fn with_loop(x: int)
        requires
            x > 3,
            forall|i: int| #[trigger] a(i) < a(i + 1),
        ensures
            x > 2 && a(0) > 100,
    {
    }

    proof fn without_loop(x: int)
        requires
            x > 3,
        ensures
            x > 2 && a(0) > 100,
    {
    }

    proof fn default_fuel()
        ensures sum(3) == 6,
    {
    }

    proof fn revealed_fuel()
        ensures sum(3) == 6,
    {
        reveal_with_fuel(sum, 4);
    }
}
"#;

/// A contradiction a lemma's ensures brings in after the first goal makes a
/// later goal vacuous: ablation names that goal, and the lemma's contract as
/// what the contradiction needs.
#[test]
fn resident_ablation_finds_a_contradiction_after_the_first_goal() {
    let mut worker = Worker::start(VACUITY_SOURCE, &[]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    let request = |name: &str, extra: Value| -> Value {
        let mut request = json!({
            "command": "ablate", "session": session, "bucket": 0, "query": query_id(&ready, name),
            "mode": "auto",
        });
        request.as_object_mut().unwrap().extend(extra.as_object().unwrap().clone());
        request
    };

    let reply = worker.send(request("::late", json!({})));
    assert_eq!(reply["event"], "ablated", "{reply}");
    assert_eq!(reply["result"], "load_bearing_set", "{reply}");
    let vacuity = &reply["vacuity"];
    assert_eq!(vacuity["vacuous"], true, "{reply}");
    assert_eq!(vacuity["before"]["result"], "valid", "{reply}");
    assert!(vacuity["goals"].as_u64().unwrap() >= 2, "{}", reply);
    let line = VACUITY_SOURCE.lines().position(|l| l.contains("assert(x == x + 1)")).unwrap() + 1;
    let span = vacuity["goal"]["span"].as_str().unwrap();
    assert!(span.contains(&format!("fixture.rs:{line}:")), "{}", reply);
    // Not every goal is vacuous: the path brings the contradiction in.
    assert!(vacuity["every_goal"].is_object(), "{}", reply);
    assert_ne!(vacuity["every_goal"]["result"], "valid", "{reply}");
    // The lemma's ensures is the contradiction, and its group says it is a
    // contract, not a definition.
    let bad = reply["witness"]
        .as_array()
        .unwrap()
        .iter()
        .find(|unit| unit["name"].as_str().unwrap().ends_with("::bad"))
        .unwrap_or_else(|| panic!("bad is load-bearing: {}", reply));
    assert_eq!(bad["roles"], json!(["contract"]), "{reply}");
    let participated = vacuity["participated"].as_array().unwrap();
    assert!(participated.contains(&bad["index"]), "{}", reply);
    assert_eq!(reply["absence_check"]["agrees"], true, "{reply}");

    // A goal is no candidate, so excluding one is refused.
    let goal = vacuity["goal"]["index"].clone();
    let refused = worker.send(request("::late", json!({"exclude": [goal]})));
    assert_eq!(refused["event"], "error", "{refused}");

    // Consistent assumptions: every goal probed, none vacuous.
    let reply = worker.send(request("::consistent", json!({})));
    assert_eq!(reply["event"], "ablated", "{reply}");
    let vacuity = &reply["vacuity"];
    assert_eq!(vacuity["vacuous"], false, "{reply}");
    assert!(vacuity["goals"].as_u64().unwrap() >= 2, "{}", reply);
    assert!(vacuity["goal"].is_null(), "{}", reply);
    assert!(vacuity["goals_unchecked"].is_null(), "{}", reply);
    assert!(vacuity["every_goal"].is_null(), "{}", reply);

    // Contradictory requires: every goal is vacuous, not only the last.
    let reply = worker.send(request("::impossible", json!({})));
    assert_eq!(reply["event"], "ablated", "{reply}");
    assert_eq!(reply["vacuity"]["vacuous"], true, "{reply}");
    assert!(reply["vacuity"]["goals"].as_u64().unwrap() >= 2, "{}", reply);
    assert_eq!(reply["vacuity"]["every_goal"]["result"], "valid", "{reply}");

    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(true);
    for log in smt_logs(worker.dir.path()) {
        assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
    }
}

/// The differential harness: a twin of `f` with an edit answers as the
/// ordinary check of `g`, the same function with the edit made in source,
/// and instantiates about as much. A twin of `g` that changes nothing
/// (the same rlimit) measures how much two checks of one query differ.
#[test]
fn resident_twin_matches_the_edit_made_in_source() {
    let mut worker = Worker::start(DIFFERENTIAL_SOURCE, &["--rlimit", "2"]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    let mut twin = |name: &str, edit: Value| {
        let reply = worker.send(json!({
            "command": "twin", "session": session, "bucket": 0, "query": query_id(&ready, name),
            "edit": edit,
        }));
        assert_eq!(reply["event"], "twin", "{reply}");
        assert_eq!(reply["integrity"]["intact"], true, "{reply}");
        reply
    };
    let instantiations = |branch: &Value| branch["instantiations"].as_u64().unwrap();

    // the loop quantifier, as a twin with more budget names it
    let probe = twin("::with_loop", json!({"bump_rlimit": 4}));
    let qid = probe["inst_count_delta"]["by_quantifier"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| q["fun"].as_str().is_some_and(|f| f.ends_with("::with_loop")))
        .and_then(|q| q["qid"].as_str())
        .unwrap_or_else(|| panic!("{}", probe))
        .to_owned();
    let removed = twin("::with_loop", json!({"remove_axiom": qid}));
    let cold = twin("::without_loop", json!({"bump_rlimit": 2}));
    assert_eq!(removed["twin"]["class"], cold["base"]["class"], "{removed}\n{cold}");
    let (t, c) = (instantiations(&removed["twin"]), instantiations(&cold["base"]));
    let noise = instantiations(&cold["base"]).abs_diff(instantiations(&cold["twin"]));
    eprintln!("remove: twin {t} instantiations, source edit {c}, repeat noise {noise}");
    assert!(t.abs_diff(c) <= 3 * noise + c / 4, "{}\n{}", removed, cold);

    let fueled = twin("::default_fuel", json!({"flip_fuel": {"fn": "sum", "fuel": 4}}));
    let cold = twin("::revealed_fuel", json!({"bump_rlimit": 2}));
    assert_eq!(fueled["twin"]["class"], "valid", "{fueled}");
    assert_eq!(cold["base"]["class"], "valid", "{cold}");
    let (t, c) = (instantiations(&fueled["twin"]), instantiations(&cold["base"]));
    let noise = instantiations(&cold["base"]).abs_diff(instantiations(&cold["twin"]));
    eprintln!("fuel: twin {t} instantiations, source edit {c}, repeat noise {noise}");
    assert!(t.abs_diff(c) <= 3 * noise + c / 4, "{}\n{}", fueled, cold);

    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
}

/// A spinoff solver journals the bucket context before it in one scope, as
/// the main context does, so a module-level axiom is rebuilt away there too
/// rather than hidden through the query's fuel.
#[test]
fn resident_twin_rebuilds_a_lemma_away_under_spinoff_all() {
    let mut worker = Worker::start(TWIN_SOURCE, &["--rlimit", "2", "-V", "spinoff-all"]);
    let ready = worker.receive();
    assert_eq!(ready["spinoff_all"], true, "{ready}");
    let session = ready["session"].clone();
    let reply = worker.send(json!({
        "command": "twin", "session": session, "bucket": 0,
        "query": query_id(&ready, "::uses_lemma"), "edit": {"remove_axiom": "f_nonneg"},
    }));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["edit"]["axioms"][0]["place"], "prefix", "{reply}");
    assert!(reply["edit"]["rebuilt_scopes"].as_u64().unwrap() >= 1, "{}", reply);
    assert!(reply["edit"]["fuel"].is_null(), "{}", reply);
    assert_eq!(reply["outcome_flip"]["base"], "valid", "{reply}");
    assert_ne!(reply["outcome_flip"]["twin"], "valid", "{reply}");
    assert_eq!(reply["integrity"]["intact"], true, "{reply}");
    let checked = worker.send(json!({
        "command": "check", "session": session, "bucket": 0,
        "query": query_id(&ready, "::uses_lemma"),
    }));
    assert_eq!(checked["result"], "valid", "{checked}");
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
}

/// In a difficulty session a twin also compares each input assertion's
/// difficulty and relevance.
#[test]
fn resident_twin_compares_difficulty_in_a_difficulty_session() {
    let mut worker = Worker::start(TWIN_SOURCE, &["--rlimit", "2", "-V", "difficulty"]);
    let ready = worker.receive();
    assert_eq!(ready["difficulty"], true, "{ready}");
    let reply = worker.send(json!({
        "command": "twin", "session": ready["session"], "bucket": 0,
        "query": query_id(&ready, "::uses_lemma"), "edit": {"remove_axiom": "f_nonneg"},
    }));
    assert_eq!(reply["event"], "twin", "{reply}");
    let difficulty = &reply["difficulty_delta"];
    assert!(difficulty["total"]["base"].is_u64(), "{}", reply);
    let relevance = &reply["did_relevant_delta"];
    assert!(relevance["basis"].is_string(), "{}", reply);
    assert!(!reply["unavailable"].to_string().contains("difficulty"), "{}", reply);
    assert_eq!(reply["integrity"]["intact"], true, "{reply}");
    assert_eq!(
        worker.send(json!({"command": "close", "session": ready["session"]}))["event"],
        "closed"
    );
    worker.finish(false);
}

/// The variables `text` names with an assignment version, as `(name, version)`.
fn versions_named(text: &str) -> Vec<(String, String)> {
    const MARK: &str = " (version ";
    let mut found = Vec::new();
    let mut rest = text;
    while let Some(at) = rest.find(MARK) {
        let name = rest[..at].rsplit(|c: char| !(c.is_alphanumeric() || c == '_')).next();
        let tail = &rest[at + MARK.len()..];
        let version: String = tail.chars().take_while(|c| c.is_ascii_digit()).collect();
        found.push((name.unwrap_or_default().to_string(), version));
        rest = tail;
    }
    found
}

/// An `egraph` request lists the equalities a failing query's e-graph holds
/// between the query's own terms, in source spelling. `f(a) == g(b)` survives
/// preprocessing, which solves an equality with a variable side, such as
/// `a == b`, by substitution instead. An injection checks the
/// query again with one of them asserted, in a scope popped right after, so a
/// later check of the retained query is unchanged. The equality to inject is
/// named by the id the reading gave it; an unknown id is refused, and the
/// session keeps serving.
#[test]
fn resident_egraph_lists_and_injects_equalities() {
    let mut worker = Worker::start(EGRAPH_SOURCE, &[]);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready", "{ready}");
    let session = ready["session"].clone();
    let target = query_id(&ready, "::egraph_target");
    let listed =
        worker.send(json!({"command": "egraph", "session": session, "bucket": 0, "query": target}));
    assert_eq!(listed["event"], "egraph", "{listed}");
    assert_eq!(listed["before"]["result"], "invalid", "{listed}");
    assert!(listed["summary"]["focus_found"].as_u64().unwrap() > 0, "{}", listed);
    let pair = listed["equalities"]
        .as_array()
        .unwrap()
        .iter()
        .find(|equality| {
            let sides = [equality["lhs"].as_str().unwrap(), equality["rhs"].as_str().unwrap()];
            sides.iter().any(|side| side.ends_with("f(a)"))
                && sides.iter().any(|side| side.ends_with("g(b)"))
        })
        .unwrap_or_else(|| panic!("no f(a) == g(b): {}", listed))
        .clone();
    assert_eq!(pair["level"], "entailed", "{pair}");
    assert_eq!(pair["used_by_proof"], false, "{pair}");
    assert!(!pair["holds_because"].as_array().unwrap().is_empty(), "{}", pair);
    // Only an entailed equality is offered as an assert: `a == b` holds in
    // the model the search ended on, and is listed without one.
    let equalities = listed["equalities"].as_array().unwrap();
    assert!(equalities.iter().any(|e| e["level"] == "decision"), "{}", listed);
    for equality in equalities {
        assert!(
            equality["level"] == "entailed" || equality["verus_assert"].is_null(),
            "{}",
            equality
        );
    }
    // The offered assert is source for the crate it came from, and it holds
    // there: pasted in place of the failing assert, the function verifies.
    let pasted = pair["verus_assert"].as_str().unwrap();
    assert!(pasted.contains("crate::f(a)") && pasted.contains("crate::g(b)"), "{}", pair);
    let mut paste_worker = Worker::start(&EGRAPH_SOURCE.replace("assert(f(a) > 1);", pasted), &[]);
    let paste_ready = paste_worker.receive();
    assert_eq!(paste_ready["event"], "ready", "{paste_ready}");
    let pasted_check = paste_worker.send(json!({"command": "check",
        "session": paste_ready["session"], "bucket": 0,
        "query": query_id(&paste_ready, "::egraph_target")}));
    assert_eq!(pasted_check["result"], "valid", "{pasted_check}");
    paste_worker.send(json!({"command": "close", "session": paste_ready["session"]}));
    paste_worker.finish(false);
    // Differently boxed terms of the same equality read alike; it is listed once.
    let mut rendered: Vec<(String, String)> = listed["equalities"]
        .as_array()
        .unwrap()
        .iter()
        .map(|equality| {
            let lhs = equality["lhs"].as_str().unwrap().to_string();
            let rhs = equality["rhs"].as_str().unwrap().to_string();
            if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) }
        })
        .collect();
    let listed_count = rendered.len();
    rendered.sort();
    rendered.dedup();
    assert_eq!(rendered.len(), listed_count, "{listed}");

    // A requires the query already entails changes nothing when injected.
    let injected = worker.send(json!({"command": "egraph", "session": session, "bucket": 0,
        "query": target, "inject": pair["id"]}));
    assert_eq!(injected["injection"]["equality"]["id"], pair["id"], "{injected}");
    assert_eq!(injected["injection"]["after"]["result"], "invalid", "{injected}");
    assert_eq!(injected["injection"]["closed"], false, "{injected}");
    assert!(injected["injection"]["frontier_delta"].is_object(), "{}", injected);

    let refused = worker.send(json!({"command": "egraph", "session": session, "bucket": 0,
        "query": target, "inject": "eq#000000000000"}));
    assert_eq!(refused["event"], "error", "{refused}");
    let checked =
        worker.send(json!({"command": "check", "session": session, "bucket": 0, "query": target}));
    assert_eq!(checked["result"], "invalid", "{checked}");

    // A valid query leaves no e-graph to read.
    let passing = query_id(&ready, "::egraph_passing");
    let valid = worker
        .send(json!({"command": "egraph", "session": session, "bucket": 0, "query": passing}));
    assert_eq!(valid["before"]["result"], "valid", "{valid}");
    assert!(valid["before"]["egraph_error"].is_string(), "{}", valid);
    assert!(valid["equalities"].as_array().unwrap().is_empty(), "{}", valid);

    // `z == (z + 1)` would name two assignments of `z` alike. The reading
    // holds such an equality between versions of `z`, and offers no assert
    // for it or any other that names one variable at two versions.
    let versions = query_id(&ready, "::egraph_versions");
    let versioned = worker
        .send(json!({"command": "egraph", "session": session, "bucket": 0, "query": versions}));
    assert_eq!(versioned["event"], "egraph", "{versioned}");
    let mut mixed = 0;
    for equality in versioned["equalities"].as_array().unwrap() {
        let text = format!("{} {}", equality["lhs"], equality["rhs"]);
        let named = versions_named(&text);
        let two = named.iter().any(|(x, v)| named.iter().any(|(y, w)| x == y && v != w));
        if two {
            mixed += 1;
            assert!(equality["verus_assert"].is_null(), "{}", equality);
        }
    }
    assert!(mixed > 0, "{}", versioned);

    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
    let launches = fs::read_to_string(worker.dir.path().join("launches")).unwrap();
    assert_eq!(launches.lines().count(), 1, "{launches}");
    for log in smt_logs(worker.dir.path()) {
        assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
    }
}

const SPECULATE_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    spec fn f(x: int) -> int;
    spec fn g(x: int) -> int;
    spec fn h(x: int) -> int;
    spec fn s(x: int) -> int;

    proof fn speculate_target(a: int)
        requires forall|i: int| #![trigger g(i)] g(i) > 0 && f(i) > 0,
    {
        assert(f(a) > 0);
    }

    proof fn speculate_loop(a: int)
        requires forall|x: int| #![trigger h(x)] h(x) > h(s(x)), h(a) > 100,
    {
        assert(h(a) < 0);
    }

    proof fn speculate_introduces(a: int)
        requires forall|x: int| #![trigger g(x)] h(x) > h(s(x)), h(a) > 0,
    {
        assert(h(a) < 0);
    }
}
"#;

/// A small budget, so the looping queries give up quickly. Set
/// `RESIDENT_NO_SOLVER_VERSION_CHECK` to run against a cvc5 build whose
/// version differs from the pinned release.
fn speculate_options() -> Vec<&'static str> {
    let mut options = vec!["--rlimit", "2"];
    if std::env::var_os("RESIDENT_NO_SOLVER_VERSION_CHECK").is_some() {
        options.extend(["-V", "no-solver-version-check"]);
    }
    options
}

fn probe<E: Endpoint>(
    worker: &mut Worker<E>,
    session: &Value,
    query: &Value,
    hypothesis: Option<Value>,
) -> Value {
    let mut request =
        json!({"command": "speculate", "session": session, "bucket": 0, "query": query});
    if let Some(hypothesis) = hypothesis {
        request["hypothesis"] = hypothesis;
    }
    worker.send(request)
}

/// The quantifier written in `function`'s own query, from a probe without a
/// hypothesis, which lists them.
fn own_quantifier<E: Endpoint>(worker: &mut Worker<E>, session: &Value, query: &Value) -> Value {
    let listed = probe(worker, session, query, None);
    assert_eq!(listed["event"], "speculated", "{listed}");
    assert_eq!(listed["hypothesis"], "none", "{listed}");
    listed["candidates"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| q["in_query"] == true)
        .unwrap_or_else(|| panic!("no quantifier of the query: {}", listed))
        .clone()
}

/// A `speculate` request checks a query as usual, then again with one
/// hypothesis in the query's own scope. A directed instance that closes the
/// goal comes back with an assert that, pasted into the source, verifies; a
/// speculative trigger with an annotation that, pasted, verifies too. A block
/// of a matching loop's later rungs ends the loop, and a trigger that makes a
/// quantifier feed itself is reported as introducing one. A hypothesis that
/// names no quantifier, a variable the quantifier lacks, or a term the solver
/// cannot read, is refused in the reply. Afterwards the query rechecks as it
/// did before, and no probe launched a solver: the probes are the pasted
/// source's differential check and the session's state check.
#[test]
fn resident_speculate_probes_and_leaves_the_session_unchanged() {
    let options = speculate_options();
    let mut worker = Worker::start(SPECULATE_SOURCE, &options);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready", "{ready}");
    let session = ready["session"].clone();
    let target = query_id(&ready, "::speculate_target");
    let first =
        worker.send(json!({"command": "check", "session": session, "bucket": 0, "query": target}));
    assert_eq!(first["result"], "invalid", "{first}");

    // Listed without a hypothesis: the requires, with its variable.
    let quantifier = own_quantifier(&mut worker, &session, &target);
    assert_eq!(quantifier["binders"][0]["name"], "i", "{quantifier}");
    assert!(quantifier["triggers"][0][0].as_str().unwrap().ends_with("g(i)"), "{}", quantifier);
    let qid = quantifier["qid"].clone();

    // A directed instance at i := a closes the goal, and the query still
    // fails right after without it.
    let instantiation = json!({"instantiation": {"qid": qid, "subst": {"i": "a"}}});
    let probed = probe(&mut worker, &session, &target, Some(instantiation));
    assert_eq!(probed["status"], "applied", "{probed}");
    assert_eq!(probed["before"]["result"], "invalid", "{probed}");
    assert_eq!(probed["after"]["result"], "valid", "{probed}");
    assert_eq!(probed["recheck"]["result"], "invalid", "{probed}");
    assert_eq!(probed["closed"], true, "{probed}");
    assert_eq!(probed["introduced_loop"], false, "{probed}");
    let instance = &probed["new_provenance"]["closing_instantiations"][0];
    assert_eq!(instance["inference_id"], "LLM_DIRECTED", "{probed}");
    assert_eq!(instance["terms"], json!(["a"]), "{probed}");
    // The assert it offers verifies the function once pasted before the goal.
    let pasted = probed["verus_snippet"].as_str().unwrap();
    assert!(pasted.starts_with("assert(") && pasted.contains("crate::f(a)"), "{}", probed);
    let source = SPECULATE_SOURCE
        .replace("assert(f(a) > 0);", &format!("{pasted}\n        assert(f(a) > 0);"));
    let mut paste_worker = Worker::start(&source, &options);
    let paste_ready = paste_worker.receive();
    let pasted_check = paste_worker.send(json!({"command": "check",
        "session": paste_ready["session"], "bucket": 0,
        "query": query_id(&paste_ready, "::speculate_target")}));
    assert_eq!(pasted_check["result"], "valid", "{pasted_check}");
    paste_worker.send(json!({"command": "close", "session": paste_ready["session"]}));
    paste_worker.finish(false);

    // A speculative trigger f(i) matches the goal's f(a); its annotation,
    // added to the quantifier, verifies the function.
    let trigger = json!({"trigger_pattern": {"qid": qid, "pattern": "f(i)"}});
    let triggered = probe(&mut worker, &session, &target, Some(trigger));
    assert_eq!(triggered["status"], "applied", "{triggered}");
    assert_eq!(triggered["closed"], true, "{triggered}");
    let annotation = triggered["verus_snippet"].as_str().unwrap();
    assert!(annotation.starts_with("#![trigger ") && annotation.contains("f(i)"), "{}", triggered);
    assert!(
        triggered["fallback_snippet"].as_str().unwrap().starts_with("assert("),
        "{}",
        triggered
    );
    let source = SPECULATE_SOURCE
        .replace("#![trigger g(i)] g(i) > 0", &format!("#![trigger g(i)] {annotation} g(i) > 0"));
    let mut paste_worker = Worker::start(&source, &options);
    let paste_ready = paste_worker.receive();
    let pasted_check = paste_worker.send(json!({"command": "check",
        "session": paste_ready["session"], "bucket": 0,
        "query": query_id(&paste_ready, "::speculate_target")}));
    assert_eq!(pasted_check["result"], "valid", "{pasted_check}");
    paste_worker.send(json!({"command": "close", "session": paste_ready["session"]}));
    paste_worker.finish(false);

    // Refusals leave the query unchecked and the session serving.
    let missing = probe(
        &mut worker,
        &session,
        &target,
        Some(json!({"instantiation": {"qid": "user_nothing_0", "subst": {"i": "a"}}})),
    );
    assert_eq!(missing["status"], "no_quantifier", "{missing}");
    assert!(missing["before"].is_null(), "{}", missing);
    assert!(!missing["candidates"].as_array().unwrap().is_empty(), "{}", missing);
    let unbound = probe(
        &mut worker,
        &session,
        &target,
        Some(json!({"instantiation": {"qid": qid, "subst": {"j": "a"}}})),
    );
    assert_eq!(unbound["status"], "mismatch", "{unbound}");
    let unreadable = probe(
        &mut worker,
        &session,
        &target,
        Some(json!({"instantiation": {"qid": qid, "subst": {"i": "nothing_declared(a)"}}})),
    );
    assert_eq!(unreadable["status"], "could_not_lower", "{unreadable}");
    assert!(unreadable["reason"].as_str().unwrap().contains("nothing_declared"), "{}", unreadable);
    let refused = worker.send(json!({"command": "speculate", "session": session, "bucket": 0,
        "query": target, "loop_threshold": 0}));
    assert_eq!(refused["event"], "error", "{refused}");

    // The loop h(x) > h(s(x)) climbs until the budget runs out; blocked from
    // its third rung on, it stops.
    let looping = query_id(&ready, "::speculate_loop");
    let loop_quantifier = own_quantifier(&mut worker, &session, &looping);
    let loop_qid = loop_quantifier["qid"].clone();
    let blocked = probe(
        &mut worker,
        &session,
        &looping,
        Some(json!({"block_cycle": {"qid": loop_qid, "fingerprint": "h(s(s(_)))"}})),
    );
    assert_eq!(blocked["status"], "applied", "{blocked}");
    let has_loop =
        |run: &Value| run["loops"].as_array().unwrap().iter().any(|l| l["qid"] == loop_qid);
    assert!(has_loop(&blocked["before"]), "{}", blocked);
    assert!(!has_loop(&blocked["after"]), "{}", blocked);
    assert!(blocked["blocked"].as_u64().unwrap() > 0, "{}", blocked);
    assert_eq!(blocked["introduced_loop"], false, "{blocked}");

    // The same shape of quantifier, triggered on g, never fires; given the
    // trigger h(x), it climbs.
    let introducing = query_id(&ready, "::speculate_introduces");
    let intro_quantifier = own_quantifier(&mut worker, &session, &introducing);
    let intro_qid = intro_quantifier["qid"].clone();
    let climbing = probe(
        &mut worker,
        &session,
        &introducing,
        Some(json!({"trigger_pattern": {"qid": intro_qid, "pattern": "h(x)"}})),
    );
    assert_eq!(climbing["status"], "applied", "{climbing}");
    assert_eq!(climbing["introduced_loop"], true, "{climbing}");
    assert!(
        climbing["new_loops"].as_array().unwrap().iter().any(|l| l["qid"] == intro_qid),
        "{}",
        climbing
    );
    assert_eq!(climbing["closed"], false, "{climbing}");

    // Nothing of the probes is left behind.
    let last =
        worker.send(json!({"command": "check", "session": session, "bucket": 0, "query": target}));
    assert_eq!(last["result"], first["result"], "{last}");
    assert_eq!(last["diagnostics"], first["diagnostics"], "{last}");
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
    let launches = fs::read_to_string(worker.dir.path().join("launches")).unwrap();
    assert_eq!(launches.lines().count(), 1, "{launches}");
    for log in smt_logs(worker.dir.path()) {
        assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
    }
}

const SCAFFOLD_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    uninterp spec fn f(i: int) -> int;
    uninterp spec fn g(i: int) -> int;

    // No term of the goal matches `g(f(i))`, so the solver never uses the
    // inverse; `g(f(x)) == x` gives it one, and congruence the other.
    proof fn scaffold_target(x: int)
        requires
            forall|i: int| #[trigger] g(f(i)) == i,
    {
        assert(f(x) != f(x + 1));
    }

    proof fn scaffold_passing(x: int)
        requires
            x > 0,
    {
        assert(x >= 0);
    }

    // The same goal inside a proof block: `P` is checked after the block's
    // steps, and belongs at its end.
    proof fn scaffold_by(x: int)
        requires
            forall|i: int| #[trigger] g(f(i)) == i,
    {
        assert(f(x) != f(x + 1)) by {
            assert(x == x);
        }
    }

    // A goal among the steps of `assert ... by` is checked where it is:
    // `P` goes right before it.
    proof fn scaffold_step(x: int)
        requires
            forall|i: int| #[trigger] g(f(i)) == i,
    {
        assert(x == x) by {
            assert(f(x) != f(1 + x));
        }
    }

    // A closure body is a dead end too, but no `by` follows its last goal.
    fn scaffold_closure(x: u64)
        requires
            forall|i: int| #[trigger] g(f(i)) == i,
    {
        let c = |y: u64| {
            assert(f(y as int) != f(y as int + 1));
        };
    }

    // Two goals fail; Verus reports the earlier first.
    proof fn scaffold_two_failing(x: int) {
        assert(x != 7);
        assert(x > 100);
    }

    // A postcondition is checked at each exit: the early `return`, and the
    // end of the body, whose final expression is `x`.
    proof fn scaffold_exit(x: int, b: bool) -> (r: int)
        requires
            forall|i: int| #[trigger] g(f(i)) == i,
        ensures
            f(r) != f(r + 1),
    {
        if b {
            return x;
        }
        x
    }
}
"#;

/// A loop whose second invariant holds on entry (the second `requires`)
/// and, at the end of the body, needs the inverse at the new `i`. The
/// inverse is an invariant too: an isolated loop body sees no `requires`.
/// Verus emits the check at the end of the body without an assert id.
const INVARIANT_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    uninterp spec fn f(i: int) -> int;
    uninterp spec fn g(i: int) -> int;

    fn scaffold_loop(n: u64)
        requires
            forall|i: int| #[trigger] g(f(i)) == i,
            f(0) != f(1),
    {
        let mut i: u64 = 0;
        while i < n
            invariant
                forall|j: int| #[trigger] g(f(j)) == j,
                f(i as int) != f(i as int + 1),
            decreases n - i,
        {
            i = i + 1;
        }
    }
}
"#;

/// One proposal per case: `P`, the case, whether `P` is provable where the
/// goal is, and whether the goal closes with `P` assumed there.
const SCAFFOLD_CASES: &[(&str, &str, bool, bool)] = &[
    ("g(f(x)) == x", "scaffold", true, true),
    ("x + 1 > x", "true_but_unhelpful", true, false),
    ("f(x) < f(x + 1)", "helpful_but_unprovable", false, true),
    ("f(x) == 0", "dead_end", false, false),
];

/// `fixture.rs:<line>:` for the first line of `source` holding `needle`.
fn line_of(source: &str, needle: &str) -> String {
    let line = source.lines().position(|l| l.contains(needle)).unwrap() + 1;
    format!("fixture.rs:{line}:")
}

fn checks_valid(worker: &mut Worker<ChildStdin>, ready: &Value, name: &str) -> bool {
    let result = worker.send(json!({"command": "check", "session": ready["session"],
        "bucket": 0, "query": query_id(ready, name)}));
    assert_eq!(result["event"], "checked", "{result}");
    result["result"] == "valid"
}

/// A scaffold request answers each of the four cases, and each answer is the
/// one the ordinary pipeline gives the edited source (the differential): `P`
/// asserted where the goal is, and `P` assumed before the goal, each as a
/// function of its own checked by a solver of its own. The printed snippet,
/// pasted, makes the function verify. Refused proposals and every check leave
/// the session as it was.
#[test]
fn resident_scaffold_tells_the_four_cases_apart_as_cold_checks_do() {
    let mut worker = Worker::start(SCAFFOLD_SOURCE, &[]);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready", "{ready}");
    let session = ready["session"].clone();
    let target = query_id(&ready, "::scaffold_target");
    let request = |extra: Value| {
        let mut request =
            json!({"command": "scaffold", "session": session, "bucket": 0, "query": target});
        request.as_object_mut().unwrap().extend(extra.as_object().unwrap().clone());
        request
    };

    // Without assert_id, the goal the query fails at, found by one more check.
    let first = worker.send(request(json!({"assert": SCAFFOLD_CASES[0].0})));
    assert_eq!(first["event"], "scaffold", "{first}");
    assert_eq!(first["target"]["chosen"], "first_failure", "{first}");
    assert_ne!(first["query_check"]["result"], "valid", "{first}");
    let goal = first["target"]["assert_id"].clone();
    assert!(goal.is_array(), "{}", first);
    let goal_line = line_of(SCAFFOLD_SOURCE, "assert(f(x) != f(x + 1));");
    assert!(first["target"]["insert_before"].as_str().unwrap().contains(&goal_line), "{}", first);
    assert_eq!(first["target"]["placement"], "before_span", "{}", first);
    assert!(first["target"]["goal"].is_u64(), "{}", first);
    assert!(first["lowered_as"].as_str().unwrap().contains("g(crate::f(x))"), "{}", first);
    assert!(first["stack_levels"].is_u64(), "{}", first);
    // an ordinary session has no provenance to say why
    assert!(first["why"].is_null(), "{}", first);
    let snippet = first["verus_snippet"].as_str().unwrap().to_owned();
    assert_eq!(snippet, "assert(g(f(x)) == x);");
    // The goal under P instantiated the inverse; alone it could not.
    let under = &first["goal_given_p"]["cost"];
    assert!(under["instantiations"].as_u64().unwrap() >= 1, "{}", first);
    assert!(first["marginal_cost"]["instantiations_delta"].as_i64().unwrap() >= 1, "{}", first);

    let mut warm = Vec::new();
    for (p, case, provable, closes) in SCAFFOLD_CASES {
        let reply = worker.send(request(json!({"assert": p, "assert_id": goal})));
        assert_eq!(reply["event"], "scaffold", "{p}: {reply}");
        assert_eq!(reply["target"]["chosen"], "requested", "{reply}");
        assert!(reply["query_check"].is_null(), "{}", reply);
        assert_ne!(reply["baseline"]["result"], "valid", "{reply}");
        let answer =
            (reply["p_provable"]["result"] == "valid", reply["goal_given_p"]["result"] == "valid");
        assert_eq!(answer, (*provable, *closes), "{p}: {reply}");
        assert_eq!(reply["case"], *case, "{reply}");
        assert_eq!(reply["verus_snippet"].is_string(), *case == "scaffold", "{reply}");
        for arm in ["baseline", "p_provable", "goal_given_p"] {
            assert!(
                reply[arm]["cost"]["resource_units"].as_u64().unwrap() > 0,
                "{}: {}",
                arm,
                reply
            );
        }
        warm.push(answer);
    }

    // P not checked: the goal's verdict alone, conditional on P.
    let only = worker.send(request(
        json!({"assert": SCAFFOLD_CASES[2].0, "assert_id": goal, "goal_only": true}),
    ));
    assert_eq!(only["case"], "goal_closes_given_p", "{only}");
    assert!(only["p_provable"].is_null(), "{}", only);

    // Refusals name the reason and keep the session.
    for (text, reason) in [
        ("h(x) > 0", "no function"),
        ("forall|i: int| f(i) > 0", "quantifier-free"),
        ("x +", "cannot read"),
        ("f(x)", "not a bool"),
    ] {
        let refused = worker.send(request(json!({"assert": text, "assert_id": goal})));
        assert_eq!(refused["event"], "error", "{}: {}", text, refused);
        assert!(refused["message"].as_str().unwrap().contains(reason), "{}: {}", text, refused);
    }
    let missing = worker.send(request(json!({"assert": "x > 0", "assert_id": [999]})));
    assert!(missing["message"].as_str().unwrap().contains("its goals are"), "{}", missing);
    let passing = query_id(&ready, "::scaffold_passing");
    let refused = worker
        .send(json!({"command": "scaffold", "session": session, "bucket": 0, "query": passing,
            "assert": "x > 0"}));
    assert!(refused["message"].as_str().unwrap().contains("verifies"), "{}", refused);

    assert!(!checks_valid(&mut worker, &ready, "::scaffold_target"));
    assert!(checks_valid(&mut worker, &ready, "::scaffold_passing"));
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);
    let launches = fs::read_to_string(worker.dir.path().join("launches")).unwrap();
    assert_eq!(launches.lines().count(), 1, "{launches}");
    for log in smt_logs(worker.dir.path()) {
        assert_eq!(log.matches("(push").count(), log.matches("(pop").count());
    }

    // Cold: every case as source, through the ordinary pipeline, and the
    // snippet pasted before the goal.
    let requires = "requires forall|i: int| #[trigger] g(f(i)) == i,";
    let mut functions = String::new();
    for (n, (p, ..)) in SCAFFOLD_CASES.iter().enumerate() {
        functions.push_str(&format!(
            "proof fn cold_p_{n}(x: int) {requires} {{ assert({p}); }}\n\
             proof fn cold_g_{n}(x: int) {requires} {{ assume({p}); assert(f(x) != f(x + 1)); }}\n"
        ));
    }
    functions.push_str(&format!(
        "proof fn pasted(x: int) {requires} {{ {snippet} assert(f(x) != f(x + 1)); }}\n"
    ));
    let cold_source = SCAFFOLD_SOURCE.replace(
        "    proof fn scaffold_passing",
        &format!("{functions}\n    proof fn scaffold_passing"),
    );
    let mut cold = Worker::start(&cold_source, &[]);
    let cold_ready = cold.receive();
    assert_eq!(cold_ready["event"], "ready", "{cold_ready}");
    for (n, answer) in warm.iter().enumerate() {
        let cold_answer = (
            checks_valid(&mut cold, &cold_ready, &format!("::cold_p_{n}")),
            checks_valid(&mut cold, &cold_ready, &format!("::cold_g_{n}")),
        );
        assert_eq!(*answer, cold_answer, "case {n}: warm {answer:?}, cold {cold_answer:?}");
    }
    assert!(checks_valid(&mut cold, &cold_ready, "::pasted"));
    cold.send(json!({"command": "close", "session": cold_ready["session"]}));
    cold.finish(false);
}

/// Every query of the function `name`, by id.
fn query_ids(ready: &Value, name: &str) -> Vec<Value> {
    ready["buckets"][0]["queries"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|query| query["function"].as_str().unwrap().ends_with(name))
        .map(|query| query["id"].clone())
        .collect()
}

/// A goal Verus emits without an assert id, the invariant at the end of the
/// loop body, is the one the query's check fails at, and is addressed by
/// its index. `P` reads `i` after the increment, so the inverse at the new
/// `i` scaffolds the goal, and pasted at the end of the body, where the
/// reply says, it makes the function verify.
#[test]
fn resident_scaffold_addresses_a_goal_without_an_assert_id() {
    let mut worker = Worker::start(INVARIANT_SOURCE, &[]);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready", "{}", ready);
    let session = ready["session"].clone();
    let queries = ready["buckets"][0]["queries"].as_array().unwrap();
    let body = queries
        .iter()
        .find(|q| q["description"] == "while loop")
        .unwrap_or_else(|| panic!("no loop query: {}", ready))["id"]
        .clone();
    let p = "g(f(i as int)) == i as int";
    let reply = worker.send(json!({"command": "scaffold", "session": session, "bucket": 0,
        "query": body, "assert": p}));
    assert_eq!(reply["event"], "scaffold", "{}", reply);
    assert_eq!(reply["target"]["chosen"], "first_failure", "{}", reply);
    assert_eq!(reply["target"]["assert_id"], json!([]), "{}", reply);
    assert_eq!(
        reply["target"]["description"], "invariant not satisfied at end of loop body",
        "{}",
        reply
    );
    assert_eq!(reply["target"]["placement"], "end_of_loop_body", "{}", reply);
    assert!(reply["target"]["insert_before"].is_null(), "{}", reply);
    assert_eq!(reply["case"], "scaffold", "{}", reply);
    let index = reply["target"]["goal"].as_u64().unwrap();
    // the same goal by index, and P read at the old `i` is no help
    let again = worker.send(json!({"command": "scaffold", "session": session, "bucket": 0,
        "query": body, "assert": p, "goal": index}));
    assert_eq!(again["target"]["chosen"], "requested", "{}", again);
    assert_eq!(again["case"], "scaffold", "{}", again);
    let old = worker.send(json!({"command": "scaffold", "session": session, "bucket": 0,
        "query": body, "assert": "g(f(i as int - 1)) == i as int - 1", "goal": index}));
    assert_eq!(old["case"], "true_but_unhelpful", "{}", old);
    let missing = worker.send(json!({"command": "scaffold", "session": session, "bucket": 0,
        "query": body, "assert": p, "goal": 999}));
    let message = missing["message"].as_str().unwrap();
    assert!(message.contains("its goals are") && message.contains("no assert id"), "{}", missing);
    worker.send(json!({"command": "close", "session": session}));
    worker.finish(false);

    let pasted = INVARIANT_SOURCE.replace("i = i + 1;", &format!("i = i + 1; assert({p});"));
    let mut cold = Worker::start(&pasted, &[]);
    let cold_ready = cold.receive();
    for id in query_ids(&cold_ready, "::scaffold_loop") {
        let result = cold.send(json!({"command": "check", "session": cold_ready["session"],
            "bucket": 0, "query": id}));
        assert_eq!(result["result"], "valid", "{}", result);
    }
    cold.send(json!({"command": "close", "session": cold_ready["session"]}));
    // the invocation verified everything, so the worker exits well
    cold.finish(true);
}

/// The claim of `assert ... by` is checked after the block's steps, and the
/// reply places the snippet at the block's end, naming no span. A goal
/// among the steps, or in a closure body (also a dead end), is placed before
/// its own span. Of two failing goals, the default is the earlier, as Verus
/// reports it.
#[test]
fn resident_scaffold_places_p_where_the_goal_is_checked() {
    let mut worker = Worker::start(SCAFFOLD_SOURCE, &[]);
    let ready = worker.receive();
    let scaffold = |worker: &mut Worker<ChildStdin>, name: &str, p: &str| {
        let reply = worker.send(json!({"command": "scaffold", "session": ready["session"],
            "bucket": 0, "query": query_id(&ready, name), "assert": p}));
        assert_eq!(reply["event"], "scaffold", "{}", reply);
        assert_eq!(reply["target"]["chosen"], "first_failure", "{}", reply);
        reply
    };
    let reply = scaffold(&mut worker, "::scaffold_by", SCAFFOLD_CASES[0].0);
    assert_eq!(reply["target"]["placement"], "end_of_proof_block", "{}", reply);
    assert!(reply["target"]["insert_before"].is_null(), "{}", reply);
    assert_eq!(reply["case"], "scaffold", "{}", reply);

    for (name, p, goal) in [
        ("::scaffold_step", SCAFFOLD_CASES[0].0, "assert(f(x) != f(1 + x));"),
        (
            "::scaffold_closure",
            "g(f(y as int)) == y as int",
            "assert(f(y as int) != f(y as int + 1));",
        ),
    ] {
        let reply = scaffold(&mut worker, name, p);
        assert_eq!(reply["target"]["placement"], "before_span", "{}: {}", name, reply);
        let at = reply["target"]["insert_before"].as_str().unwrap_or_default();
        assert!(at.contains(&line_of(SCAFFOLD_SOURCE, goal)), "{}: {}", name, reply);
        assert_eq!(reply["case"], "scaffold", "{}: {}", name, reply);
    }

    let reply = scaffold(&mut worker, "::scaffold_two_failing", "x > 100");
    let at = reply["target"]["insert_before"].as_str().unwrap_or_default();
    assert!(at.contains(&line_of(SCAFFOLD_SOURCE, "assert(x != 7);")), "{}", reply);
    assert!(reply["query_check"]["rechecks"].as_u64().unwrap() >= 1, "{}", reply);

    // A postcondition at an early `return` is checked there, and P goes
    // right before the `return`, not at the `ensures` clause (the message's
    // primary span). At the end of the body P goes before the body's final
    // expression, which the message's label names.
    let exit = scaffold(&mut worker, "::scaffold_exit", SCAFFOLD_CASES[0].0);
    assert_eq!(exit["target"]["placement"], "before_span", "{}", exit);
    let at = exit["target"]["insert_before"].as_str().unwrap_or_default();
    assert!(at.contains(&line_of(SCAFFOLD_SOURCE, "return x;")), "{}", exit);
    assert_eq!(exit["case"], "scaffold", "{}", exit);
    let exit_query = query_id(&ready, "::scaffold_exit");
    let end = (0..4)
        .map(|goal| {
            worker.send(json!({"command": "scaffold", "session": ready["session"], "bucket": 0,
                "query": exit_query, "assert": SCAFFOLD_CASES[0].0, "goal": goal}))
        })
        .find(|reply| reply["target"]["placement"] == "end_of_body")
        .expect("a goal at the end of the body");
    let tail = SCAFFOLD_SOURCE.lines().position(|l| l.trim() == "x").unwrap() + 1;
    let at = end["target"]["insert_before"].as_str().unwrap_or_default();
    assert!(at.contains(&format!("fixture.rs:{tail}:")), "{}", end);
    assert_eq!(end["case"], "scaffold", "{}", end);
    worker.send(json!({"command": "close", "session": ready["session"]}));
    worker.finish(false);

    // Pasted where the two replies say, the function verifies.
    let snippet = exit["verus_snippet"].as_str().unwrap();
    let pasted = SCAFFOLD_SOURCE
        .replace("return x;", &format!("{snippet} return x;"))
        .replace("        x\n    }", &format!("        {snippet} x\n    }}"));
    assert_eq!(pasted.matches(snippet).count(), 2, "{}", pasted);
    let mut cold = Worker::start(&pasted, &[]);
    let cold_ready = cold.receive();
    for id in query_ids(&cold_ready, "::scaffold_exit") {
        let result = cold.send(json!({"command": "check", "session": cold_ready["session"],
            "bucket": 0, "query": id}));
        assert_eq!(result["result"], "valid", "{}", result);
    }
    cold.send(json!({"command": "close", "session": cold_ready["session"]}));
    cold.finish(false);
}

/// A matching loop runs the query out of budget, and a resource limit names
/// no goal: the worker checks each goal alone and takes the first that
/// fails, here the postcondition. Assuming it closes the goal; proving it
/// runs out of budget again, which proves nothing, so P is undecided.
#[test]
fn resident_scaffold_finds_the_goal_behind_a_resource_limit() {
    let mut worker = Worker::start(BISECT_SOURCE, &["--rlimit", "2"]);
    let ready = worker.receive();
    let reply = worker.send(json!({"command": "scaffold", "session": ready["session"],
        "bucket": 0, "query": query_id(&ready, "::looping"), "assert": "a(0) > 100"}));
    assert_eq!(reply["event"], "scaffold", "{}", reply);
    assert_eq!(reply["query_check"]["result"], "resource_limit", "{}", reply);
    assert_eq!(reply["target"]["chosen"], "first_failing_alone", "{}", reply);
    assert!(reply["target"]["goals_probed"].as_u64().unwrap() >= 1, "{}", reply);
    assert_eq!(reply["case"], "helpful_but_undecided", "{}", reply);
    assert_eq!(reply["p_provable"]["result"], "resource_limit", "{}", reply);
    worker.send(json!({"command": "close", "session": ready["session"]}));
    worker.finish(false);
}

/// Under provenance, the goal that closes with `P` assumed says why: the
/// `requires` it used, and the inverse's instantiations at their source.
#[test]
fn resident_scaffold_says_why_under_provenance() {
    let mut worker = Worker::start(SCAFFOLD_SOURCE, &["-V", "provenance"]);
    let ready = worker.receive();
    assert_eq!(ready["provenance"], true, "{ready}");
    let reply = worker.send(json!({"command": "scaffold", "session": ready["session"],
        "bucket": 0, "query": query_id(&ready, "::scaffold_target"),
        "assert": SCAFFOLD_CASES[0].0}));
    assert_eq!(reply["case"], "scaffold", "{reply}");
    let inverse = line_of(SCAFFOLD_SOURCE, "g(f(i)) == i");
    let why = &reply["why"];
    let explains = why["explains_goal"].as_array().unwrap();
    assert!(
        explains.iter().any(|tag| tag["kind"] == "requires"
            && tag["span"].as_str().is_some_and(|span| span.contains(&inverse))),
        "{}",
        reply
    );
    let closing = why["closing_quantifiers"].as_array().unwrap();
    assert!(
        closing.iter().any(|q| q["span"].as_str().is_some_and(|span| span.contains(&inverse))),
        "{}",
        reply
    );
    worker.send(json!({"command": "close", "session": ready["session"]}));
    worker.finish(false);
}

const SPECULATE_GOAL_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    spec fn f(x: int) -> int;
    spec fn g(x: int) -> int;

    proof fn shadowed(i: int)
        requires forall|i: int| #![trigger g(i)] g(i) > 0 && f(i) > 0,
    {
        assert(f(i) > 0);
    }

    proof fn reassigned(a: int)
        requires forall|i: int| #![trigger g(i)] g(i) > 0 && f(i) > 0,
    {
        let mut y = a;
        y = y + 1;
        assert(f(y) > 0);
    }

    proof fn last_of(s: Seq<int>)
        requires s.len() > 0, forall|i: int| #![trigger g(i)] 0 <= i < s.len() ==> s[i] > 0,
    {
        assert(s[s.len() - 1] > 0);
    }

    spec fn p<A>(x: A) -> bool;
    spec fn r<A>(x: A, y: A) -> bool;

    proof fn eliminated<A>(a: A)
        requires forall|x: A, y: A| #![trigger r(x, y)] x == y ==> p(x),
    {
        assert(p(a));
    }
}
"#;

/// The options for a cvc5 build whose version differs from the pinned
/// release, without `speculate_options`' small budget.
fn version_options() -> Vec<&'static str> {
    match std::env::var_os("RESIDENT_NO_SOLVER_VERSION_CHECK") {
        Some(_) => vec!["-V", "no-solver-version-check"],
        None => Vec::new(),
    }
}

/// A probe of the quantifier in `function`'s own query.
fn probe_own<E: Endpoint>(
    worker: &mut Worker<E>,
    ready: &Value,
    function: &str,
    hypothesis: impl FnOnce(&Value) -> Value,
) -> Value {
    let session = ready["session"].clone();
    let query = query_id(ready, function);
    let qid = own_quantifier(worker, &session, &query)["qid"].clone();
    probe(worker, &session, &query, Some(hypothesis(&qid)))
}

/// `function`'s check in a fresh worker on `source`.
fn cold_check(source: &str, function: &str, options: &[&str]) -> Value {
    let mut worker = Worker::start(source, options);
    let ready = worker.receive();
    let checked = worker.send(json!({"command": "check", "session": ready["session"],
        "bucket": 0, "query": query_id(&ready, function)}));
    worker.send(json!({"command": "close", "session": ready["session"]}));
    worker.finish(false);
    checked
}

/// A hypothesis's terms are read at the goal the query fails at. An
/// instantiation's never name the quantifier's own variable, so a parameter
/// it shadows is the parameter; a mutable local reads as its value there;
/// Verus method calls and the prelude's arithmetic in SMT spelling are
/// read; and a snippet names no variable at another version than the
/// goal's, so pasted before the goal it verifies.
#[test]
fn resident_speculate_reads_terms_at_the_goal() {
    let options = version_options();
    let mut worker = Worker::start(SPECULATE_GOAL_SOURCE, &options);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready", "{ready}");
    let instantiation =
        |subst: Value| move |qid: &Value| json!({"instantiation": {"qid": qid, "subst": subst}});

    let shadowed = probe_own(&mut worker, &ready, "::shadowed", instantiation(json!({"i": "i"})));
    assert_eq!(shadowed["closed"], true, "{shadowed}");
    assert!(shadowed["verus_snippet"].as_str().unwrap().contains("crate::f(i)"), "{}", shadowed);

    let local = probe_own(&mut worker, &ready, "::reassigned", instantiation(json!({"i": "y"})));
    assert_eq!(local["status"], "applied", "{local}");
    assert_eq!(local["closed"], true, "{local}");
    let pasted = local["verus_snippet"].as_str().unwrap();
    assert!(pasted.contains("crate::f(y)"), "{}", local);
    let source = SPECULATE_GOAL_SOURCE
        .replace("assert(f(y) > 0);", &format!("{pasted}\n        assert(f(y) > 0);"));
    assert_eq!(cold_check(&source, "::reassigned", &options)["result"], "valid");

    let spelled =
        probe_own(&mut worker, &ready, "::reassigned", instantiation(json!({"i": "(Add a! 1)"})));
    assert_eq!(spelled["closed"], true, "{spelled}");

    // The trigger matches the goal's term as cvc5 holds it, over the first
    // version of `y`; an assert of it could only paste as a claim about
    // the second, so it is offered only when it names none.
    let triggered = probe_own(
        &mut worker,
        &ready,
        "::reassigned",
        |qid| json!({"trigger_pattern": {"qid": qid, "pattern": "f(i)"}}),
    );
    assert_eq!(triggered["closed"], true, "{triggered}");
    if let Some(fallback) = triggered["fallback_snippet"].as_str() {
        let source = SPECULATE_GOAL_SOURCE
            .replace("assert(f(y) > 0);", &format!("{fallback}\n        assert(f(y) > 0);"));
        assert_eq!(cold_check(&source, "::reassigned", &options)["result"], "valid", "{fallback}");
    }

    let method =
        probe_own(&mut worker, &ready, "::last_of", instantiation(json!({"i": "s.len() - 1"})));
    assert_eq!(method["status"], "applied", "{method}");
    assert_eq!(method["closed"], true, "{method}");

    // A generic quantifier with an equality guard. cvc5 at da4b2b0073 keeps
    // both variables of this one (the equality is between boxed values
    // under type guards); where it eliminates one, the instance goes
    // without it, and a snippet offered is the instance cvc5 made.
    let eliminated =
        probe_own(&mut worker, &ready, "::eliminated", instantiation(json!({"x": "a", "y": "a"})));
    assert_eq!(eliminated["closed"], true, "{eliminated}");
    if let Some(snippet) = eliminated["verus_snippet"].as_str() {
        let source = SPECULATE_GOAL_SOURCE
            .replace("assert(p(a));", &format!("{snippet}\n        assert(p(a));"));
        assert_eq!(cold_check(&source, "::eliminated", &options)["result"], "valid", "{snippet}");
    }

    assert_eq!(
        worker.send(json!({"command": "close", "session": ready["session"]}))["event"],
        "closed"
    );
    worker.finish(false);
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
#[test]
fn resident_inst_graph_finds_the_matching_loop() {
    let mut worker = Worker::start_with_env(
        LOOP_SOURCE,
        &["--rlimit", "1"],
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
    assert_eq!(summary["check"], "search", "{checked}");
    assert!(summary["instantiations"].as_u64().unwrap() > 10, "{}", checked);
    assert!(summary["edges"].as_u64().unwrap() > 5, "{}", checked);
    assert!(summary["max_depth"].as_u64().unwrap() > 2, "{}", checked);

    let cycles = graph(&mut worker, &looping, json!({"op": "cycles"}));
    assert_eq!(cycles["event"], "inst_graph", "{cycles}");
    let result = &cycles["result"];
    assert_eq!(result["op"], "cycles");
    let found = result["cycles"].as_array().unwrap();
    assert_eq!(found.len(), 1, "{result}");
    assert_eq!(found[0]["length"], 2, "{result}");
    assert!(found[0]["repetitions"].as_u64().unwrap() > 5, "{}", result);
    for node in found[0]["nodes"].as_array().unwrap() {
        assert!(node["function"].as_str().unwrap().ends_with("::roundtrip"), "{}", node);
        assert!(node["source_span"].as_str().unwrap().contains("fixture.rs"), "{}", node);
    }
    // Each unrolling is one deeper than the last.
    let depths: Vec<u64> = found[0]["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|n| n["depth"].as_u64().unwrap())
        .collect();
    assert!(depths.windows(2).all(|pair| pair[1] == pair[0] + 1), "{:?}", depths);

    // The loop's quantifiers are the costliest, and a filter on another
    // function leaves nothing to report.
    let cost = graph(&mut worker, &looping, json!({"op": "top_cost", "limit": 2}));
    let ranked = cost["result"]["quantifiers"].as_array().unwrap();
    let loop_qids: BTreeSet<&str> =
        found[0]["quantifiers"].as_array().unwrap().iter().map(|q| q.as_str().unwrap()).collect();
    let top: BTreeSet<&str> = ranked.iter().map(|q| q["qid"].as_str().unwrap()).collect();
    assert_eq!(top, loop_qids, "{cost}");
    // `source_fn` matches whole path segments: the loop's function and its
    // crate find the loop, a partial segment or another crate does not.
    let function = found[0]["nodes"][0]["function"].as_str().unwrap().to_owned();
    let krate = function.strip_suffix("::roundtrip").unwrap().to_owned();
    let partial = function.strip_suffix("trip").unwrap().to_owned();
    for (source_fn, cycles) in
        [(function.as_str(), 1), (krate.as_str(), 1), (partial.as_str(), 0), ("no_such_crate::", 0)]
    {
        let filtered = graph(
            &mut worker,
            &looping,
            json!({"op": "cycles", "filter": {"source_fn": source_fn}}),
        );
        assert_eq!(
            filtered["result"]["cycles"].as_array().unwrap().len(),
            cycles,
            "{source_fn}: {filtered}"
        );
    }
    // Naming one member of the loop finds the whole loop.
    let member = found[0]["quantifiers"][0].as_str().unwrap();
    let named =
        graph(&mut worker, &looping, json!({"op": "cycles", "filter": {"quantifier": member}}));
    assert_eq!(named["result"]["cycles"][0]["length"], 2, "{}", named);

    // The deepest instantiation descends from a root through the loop.
    let deepest = found[0]["nodes"].as_array().unwrap().last().unwrap()["inst"].clone();
    let path =
        graph(&mut worker, &looping, json!({"op": "path", "to_inst": deepest, "limit": 1000}));
    let chain = path["result"]["nodes"].as_array().unwrap();
    assert_eq!(chain.last().unwrap()["inst"], deepest, "{path}");
    assert_eq!(chain[0]["depth"], 0, "{path}");
    let growth = graph(&mut worker, &looping, json!({"op": "growth"}));
    assert_eq!(growth["result"]["step"], "round", "{growth}");
    assert!(!growth["result"]["per_round"].as_array().unwrap().is_empty(), "{}", growth);
    let pathless = graph(&mut worker, &looping, json!({"op": "path"}));
    assert_eq!(pathless["event"], "error", "{pathless}");

    // A qid nothing was instantiated for is refused rather than answered: an
    // op that found nothing would otherwise read like a graph holding nothing.
    // A `source_fn` prefix owning no quantifier is a fair question with an
    // empty answer, so it is answered, with `matching_nodes` saying as much.
    let refused =
        graph(&mut worker, &looping, json!({"op": "cycles", "filter": {"quantifier": "absent"}}));
    assert_eq!(refused["event"], "error", "{refused}");
    let empty =
        graph(&mut worker, &looping, json!({"op": "cycles", "filter": {"source_fn": "no::such"}}));
    assert_eq!(empty["result"]["matching_nodes"], 0, "{empty}");
    // A filter that stands for something but selects nothing is answered, and
    // says so: `matching_nodes` separates it from a graph with nothing in it.
    let total = summary["instantiations"].as_u64().unwrap();
    for op in ["cycles", "top_cost", "subgraph", "growth"] {
        let deep = graph(&mut worker, &looping, json!({"op": op, "filter": {"min_depth": 9999}}));
        assert_eq!(deep["result"]["matching_nodes"], 0, "{op}: {deep}");
        assert_eq!(deep["result"]["total_instantiations"], total, "{op}: {deep}");
        let all = graph(&mut worker, &looping, json!({"op": op}));
        assert_eq!(all["result"]["matching_nodes"], total, "{op}: {all}");
    }
    // `path` takes no filter, and claims no count.
    let walked =
        graph(&mut worker, &looping, json!({"op": "path", "to_inst": deepest, "limit": 1000}));
    assert!(walked["result"]["matching_nodes"].is_null(), "{}", walked);

    // A healthy query records its own, smaller graph.
    let healthy =
        worker.send(json!({"command": "check", "session": session, "bucket": 0, "query": passing}));
    assert_eq!(healthy["result"], "valid", "{healthy}");
    assert!(healthy["inst_graph"].is_object(), "{}", healthy);
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(false);

    // Without the variable, no graph is recorded or served.
    let mut plain = Worker::start(LOOP_SOURCE, &["--rlimit", "1"]);
    let ready = plain.receive();
    assert_eq!(ready["inst_graph"], false);
    let session = ready["session"].clone();
    let checked =
        plain.send(json!({"command": "check", "session": session, "bucket": 0, "query": passing}));
    assert!(checked["inst_graph"].is_null(), "{}", checked);
    let refused = plain.send(
        json!({"command": "inst_graph", "session": session, "bucket": 0, "query": passing, "op": "cycles"}),
    );
    assert_eq!(refused["event"], "error", "{refused}");
    assert_eq!(plain.send(json!({"command": "close", "session": session}))["event"], "closed");
    plain.finish(false);
}

/// Every quantifier in a graph but the prelude's has an owner: a function's
/// definition and pre/post axioms their function, a datatype's box and type
/// axioms the datatype, so `source_fn` finds those too.
#[test]
fn resident_inst_graph_names_internal_axiom_owners() {
    let source = r#"
use vstd::prelude::*;
verus! {
    proof fn pushed(s: Seq<int>)
        requires s.len() > 3,
        ensures
            s.push(1).len() == s.len() + 1,
            s.subrange(0, 2).len() == 2,
            s.push(7)[s.len() as int] == 7,
    {
    }
}
"#;
    let mut worker = Worker::start_with_env(source, &[], &[("VERUS_RESIDENT_INST_GRAPH", "1")]);
    let ready = worker.receive();
    assert_eq!(ready["event"], "ready", "{}", ready);
    let succeeded = ready["invocation_succeeded"].as_bool().unwrap();
    let session = ready["session"].clone();
    let query = query_id(&ready, "::pushed");
    let checked =
        worker.send(json!({"command": "check", "session": session, "bucket": 0, "query": query}));
    assert_eq!(checked["result"], "valid", "{}", checked);
    // Each node as (qid, owner).
    let mut subgraph = |filter: Value| -> Vec<(String, Option<String>)> {
        let reply = worker.send(json!({"command": "inst_graph", "session": session, "bucket": 0,
            "query": query, "op": "subgraph", "limit": 1000, "filter": filter}));
        reply["result"]["nodes"]
            .as_array()
            .unwrap_or_else(|| panic!("{}", reply))
            .iter()
            .map(|n| {
                (n["qid"].as_str().unwrap().to_owned(), n["function"].as_str().map(str::to_owned))
            })
            .collect()
    };

    let all = subgraph(json!({}));
    for (qid, owner) in &all {
        assert_eq!(owner.is_none(), qid.starts_with("prelude_"), "{} {:?}", qid, owner);
    }
    let owner_of = |qid: &str| all.iter().find(|(q, _)| q == qid).and_then(|(_, o)| o.clone());
    let len = "internal_vstd!seq.Seq.len.?_pre_post_definition";
    assert_eq!(owner_of(len).as_deref(), Some("vstd::seq::Seq::len"), "{:?}", all);
    let (boxed, boxed_owner) = all
        .iter()
        .find(|(q, _)| {
            q.starts_with("internal_vstd__seq__Seq<") && q.ends_with("_axiom_definition")
        })
        .unwrap_or_else(|| panic!("no datatype axiom in {:?}", all));
    assert!(boxed_owner.as_deref().unwrap().starts_with("vstd::seq::Seq<"), "{:?}", boxed_owner);

    // The datatype's path takes its axioms, its instantiations' and its
    // methods', and nothing else.
    let seq = subgraph(json!({"source_fn": "vstd::seq::Seq"}));
    assert!(seq.iter().any(|(q, _)| q == boxed) && seq.iter().any(|(q, _)| q == len), "{:?}", seq);
    for (qid, owner) in &seq {
        assert!(owner.as_deref().unwrap().starts_with("vstd::seq::Seq"), "{} {:?}", qid, owner);
    }
    assert_eq!(worker.send(json!({"command": "close", "session": session}))["event"], "closed");
    worker.finish(succeeded);
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
    assert!(name.starts_with('c') && name.ends_with(".smt2"), "{}", name);
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

/// A session under `-V matching-loops=N` reports, with a check that came back
/// unknown, the quantifier that fed its own trigger, in source spelling; an
/// unknown without a loop reports none.
///
/// Needs the pinned cvc5 to have `--matching-loops` and to report the
/// trigger that matched (BasisResearch/cvc5#3 and #10).
#[test]
fn resident_matching_loops_name_the_self_feeding_quantifier() {
    let source = r#"
use vstd::prelude::*;
verus! {
    pub uninterp spec fn a(i: int) -> int;
    pub uninterp spec fn h(x: int) -> int;

    proof fn loops()
        requires forall|i: int| #[trigger] a(i) < a(i + 1),
        ensures a(0) > 100,
    {
    }

    proof fn incomplete(x: int)
        requires forall|y: int| #[trigger] h(y) > 0,
        ensures h(x) > 1,
    {
    }

    pub uninterp spec fn b(i: int) -> int;

    proof fn twin()
        requires
            forall|i: int| #[trigger] a(i) < a(i + 1),
            forall|i: int| #[trigger] b(i) < b(i - 1),
        ensures a(0) + b(0) > 100,
    {
    }

    proof fn indexed(s: Seq<int>)
        requires forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] < s[i + 1],
        ensures s.len() > 5 ==> s[0] + 100 < s[5],
    {
    }
}
"#;
    let mut worker = Worker::start(source, &["-V", "matching-loops=20"]);
    let ready = worker.receive();
    assert_eq!(ready["matching_loops"], true, "{ready}");
    let checked = worker.send(json!({"command":"check", "session":ready["session"], "bucket":0, "query":query_id(&ready, "loops")}));
    assert_eq!(checked["result"], "invalid", "{checked}");
    let report = &checked["matching_loops"];
    assert_eq!(report["max_inst_rounds"], true, "{checked}");
    let found = report["loops"].as_array().unwrap();
    let culprit = found
        .iter()
        .find(|l| l["trigger"].as_str().is_some_and(|t| t.contains("a(i)")))
        .unwrap_or_else(|| panic!("no loop on a: {}", checked));
    assert_eq!(culprit["confidence"], "high", "{}", culprit);
    assert_eq!(culprit["edges"], "confirmed", "{}", culprit);
    assert!(culprit["fun"].as_str().unwrap().ends_with("::loops"), "{}", culprit);
    assert!(culprit["span"].as_str().unwrap().contains("fixture.rs"), "{}", culprit);
    assert!(culprit["growth_rate"].as_str().unwrap().starts_with("linear-depth"), "{}", culprit);
    let ladder = culprit["term_ladder"].as_array().unwrap();
    assert!(ladder.len() >= 3, "{}", culprit);
    assert!(ladder[1].as_str().unwrap().contains("(0 + 1)"), "{}", culprit);
    assert!(ladder[2].as_str().unwrap().contains("((0 + 1) + 1)"), "{}", culprit);
    // cvc5 sends the first rungs and the last of the 20-round chain
    assert!(ladder.iter().any(|rung| rung == "…"), "{}", culprit);
    assert!(culprit["growth_rate"].as_str().unwrap().contains("solver term depth"), "{}", culprit);
    // the prelude axioms the loop drags along are not loops of their own
    assert!(
        found.iter().all(|l| l["fun"].as_str().is_some_and(|f| f.ends_with("::loops"))),
        "{}",
        checked
    );
    let checked = worker.send(json!({"command":"check", "session":ready["session"], "bucket":0, "query":query_id(&ready, "incomplete")}));
    assert_eq!(checked["result"], "invalid", "{checked}");
    assert_eq!(checked["matching_loops"]["loops"], json!([]), "{checked}");
    // two written loops, each reported on its own. cvc5 leaves out most
    // formulas that only ride a loop; any it still lists follow a loop whose
    // terms they share, so subtraction never follows a's loop
    let checked = worker.send(json!({"command":"check", "session":ready["session"], "bucket":0, "query":query_id(&ready, "twin")}));
    let found = checked["matching_loops"]["loops"].as_array().unwrap();
    let on = |f: &str| {
        found
            .iter()
            .find(|l| l["trigger"].as_str().is_some_and(|t| t.contains(f)))
            .unwrap_or_else(|| panic!("no loop on {}: {}", f, checked))
    };
    let follows = |l: &serde_json::Value, qid: &str| {
        l["followers"].as_array().is_some_and(|fs| fs.iter().any(|f| f == qid))
    };
    assert_eq!(found.len(), 2, "{}", checked);
    on("b(i)");
    assert!(!follows(on("a(i)"), "prelude_sub"), "{}", checked);
    // the axiom Verus generates for `Seq::index` rides the written loop
    let checked = worker.send(json!({"command":"check", "session":ready["session"], "bucket":0, "query":query_id(&ready, "indexed")}));
    let found = checked["matching_loops"]["loops"].as_array().unwrap();
    assert!(!found.is_empty(), "{}", checked);
    assert!(found.iter().all(|l| l["qid"].as_str().unwrap().starts_with("user_")), "{}", checked);
    assert_eq!(
        worker.send(json!({"command":"close", "session":ready["session"]}))["event"],
        "closed"
    );
    worker.finish(false);
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

/// The prelude's quantifiers keep cvc5 from confirming a model, so a failing
/// query answers `unknown` (incomplete) rather than `sat`. The reply says why,
/// in every mode; a query that was proved carries no reason.
#[test]
fn resident_checks_say_why_the_solver_answered_unknown() {
    let mut worker = Worker::start(SOURCE, &[]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    for _ in 0..2 {
        let failing = worker.send(
            json!({"command":"check", "session":session, "bucket":0, "query":query_id(&ready, "::failing")}),
        );
        assert_eq!(failing["result"], "invalid", "{}", failing);
        let reason = &failing["unknown_reason"];
        assert_eq!(reason["reason"], "incomplete", "{}", failing);
        assert!(reason["desc"].is_string() && reason["span"].is_string(), "{}", failing);
        // A cvc5 older than the incomplete-id key answers `unsupported`, which
        // leaves the id out and the culprits empty.
        let culprits = reason["culprits"].as_array().unwrap();
        if let Some(id) = reason.get("incomplete_id").and_then(|id| id.as_str()) {
            assert!(id.starts_with("QUANTIFIERS"), "{}", failing);
            // At least the prelude's quantifiers are asserted in every query.
            assert!(!culprits.is_empty(), "{}", failing);
        }
        // Source-spanned culprits lead and the prelude's come last.
        let rank = |culprit: &Value| match (culprit.get("span"), culprit["fun"].as_str()) {
            (Some(_), _) => 0,
            (None, Some("prelude")) => 2,
            (None, _) => 1,
        };
        assert!(culprits.iter().all(|culprit| culprit["qid"].is_string()), "{}", failing);
        assert!(culprits.windows(2).all(|pair| rank(&pair[0]) <= rank(&pair[1])), "{}", failing);
        let passing = worker.send(
            json!({"command":"check", "session":session, "bucket":0, "query":query_id(&ready, "::passing")}),
        );
        assert_eq!(passing["result"], "valid", "{}", passing);
        assert!(passing["unknown_reason"].is_null(), "{}", passing);
    }
    assert_eq!(worker.send(json!({"command":"close", "session":session}))["event"], "closed");
    worker.finish(false);
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

/// `ready` names the requests the worker serves, so a client can tell a
/// request this build does not have from one it rejected: both answer with the
/// same error otherwise.
#[test]
fn resident_ready_lists_the_requests_it_serves() {
    let mut worker = Worker::start("use vstd::prelude::*; verus! { proof fn passing() {} }", &[]);
    let ready = worker.receive();
    let commands: Vec<String> = ready["commands"]
        .as_array()
        .unwrap_or_else(|| panic!("{}", ready))
        .iter()
        .map(|command| command.as_str().unwrap().to_owned())
        .collect();
    assert_eq!(
        commands,
        [
            "list",
            "check",
            "bisect",
            "ablate",
            "egraph",
            "scaffold",
            "close",
            "inst_graph",
            "ladder",
            "twin",
            "speculate"
        ],
        "{ready}"
    );
    // Each listed request parses: a stale session is refused as a session,
    // not as an unknown request, so the list cannot drift from `Request`.
    for command in &commands {
        let request = match command.as_str() {
            "list" | "close" => json!({"command": command, "session": "stale"}),
            "check" | "egraph" | "ladder" | "speculate" => {
                json!({"command": command, "session": "stale", "bucket": 0, "query": 0})
            }
            "bisect" => {
                json!({"command": command, "session": "stale", "bucket": 0, "query": 0, "mode": "flip"})
            }
            "ablate" => {
                json!({"command": command, "session": "stale", "bucket": 0, "query": 0, "mode": "auto"})
            }
            "inst_graph" => {
                json!({"command": command, "session": "stale", "bucket": 0, "query": 0, "op": "cycles"})
            }
            "twin" => {
                json!({"command": command, "session": "stale", "bucket": 0, "query": 0, "edit": {"bump_rlimit": 2}})
            }
            "scaffold" => {
                json!({"command": command, "session": "stale", "bucket": 0, "query": 0, "assert": "true"})
            }
            _ => panic!("no request for {}", command),
        };
        let reply = worker.send(request);
        assert_eq!(reply["event"], "error", "{command}: {reply}");
        assert_ne!(reply["message"], "invalid resident request", "{command}: {reply}");
    }
    worker.finish(true);
}

const LADDER_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    uninterp spec fn f(i: int) -> int;
    uninterp spec fn p(i: int) -> bool;

    // The goal has no `f` term, so E-matching never instantiates the
    // requirement; a strategy that needs no trigger can.
    proof fn untriggered(a: int)
        requires forall|x: int| #[trigger] f(x) >= 0 && p(x),
    {
        assert(p(a));
    }

    proof fn triggered(a: int)
        requires forall|x: int| #[trigger] f(x) >= 0 && p(x),
    {
        assert(f(a) >= 0);
    }
}
"#;

fn rung<'a>(ladder: &'a Value, name: &str) -> &'a Value {
    ladder["rungs"]
        .as_array()
        .unwrap_or_else(|| panic!("{}", ladder))
        .iter()
        .find(|rung| rung["rung"] == name)
        .unwrap_or_else(|| panic!("no {} rung: {}", name, ladder))
}

#[test]
fn resident_strategy_ladder_finds_a_strategy_and_pins_it() {
    let mut worker =
        Worker::start_with_env(LADDER_SOURCE, &[], &[("VERUS_RESIDENT_STRATEGY_LADDER", "1")]);
    let ready = worker.receive();
    assert_eq!(ready["strategy_ladder"], true, "{ready}");
    let session = ready["session"].clone();
    let untriggered = query_id(&ready, "::untriggered");
    let check = json!({"command":"check", "session":session, "bucket":0, "query":untriggered});
    let before = worker.send(check.clone());
    assert_eq!(before["result"], "invalid", "{before}");
    assert!(before["pinned"].is_null(), "{}", before);

    let ladder = worker
        .send(json!({"command":"ladder", "session":session, "bucket":0, "query":untriggered}));
    assert_eq!(ladder["event"], "laddered", "{ladder}");
    assert_eq!(ladder["available"], json!(["ematch", "conflict", "pool", "enum", "mbqi"]));
    // E-matching alone is the default schedule's own failure.
    assert_eq!(rung(&ladder, "ematch")["verdict"], "unknown", "{ladder}");
    assert_eq!(rung(&ladder, "ematch")["incomplete_id"], "QUANTIFIERS", "{ladder}");
    let solved = ladder["solved_by"].as_str().unwrap_or_else(|| panic!("{}", ladder)).to_owned();
    assert_ne!(solved, "ematch");
    let winner = rung(&ladder, &solved);
    assert_eq!(winner["verdict"], "valid", "{ladder}");
    assert!(winner["instantiations"].as_u64().unwrap() > 0, "{}", ladder);
    assert!(winner["resource_units"].as_u64().unwrap() > 0, "{}", ladder);
    // Rungs after the winner wait for run_all.
    let order = ["ematch", "conflict", "pool", "enum", "mbqi"];
    let after_winner = order.iter().skip_while(|name| **name != solved).skip(1);
    for name in after_winner {
        assert_eq!(rung(&ladder, name)["verdict"], "not_run", "{ladder}");
    }
    assert_eq!(
        ladder["pinned"],
        json!({"rung": solved, "alongside": false, "rlimit": 10.0}),
        "{ladder}"
    );

    // The pinned rung closes the recheck before the full schedule runs.
    let pinned = worker.send(check.clone());
    assert_eq!(pinned["result"], "valid", "{pinned}");
    assert_eq!(pinned["pinned"]["rung"], solved.as_str(), "{pinned}");
    assert_eq!(pinned["pinned"]["alongside"], false, "{pinned}");
    assert_eq!(pinned["pinned"]["closed"], true, "{pinned}");

    // An empty ladder removes the pin, and the default schedule answers as
    // it did at first: no strategy setting outlived its rung.
    let cleared = worker.send(
        json!({"command":"ladder", "session":session, "bucket":0, "query":untriggered, "rungs":[]}),
    );
    assert!(cleared["pinned"].is_null() && cleared["solved_by"].is_null(), "{}", cleared);
    let again = worker.send(check.clone());
    assert_eq!(again["result"], "invalid", "{again}");
    assert!(again["pinned"].is_null(), "{}", again);
    // Nor does an alongside rung's `quant-strategy-alone`: after an alongside
    // ladder that pins nothing, the default schedule still fails.
    let unpinned = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
        "query":untriggered, "alongside":true, "pin":false}));
    assert!(unpinned["solved_by"].is_string() && unpinned["pinned"].is_null(), "{}", unpinned);
    let again = worker.send(check.clone());
    assert_eq!(again["result"], "invalid", "{again}");
    assert!(again["pinned"].is_null(), "{}", again);

    // run_all tries every rung; pin false leaves no pin; budgets apply per rung.
    let all = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
        "query":untriggered, "run_all":true, "pin":false, "budgets":{"enum":5}}));
    assert!(all["rungs"].as_array().unwrap().iter().all(|r| r["verdict"] != "not_run"), "{}", all);
    assert_eq!(rung(&all, "pool")["verdict"], "unknown", "{all}");
    assert_eq!(rung(&all, "enum")["rlimit"], 5.0, "{all}");
    assert!(rung(&all, "enum")["resource_limit"].as_u64().unwrap() > 0, "{}", all);
    assert!(all["pinned"].is_null(), "{}", all);

    // Alongside E-matching the default rungs are the three the schedule
    // lacks; the pin records how its rung ran, and the recheck runs it so.
    let alongside = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
        "query":untriggered, "alongside":true}));
    assert_eq!(alongside["alongside"], true, "{alongside}");
    let names: Vec<&Value> =
        alongside["rungs"].as_array().unwrap().iter().map(|rung| &rung["rung"]).collect();
    assert_eq!(names, [&json!("conflict"), &json!("enum"), &json!("mbqi")], "{alongside}");
    let alongside_solved =
        alongside["solved_by"].as_str().unwrap_or_else(|| panic!("{}", alongside)).to_owned();
    assert_eq!(
        alongside["pinned"],
        json!({"rung": alongside_solved, "alongside": true, "rlimit": 10.0}),
        "{alongside}"
    );
    let rechecked = worker.send(check.clone());
    assert_eq!(rechecked["result"], "valid", "{rechecked}");
    assert_eq!(rechecked["pinned"]["alongside"], true, "{rechecked}");
    assert_eq!(rechecked["pinned"]["closed"], true, "{rechecked}");

    // A query E-matching proves is solved on the first rung.
    let triggered = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
        "query":query_id(&ready, "::triggered")}));
    assert_eq!(triggered["solved_by"], "ematch", "{triggered}");

    // Named alongside, E-matching is the default schedule itself, and runs
    // as a baseline rather than being refused.
    let baseline = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
        "query":untriggered, "alongside":true, "rungs":["ematch"], "pin":false}));
    assert_eq!(rung(&baseline, "ematch")["verdict"], "unknown", "{baseline}");

    for bad in [json!(["enum", "enum"]), json!(["nope"])] {
        let reply = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
            "query":untriggered, "rungs":bad}));
        assert_eq!(reply["event"], "error", "{reply}");
    }
    // Zero, above the cap, and a budget too small for one cvc5 resource unit
    // (which would reach cvc5 as 0, no limit at all) are all refused.
    for budget in [json!(0), json!(1001), json!(0.000001)] {
        let reply = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
            "query":untriggered, "budgets":{"enum":budget}}));
        assert_eq!(reply["event"], "error", "{reply}");
    }
    // The refusals left the pin and the session as they were.
    let rechecked = worker.send(check.clone());
    assert_eq!(rechecked["result"], "valid", "{rechecked}");
    assert_eq!(rechecked["pinned"]["closed"], true, "{rechecked}");
    assert_eq!(worker.send(json!({"command":"close", "session":session}))["event"], "closed");
    worker.finish(false);
}

/// A twin predicts what an edit does under ordinary verification, so it runs
/// the default schedule even for a query a ladder pinned, names the pin it
/// did not follow, and leaves the session's pin working.
#[test]
fn resident_twin_runs_the_default_schedule_for_a_pinned_query() {
    let mut worker =
        Worker::start_with_env(LADDER_SOURCE, &[], &[("VERUS_RESIDENT_STRATEGY_LADDER", "1")]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    let untriggered = query_id(&ready, "::untriggered");
    let twin = |edit: Value| json!({"command":"twin", "session":session, "bucket":0, "query":untriggered, "edit":edit});
    let check = json!({"command":"check", "session":session, "bucket":0, "query":untriggered});

    let reply = worker.send(twin(json!({"bump_rlimit": 20})));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert!(reply["pin_ignored"].is_null(), "{}", reply);

    let ladder = worker
        .send(json!({"command":"ladder", "session":session, "bucket":0, "query":untriggered}));
    let solved = ladder["solved_by"].as_str().unwrap_or_else(|| panic!("{}", ladder)).to_owned();
    let pinned = worker.send(check.clone());
    assert_eq!(pinned["result"], "valid", "{pinned}");

    // check closes on the pin; the twin still predicts plain verification,
    // where more budget does not help, and says which pin it left out.
    let reply = worker.send(twin(json!({"bump_rlimit": 20})));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["pin_ignored"], ladder["pinned"], "{reply}");
    assert_eq!(reply["pin_ignored"]["rung"], solved.as_str(), "{reply}");
    assert_ne!(reply["base"]["class"], "valid", "{reply}");
    assert_ne!(reply["twin"]["class"], "valid", "{reply}");
    assert!(reply["caveat"].as_str().unwrap().contains("pin_ignored"), "{}", reply);

    // An edit the pinned rung could not prove either leaves the session's
    // pin working: the twin never runs the rung.
    let reply = worker.send(twin(json!({"remove_axiom": "hyp_1"})));
    assert_eq!(reply["event"], "twin", "{reply}");
    assert_eq!(reply["edit"]["axioms"][0]["tag"]["kind"], "requires", "{reply}");
    let rechecked = worker.send(check.clone());
    assert_eq!(rechecked["result"], "valid", "{rechecked}");
    assert_eq!(rechecked["pinned"]["closed"], true, "{rechecked}");
    assert_eq!(worker.send(json!({"command":"close", "session":session}))["event"], "closed");
    worker.finish(false);
}

/// Without the ladder mode, Verus's cvc5 has only E-matching and pools: the
/// other rungs are reported, not run.
#[test]
fn resident_ladder_without_the_mode_reports_what_is_missing() {
    let mut worker = Worker::start(LADDER_SOURCE, &[]);
    let ready = worker.receive();
    assert_eq!(ready["strategy_ladder"], false, "{ready}");
    let session = ready["session"].clone();
    let ladder = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
        "query":query_id(&ready, "::untriggered")}));
    assert_eq!(ladder["available"], json!(["ematch", "pool"]), "{ladder}");
    for name in ["conflict", "enum", "mbqi"] {
        assert_eq!(rung(&ladder, name)["verdict"], "unavailable", "{ladder}");
    }
    // The two the solver has still run: E-matching fails as the default
    // schedule does, and pools, which Verus never emits, instantiate nothing.
    assert_eq!(rung(&ladder, "ematch")["verdict"], "unknown", "{ladder}");
    assert_eq!(rung(&ladder, "pool")["verdict"], "unknown", "{ladder}");
    assert_eq!(rung(&ladder, "pool")["instantiations"], 0, "{ladder}");
    assert!(ladder["solved_by"].is_null(), "{}", ladder);
    worker.finish(false);
}

/// A pinned rung's proof decides the verdict, so the reply keeps that check's
/// provenance, as it keeps its instantiation graph; only a pinned attempt
/// that fails has its diagnostics discarded with it.
#[test]
fn resident_pinned_recheck_keeps_the_provenance_of_its_proof() {
    let mut worker = Worker::start_with_env(
        LADDER_SOURCE,
        &["-V", "provenance"],
        &[("VERUS_RESIDENT_STRATEGY_LADDER", "1")],
    );
    let ready = worker.receive();
    assert_eq!(ready["provenance"], true, "{ready}");
    let session = ready["session"].clone();
    let untriggered = query_id(&ready, "::untriggered");
    let ladder = worker
        .send(json!({"command":"ladder", "session":session, "bucket":0, "query":untriggered}));
    assert!(ladder["solved_by"].is_string(), "{}", ladder);
    let checked =
        worker.send(json!({"command":"check", "session":session, "bucket":0, "query":untriggered}));
    assert_eq!(checked["result"], "valid", "{checked}");
    assert_eq!(checked["pinned"]["closed"], true, "{checked}");
    assert_eq!(checked["provenance"]["result"], "valid", "{checked}");
    assert_eq!(checked["provenance"]["round"], 0, "{checked}");
    let requires = checked["provenance"]["hypotheses"]
        .as_array()
        .unwrap_or_else(|| panic!("{}", checked))
        .iter()
        .filter(|h| h["kind"] == "requires")
        .count();
    assert!(requires > 0, "{}", checked);
    worker.finish(false);
}

const UNBOUNDED_SOURCE: &str = r#"
use vstd::prelude::*;
verus! {
    uninterp spec fn f(i: int) -> int;
    uninterp spec fn p(i: int) -> bool;

    // The goal has no `f` term, so E-matching does nothing, but every
    // enumerative instance of the requirement makes a new one.
    #[verifier::rlimit(infinity)]
    proof fn growing(a: int)
        requires forall|x: int| #[trigger] f(x) < f(x + 1),
    {
        assert(p(a));
    }

    #[verifier::rlimit(infinity)]
    proof fn untriggered(a: int)
        requires forall|x: int| #[trigger] f(x) >= 0 && p(x),
    {
        assert(p(a));
    }
}
"#;

/// A query without an rlimit gives its rungs the default one rather than no
/// limit at all, and a pinned attempt runs at the budget that proved it, also
/// after a rung on another query ran out of its budget.
#[test]
fn resident_ladder_bounds_a_query_without_an_rlimit() {
    let mut worker =
        Worker::start_with_env(UNBOUNDED_SOURCE, &[], &[("VERUS_RESIDENT_STRATEGY_LADDER", "1")]);
    let ready = worker.receive();
    let session = ready["session"].clone();
    // Unbounded, enumerative instantiation would never answer this one.
    let growing = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
        "query":query_id(&ready, "::growing"), "rungs":["enum"]}));
    let enumerative = rung(&growing, "enum");
    assert_eq!(enumerative["rlimit"], 10.0, "{growing}");
    assert!(enumerative["resource_limit"].as_u64().unwrap() > 0, "{}", growing);
    assert_ne!(enumerative["verdict"], "valid", "{growing}");
    // A pin found at a budget below the query's is tried at that budget.
    // (Enumerative instantiation alone spends 5 on the prelude; alongside
    // E-matching it proves this in a small part of it.) It follows the rung
    // above, cut off by its budget: a cvc5 before BasisResearch/cvc5#15 sent
    // that rung's unsent instances into the next query, and this ladder then
    // ran out of its budget.
    let untriggered = query_id(&ready, "::untriggered");
    let ladder = worker.send(json!({"command":"ladder", "session":session, "bucket":0,
        "query":untriggered, "rungs":["enum"], "alongside":true, "budgets":{"enum":5}}));
    assert_eq!(
        ladder["pinned"],
        json!({"rung": "enum", "alongside": true, "rlimit": 5.0}),
        "{ladder}"
    );
    let checked =
        worker.send(json!({"command":"check", "session":session, "bucket":0, "query":untriggered}));
    assert_eq!(checked["result"], "valid", "{checked}");
    assert_eq!(checked["pinned"]["rlimit"], 5.0, "{checked}");
    assert_eq!(checked["pinned"]["closed"], true, "{checked}");
    worker.finish(false);
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

/// A session under `-V difficulty` reports, for every check it runs, what
/// cvc5 attributed to each tagged assertion of that query, joined to source:
/// the goal and the hypotheses are listed, the axioms that did no work are
/// counted rather than listed, and a recheck names no focused obligation,
/// since a session never expands an error.
///
/// Needs the pinned cvc5 to answer `(get-info :difficulty-gradient)`
/// (BasisResearch/cvc5#5).
#[test]
fn resident_difficulty_reports_the_gradient_of_a_check() {
    let source = r#"
use vstd::prelude::*;
verus! {
    pub uninterp spec fn enc(k: int) -> int;
    pub uninterp spec fn dec(v: int) -> int;

    #[verifier::external_body]
    pub broadcast proof fn roundtrip(k: int)
        ensures #[trigger] dec(enc(k)) == k,
    {
    }

    proof fn decode_ok(k: int, v: int, bound: int)
        requires
            v == enc(k),
            bound < 100,
        ensures
            dec(v) == k,
    {
        broadcast use roundtrip;
    }
}
"#;
    let mut worker = Worker::start(source, &["-V", "difficulty"]);
    let ready = worker.receive();
    assert_eq!(ready["difficulty"], true, "{}", ready);
    let checked = worker.send(json!({"command":"check", "session":ready["session"], "bucket":0, "query":query_id(&ready, "decode_ok")}));
    assert_eq!(checked["result"], "valid", "{}", checked);
    let report = &checked["difficulty"];
    assert_eq!(report["kind"], "body", "{}", checked);
    assert_eq!(report["round"], 0, "{}", checked);
    assert_eq!(report["result"], "valid", "{}", checked);
    assert_eq!(report["solver_result"], "unsat", "{}", checked);
    assert_eq!(report["difficulty"], true, "{}", checked);
    assert_eq!(report["core"], true, "{}", checked);
    assert!(report["unparsed"].is_null(), "the pinned cvc5 answers the key: {}", checked);
    assert!(report["focus"].is_null(), "a session expands no error: {}", checked);
    let kinds = |row: &serde_json::Value| {
        row["tags"]
            .as_array()
            .unwrap()
            .iter()
            .map(|tag| tag["kind"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>()
    };
    let rows = report["rows"].as_array().unwrap();
    let goal = rows
        .iter()
        .find(|row| kinds(row).iter().any(|kind| kind == "query"))
        .unwrap_or_else(|| panic!("no goal row: {}", checked));
    // the goal is in every refutation's core
    assert_eq!(goal["in_core"], true, "{}", goal);
    // both requires clauses are listed, whatever work they did
    let requires = rows.iter().filter(|row| kinds(row).iter().any(|k| k == "requires")).count();
    assert_eq!(requires, 2, "{}", checked);
    // the axioms that did nothing are counted: most of what is in scope
    assert!(report["idle_axioms"].as_u64().unwrap() > 0, "{}", checked);
    assert_eq!(
        worker.send(json!({"command":"close", "session":ready["session"]}))["event"],
        "closed"
    );
    // every query of the fixture verifies, so the invocation succeeded
    worker.finish(true);
}

/// Without `-V difficulty` a session says the mode is off and its checks
/// carry no gradient, so a caller cannot mistake an absent reply for an empty
/// one.
#[test]
fn resident_without_difficulty_reports_none() {
    let mut worker = Worker::start(SOURCE, &[]);
    let ready = worker.receive();
    assert_eq!(ready["difficulty"], false, "{}", ready);
    let checked = worker.send(json!({"command":"check", "session":ready["session"], "bucket":0, "query":query_id(&ready, "passing")}));
    assert_eq!(checked["result"], "valid", "{}", checked);
    assert!(checked["difficulty"].is_null(), "{}", checked);
    assert_eq!(
        worker.send(json!({"command":"close", "session":ready["session"]}))["event"],
        "closed"
    );
    worker.finish(false);
}
