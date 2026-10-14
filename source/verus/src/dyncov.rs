//! `--dyncov` builds: the `verus!` macro lowers contracts and spec functions
//! to exec code with an engine that works on syntax, so some of what it
//! generates does not type-check (a contract over a type the engine does not
//! know how to compare, a spec function of vstd without an exec twin). The
//! instrumented build must still succeed, with those pieces recorded as
//! `Unknown` rather than evaluated. This module runs `rust_verify` with
//! JSON diagnostics, collects the locations of the errors, and reruns it
//! with `VERUS_DYNCOV_DISABLE` naming them; the macro gives every clause or
//! twin whose source span contains one of those locations its `Unknown`
//! form. Only the last attempt's output is shown.

use std::io::{Read, Write};
use std::process::{Command, Stdio};

const MAX_ATTEMPTS: usize = 8;

/// A diagnostic's primary location, as the macro matches it: the file as
/// rustc names it, and the line.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Location {
    file: String,
    line: u64,
}

/// Runs `cmd` (rust_verify with the user's `args`) until the instrumented
/// crate compiles or nothing new can be disabled; returns the exit code.
pub fn run_with_retries(cmd: &mut Command, args: &[String]) -> i32 {
    // Under cargo, rustc already emits JSON that cargo renders; standalone,
    // ask for it and render it ourselves
    let cargo_json = args.iter().any(|a| a.starts_with("--error-format=json"));
    if !cargo_json {
        cmd.arg("--error-format=json");
    }
    let mut disabled: Vec<Location> =
        std::env::var("VERUS_DYNCOV_DISABLE").ok().map(|v| parse_locations(&v)).unwrap_or_default();
    let mut attempt = 0;
    loop {
        attempt += 1;
        if !disabled.is_empty() {
            cmd.env("VERUS_DYNCOV_DISABLE", format_locations(&disabled));
        }
        cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
        let mut child = match cmd.spawn() {
            Ok(c) => c,
            Err(e) => {
                eprintln!("error: failed to execute rust_verify {e:?}");
                return 128;
            }
        };
        let mut out = child.stdout.take().expect("stdout");
        let mut err = child.stderr.take().expect("stderr");
        let out_thread = std::thread::spawn(move || {
            let mut buf = Vec::new();
            let _ = out.read_to_end(&mut buf);
            buf
        });
        let mut stderr = Vec::new();
        let _ = err.read_to_end(&mut stderr);
        let status = child.wait().expect("wait for rust_verify");
        let stdout = out_thread.join().unwrap_or_default();
        let code = status.code().unwrap_or(1);

        let errors = error_messages(&stderr);
        let new: Vec<(Location, String)> =
            errors.into_iter().filter(|(l, _)| !disabled.contains(l)).collect();
        let retry = code != 0 && !new.is_empty() && attempt < MAX_ATTEMPTS;
        if retry {
            eprintln!(
                "verus --dyncov: attempt {attempt}: {} error location(s) in lowered code, retrying with them disabled:",
                new.len()
            );
            // Say what went wrong at each location (one line each, the
            // full diagnostics with VERUS_DYNCOV_DEBUG), since this attempt's
            // output is otherwise discarded
            for (l, msg) in &new {
                eprintln!("verus --dyncov:   {}:{}: {msg}", l.file, l.line);
            }
            if std::env::var("VERUS_DYNCOV_DEBUG").is_ok_and(|v| !v.is_empty()) {
                render(&stderr);
            }
            let new: Vec<Location> = new.into_iter().map(|(l, _)| l).collect();
            disabled.extend(new);
            disabled.sort();
            disabled.dedup();
            continue;
        }
        std::io::stdout().write_all(&stdout).ok();
        if cargo_json {
            std::io::stderr().write_all(&stderr).ok();
        } else {
            render(&stderr);
        }
        if !disabled.is_empty() && code == 0 {
            eprintln!(
                "verus --dyncov: {} clause(s) or spec function(s) whose lowering did not compile are recorded as unknown (VERUS_DYNCOV_DISABLE={})",
                disabled.len(),
                format_locations(&disabled)
            );
        }
        return code;
    }
}

fn parse_locations(s: &str) -> Vec<Location> {
    s.split(',')
        .filter_map(|e| {
            let (file, line) = e.rsplit_once(':')?;
            Some(Location { file: file.to_string(), line: line.parse().ok()? })
        })
        .collect()
}

fn format_locations(locs: &[Location]) -> String {
    locs.iter().map(|l| format!("{}:{}", l.file, l.line)).collect::<Vec<_>>().join(",")
}

/// The primary locations of the error diagnostics in rustc's JSON output,
/// each with the first message reported there.
fn error_messages(stderr: &[u8]) -> Vec<(Location, String)> {
    let mut locs: Vec<(Location, String)> = Vec::new();
    for line in String::from_utf8_lossy(stderr).lines() {
        let Some(d) = parse_json_line(line) else { continue };
        // Only rustc's own errors come from lowered code that does not
        // type-check; a verification failure is not something to disable
        if d.level != "error" || !d.coded {
            continue;
        }
        for l in d.primary {
            if !locs.iter().any(|(k, _)| *k == l) {
                locs.push((l, d.message.clone()));
            }
        }
    }
    locs.sort();
    locs
}

struct Diag {
    level: String,
    /// Has an error code: a rustc error, as opposed to a verification
    /// failure reported by Verus
    coded: bool,
    message: String,
    rendered: Option<String>,
    primary: Vec<Location>,
}

/// A minimal reading of a rustc JSON diagnostic (no JSON library here): the
/// level, whether it carries an error code (rustc's own errors do, Verus's
/// verification failures do not), the rendered text, and the primary spans'
/// file and line, from the diagnostic's own `spans` only (not its children's,
/// and not the macro-expansion sites nested in them).
fn parse_json_line(line: &str) -> Option<Diag> {
    if !line.starts_with('{') || !line.contains("\"$message_type\":\"diagnostic\"") {
        return None;
    }
    let level = find_string(line, "\"level\":\"")?;
    let message = find_string(line, "\"message\":\"").map(unescape).unwrap_or_default();
    let rendered = find_string(line, "\"rendered\":\"").map(unescape);
    let coded = line.find("\"code\":").map_or(false, |i| line[i + 7..].starts_with('{'));
    let mut primary = Vec::new();
    if let Some(spans) = top_level_array(line, "\"spans\":") {
        for obj in top_level_objects(spans) {
            // The span's own fields come before its nested `expansion`
            let own = &obj[..obj.find("\"expansion\":").unwrap_or(obj.len())];
            if own.contains("\"is_primary\":true") {
                if let (Some(file), Some(l)) =
                    (find_string(own, "\"file_name\":\""), find_number(own, "\"line_start\":"))
                {
                    primary.push(Location { file: unescape(file), line: l });
                }
            }
        }
    }
    Some(Diag { level, message, coded, rendered, primary })
}

/// The text inside the brackets of `key:[...]`, where `key` is a field of
/// the outermost object (the first occurrence outside any nested value).
fn top_level_array<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let bytes = line.as_bytes();
    let (mut depth, mut in_str, mut esc) = (0i32, false, false);
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if in_str {
            if esc {
                esc = false;
            } else if c == b'\\' {
                esc = true;
            } else if c == b'"' {
                in_str = false;
            }
        } else {
            match c {
                b'"' => {
                    if depth == 1 && line[i..].starts_with(key) {
                        let start = i + key.len();
                        if bytes.get(start) == Some(&b'[') {
                            let end = matching_close(line, start)?;
                            return Some(&line[start + 1..end]);
                        }
                    }
                    in_str = true;
                }
                b'{' | b'[' => depth += 1,
                b'}' | b']' => depth -= 1,
                _ => {}
            }
        }
        i += 1;
    }
    None
}

/// The index of the bracket closing the one at `open`.
fn matching_close(s: &str, open: usize) -> Option<usize> {
    let bytes = s.as_bytes();
    let (mut depth, mut in_str, mut esc) = (0i32, false, false);
    for (i, &c) in bytes.iter().enumerate().skip(open) {
        if in_str {
            if esc {
                esc = false;
            } else if c == b'\\' {
                esc = true;
            } else if c == b'"' {
                in_str = false;
            }
            continue;
        }
        match c {
            b'"' => in_str = true,
            b'{' | b'[' => depth += 1,
            b'}' | b']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// The objects of a JSON array's text, each as its own text.
fn top_level_objects(array: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(rel) = array[i..].find('{') {
        let open = i + rel;
        let Some(close) = matching_close(array, open) else { break };
        out.push(&array[open..=close]);
        i = close + 1;
    }
    out
}

fn find_string(s: &str, key: &str) -> Option<String> {
    let i = s.find(key)? + key.len();
    let bytes = s.as_bytes();
    let mut j = i;
    while j < bytes.len() {
        match bytes[j] {
            b'\\' => j += 2,
            b'"' => return Some(s[i..j].to_string()),
            _ => j += 1,
        }
    }
    None
}

fn find_number(s: &str, key: &str) -> Option<u64> {
    let i = s.find(key)? + key.len();
    let digits: String = s[i..].chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse().ok()
}

fn unescape(s: String) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some('r') => out.push('\r'),
            Some('"') => out.push('"'),
            Some('\\') => out.push('\\'),
            Some('/') => out.push('/'),
            Some('u') => {
                let hex: String = chars.by_ref().take(4).collect();
                if let Some(ch) = u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32) {
                    out.push(ch);
                }
            }
            Some(other) => {
                out.push('\\');
                out.push(other);
            }
            None => out.push('\\'),
        }
    }
    out
}

/// Prints rustc's JSON diagnostics as rustc would have; anything else
/// verbatim.
fn render(stderr: &[u8]) {
    let mut err = std::io::stderr();
    for line in String::from_utf8_lossy(stderr).lines() {
        match parse_json_line(line) {
            Some(Diag { rendered: Some(r), .. }) => {
                let _ = err.write_all(r.as_bytes());
            }
            Some(_) => {}
            None => {
                let _ = writeln!(err, "{line}");
            }
        }
    }
}
