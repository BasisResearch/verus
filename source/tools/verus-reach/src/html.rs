//! The `--html` report: a directory of pages in the shape of genhtml's
//! output. `index.html` tables the files with verified code; `src/<path>.html`
//! shows one file's functions and its source with every line tinted by the
//! state of the function it belongs to. Each page carries only its own
//! data, so a large crate does not load into the browser all at once. The
//! pages render themselves from `report.html`.

use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use verus_reach::dyncov::Dynamic;
use verus_reach::{Graph, Node, Report};

/// How a function's reachability is judged: statically, or, with the
/// profiles of a `verus --dyncov` run, dynamically for verified exec code
/// (in T: called, precondition never false, never tainted) and statically
/// through any copy of the function for everything else.
pub struct View<'a> {
    pub graph: &'a Graph,
    pub dynamic: Option<&'a Dynamic>,
}

impl<'a> View<'a> {
    fn reachable(&self, n: &Node) -> bool {
        match self.dynamic {
            Some(d) if n.is_verified_exec() => d.true_reachable.contains(&n.id),
            Some(d) => d.static_reachable(self.graph, n),
            None => self.graph.is_reachable_any(n),
        }
    }

    /// The nodes counted once (a crate's test build duplicates its functions)
    fn nodes(&self) -> Vec<&'a Node> {
        match self.dynamic {
            Some(d) => d.nodes(self.graph).collect(),
            None => self.graph.counted().collect(),
        }
    }
}

const TEMPLATE: &str = include_str!("report.html");

fn function(n: &Node, view: &View) -> Value {
    let mut f = json!({
        "name": n.name(),
        "path": n.def_path,
        "mode": n.mode,
        "start": n.span.start_line,
        "end": n.span.end_line,
        "verified": n.is_verified(),
        "trusted": n.is_trusted(),
        "reachable": view.reachable(n),
    });
    if let Some(d) = view.dynamic {
        if n.is_verified_exec() {
            let p = d.profiled.get(&n.id);
            let mut why = if d.static_reachable(view.graph, n) {
                "statically reachable".to_string()
            } else {
                "statically unreachable".to_string()
            };
            match p {
                Some(p) => {
                    why.push_str(&format!(", called {} time(s)", p.calls));
                    if p.pre.iter().sum::<u64>() > 0 {
                        why.push_str(&format!(
                            ", precondition true {} / unknown {} / false {}",
                            p.pre[0], p.pre[1], p.pre[2]
                        ));
                    }
                }
                None => why.push_str(", never called"),
            }
            if let Some(ex) = d.excluded.get(&n.id) {
                if ex.tainted > 0 {
                    why.push_str(&format!(", tainted {} time(s)", ex.tainted));
                }
            }
            f["dynamic"] = json!(why);
        }
    }
    f
}

/// Where a file's page goes, under the output directory: the file's path
/// with `.html` appended, `..` and the root spelled out so that distinct
/// paths get distinct pages.
fn page_path(file: &str) -> PathBuf {
    use std::path::Component::*;
    let mut p = PathBuf::from("src");
    for part in Path::new(file).components() {
        match part {
            Normal(part) => p.push(part),
            ParentDir => p.push("__up__"),
            RootDir | Prefix(_) => p.push("__root__"),
            CurDir => {}
        }
    }
    let name = p.file_name().map_or("_".to_string(), |n| n.to_string_lossy().into_owned());
    p.set_file_name(format!("{name}.html"));
    p
}

/// A page's link from `index.html`: the components of its path joined with
/// `/` whatever the OS, each percent-encoded, so `#` and `?` in a file name
/// stay in the path
fn page_href(rel: &Path) -> String {
    let parts: Vec<String> = rel
        .components()
        .map(|c| c.as_os_str().to_string_lossy().bytes().map(encode_byte).collect())
        .collect();
    parts.join("/")
}

fn encode_byte(b: u8) -> String {
    match b {
        b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' => (b as char).into(),
        _ => format!("%{b:02X}"),
    }
}

/// The functions of every file, by file, with the labels the pages need.
/// The graph already leaves out the items nobody wrote.
pub fn files<'a>(view: &View<'a>) -> BTreeMap<&'a str, Vec<&'a Node>> {
    let mut files: BTreeMap<&str, Vec<&Node>> = BTreeMap::new();
    for n in view.nodes() {
        files.entry(&n.span.file).or_default().push(n);
    }
    files
}

fn page(data: Value, title: &str) -> String {
    // The JSON sits in a <script> element, where `</script>` ends it early
    // and `<!--<script` starts a run the next `</script>` does not end; a
    // `<` only ever sits inside a JSON string, where its escape is legal
    let data = data.to_string().replace('<', "\\u003c");
    let title = title.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;");
    TEMPLATE.replace("__TITLE__", &title).replace("__DATA__", &data)
}

/// Writes `index.html` and a page per file with verified code into `out`.
/// Sources are read from `src`, the directory the crates were compiled from
/// (paths in the reports are relative to it); a file that is not there gets
/// no source view.
pub fn write(
    reports: &[Report],
    graph: &Graph,
    dynamic: Option<&Dynamic>,
    src: &Path,
    title: &str,
    out: &Path,
) -> Result<(), String> {
    let view = View { graph, dynamic };
    let files = files(&view);
    let crates: Vec<String> = reports.iter().map(|r| r.label()).collect();
    let common = json!({
        "title": title,
        "crates": crates,
        "roots": graph.root_names(),
        "src_root": src.display().to_string(),
        "file_count": files.len(),
        "dynamic": dynamic.is_some(),
    });
    let with = |mut extra: Value| {
        for (k, v) in common.as_object().unwrap() {
            extra[k] = v.clone();
        }
        extra
    };
    let write = |rel: &Path, text: String| -> Result<(), String> {
        let path = out.join(rel);
        if let Some(dir) = path.parent() {
            std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        }
        std::fs::write(&path, text).map_err(|e| format!("{}: {e}", path.display()))
    };

    let mut index_files = vec![];
    for (file, nodes) in &files {
        let functions: Vec<Value> = nodes.iter().map(|n| function(n, &view)).collect();
        let rel = page_path(file);
        index_files.push(json!({ "path": file, "href": page_href(&rel), "functions": functions }));
        if !nodes.iter().any(|n| n.is_verified()) {
            continue;
        }
        let source = std::fs::read_to_string(src.join(file)).ok();
        let up = vec![".."; rel.components().count() - 1].join("/");
        let data = with(json!({
            "page": "file",
            "up": up,
            "file": { "path": file, "href": "", "functions": functions, "source": source },
            "totals": { "all": total(&files, &view, |_| true), "exec": total(&files, &view, |n| n.mode == "exec") },
        }));
        write(&rel, page(data, &format!("{file} · {title}")))?;
    }
    let data = with(json!({ "page": "index", "files": index_files }));
    write(Path::new("index.html"), page(data, title))
}

/// The run's totals over the functions `scope` selects, the one
/// denominator every page shows
fn total(files: &BTreeMap<&str, Vec<&Node>>, view: &View, scope: fn(&Node) -> bool) -> Value {
    let all: Vec<&Node> = files.values().flatten().copied().filter(|n| scope(n)).collect();
    let fns = all.len();
    let verified = all.iter().filter(|n| n.is_verified()).count();
    let reach = all.iter().filter(|n| view.reachable(n)).count();
    let vreach = all.iter().filter(|n| n.is_verified() && view.reachable(n)).count();
    let mode = |m: &str| {
        let of = all.iter().filter(|n| n.is_verified() && n.mode == m);
        json!([of.clone().filter(|n| view.reachable(n)).count(), of.count()])
    };
    let pct = |a: usize, b: usize| (b > 0).then(|| (100 * a / b) as u64);
    json!({
        "fns": fns, "verified": verified, "reach": reach, "vreach": vreach,
        "exec": mode("exec"), "spec": mode("spec"), "proof": mode("proof"),
        "dead": pct(verified - vreach, verified), "share": pct(vreach, reach),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use verus_reach::Roots;
    use verus_reach::fixture::{lib_and_bin, node, report};

    fn graph() -> (Vec<Report>, Graph) {
        let reports = lib_and_bin();
        let graph = Graph::new(&reports, &Roots::default()).unwrap();
        (reports, graph)
    }

    fn data(text: &str) -> Value {
        let start = text.find("application/json\">").unwrap() + "application/json\">".len();
        let end = text[start..].find("</script>").unwrap() + start;
        serde_json::from_str(&text[start..end]).unwrap()
    }

    #[test]
    fn index_lists_every_file_and_pages_the_verified_ones() {
        let (mut reports, _) = graph();
        // The binary's main is in a file of its own with nothing verified
        reports[1].nodes[0].span.file = "src/main.rs".into();
        let graph2 = Graph::new(&reports, &Roots::default()).unwrap();
        let src = tempfile::tempdir().unwrap();
        std::fs::write(src.path().join("x.rs"), "fn a() {}\n").unwrap();
        let out = tempfile::tempdir().unwrap();
        write(&reports, &graph2, None, src.path(), "t", out.path()).unwrap();

        let index = data(&std::fs::read_to_string(out.path().join("index.html")).unwrap());
        assert_eq!(index["page"], "index");
        assert_eq!(index["file_count"], 2);
        let files = index["files"].as_array().unwrap();
        assert_eq!(files.len(), 2);
        assert_eq!(files[0]["path"], "src/main.rs");
        assert_eq!(files[0]["href"], "src/src/main.rs.html");
        assert_eq!(files[1]["path"], "x.rs");
        assert_eq!(files[1]["href"], "src/x.rs.html");
        assert_eq!(files[1]["functions"].as_array().unwrap().len(), 7);
        assert!(files[1].get("source").is_none());

        let x = data(&std::fs::read_to_string(out.path().join("src/x.rs.html")).unwrap());
        assert_eq!(x["page"], "file");
        assert_eq!(x["up"], "..");
        assert_eq!(x["file"]["source"], "fn a() {}\n");
        let fns = x["file"]["functions"].as_array().unwrap();
        let by_name = |name: &str| fns.iter().find(|f| f["name"] == name).unwrap();
        assert_eq!(by_name("wired")["reachable"], true);
        assert_eq!(by_name("spec_inc")["reachable"], false);
        // 6 verified, 4 reachable; main and inc reachable but unverified
        let all = &x["totals"]["all"];
        assert_eq!(all["verified"], 6);
        assert_eq!(all["vreach"], 4);
        assert_eq!(all["reach"], 6);
        assert_eq!(all["fns"], 8);
        assert_eq!(all["dead"], 33);
        assert_eq!(all["share"], 66);
        assert_eq!(all["proof"], json!([1, 1]));
        // Exec only: wired, helper, verified::inc verified; inc and main not
        let exec = &x["totals"]["exec"];
        assert_eq!(exec["fns"], 5);
        assert_eq!(exec["verified"], 3);
        assert_eq!(exec["vreach"], 2);
        assert_eq!(exec["reach"], 4);
        assert_eq!(exec["dead"], 33);
        assert_eq!(exec["share"], 50);
        assert_eq!(exec["proof"], json!([0, 0]));
        assert!(!out.path().join("src/src/main.rs.html").exists());
    }

    #[test]
    fn synthesized_twins_are_left_out() {
        let mut twin = node("lib::VERUS_UNERASED_PROXY__is_lt", false, false);
        twin.def_path = "lib::VERUS_UNERASED_PROXY__is_lt".into();
        let mut reveal = node("lib::lemma::__VERUS_REVEAL_INTERNAL__", false, false);
        reveal.def_path = "lib::lemma::__VERUS_REVEAL_INTERNAL__".into();
        let mut proxy = node("lib::ext", true, false);
        proxy.proxy = true;
        let lib = report(
            "lib",
            "lib",
            None,
            vec![node("lib::is_lt", true, true), twin, reveal, proxy],
            vec![],
        );
        let graph = Graph::new(&[lib], &Roots::default()).unwrap();
        let view = View { graph: &graph, dynamic: None };
        let names: Vec<&str> = files(&view)["x.rs"].iter().map(|n| n.name()).collect();
        assert_eq!(names, vec!["is_lt"]);
    }

    #[test]
    fn distinct_paths_get_distinct_pages() {
        let pages: Vec<String> = ["src/a.rs", "../a.rs", "/abs/a.rs", "a", "./a.rs"]
            .iter()
            .map(|f| page_href(&page_path(f)))
            .collect();
        assert_eq!(
            pages,
            vec![
                "src/src/a.rs.html",
                "src/__up__/a.rs.html",
                "src/__root__/abs/a.rs.html",
                "src/a.html",
                "src/a.rs.html"
            ]
        );
    }

    #[test]
    fn links_are_urls_whatever_the_file_name() {
        assert_eq!(page_href(&page_path("src/a#1?.rs")), "src/src/a%231%3F.rs.html");
        assert_eq!(page_href(&page_path("my dir/ü.rs")), "src/my%20dir/%C3%BC.rs.html");
        assert_eq!(page_href(&page_path("src/a.rs")), "src/src/a.rs.html");
    }

    #[test]
    fn dynamic_view_counts_only_true_verified_reachable_exec() {
        // wired is statically reachable and called with its pre true;
        // helper is reachable but never called; ghost reachability is static
        let (reports, graph) = graph();
        let mut profile = verus_reach::dyncov::Profile { schema_version: 2, ..Default::default() };
        profile.functions.insert(
            "x.rs:1:wired".into(),
            verus_reach::dyncov::FnProfile { calls: 2, pre: [2, 0, 0], ..Default::default() },
        );
        let dynamic = Dynamic::new(&graph, &profile);
        let view = View { graph: &graph, dynamic: Some(&dynamic) };
        let by = |name: &str| graph.nodes.values().find(|n| n.name() == name).unwrap();
        assert!(view.reachable(by("wired")));
        assert!(!view.reachable(by("helper")));
        assert!(view.reachable(by("spec_wired")));
        let f = function(by("wired"), &view);
        assert_eq!(f["reachable"], true);
        assert!(f["dynamic"].as_str().unwrap().contains("called 2 time(s), precondition true 2"));
        let src = tempfile::tempdir().unwrap();
        let out = tempfile::tempdir().unwrap();
        write(&reports, &graph, Some(&dynamic), src.path(), "t", out.path()).unwrap();
        let index = data(&std::fs::read_to_string(out.path().join("index.html")).unwrap());
        assert_eq!(index["dynamic"], true);
    }

    #[test]
    fn page_keeps_the_script_element_intact() {
        let text = page(json!({ "name": "a</script><b>", "src": "<!--<script>" }), "a <b> & c");
        assert!(text.contains("<title>a &lt;b&gt; &amp; c</title>"), "{text}");
        assert!(!text.contains("</script><b>"), "{text}");
        assert!(!text.contains("<!--"), "{text}");
        assert!(text.contains("\\u003c/script>\\u003cb>"), "{text}");
        assert_eq!(data(&text)["name"], "a</script><b>");
        assert_eq!(data(&text)["src"], "<!--<script>");
    }
}
