//! The `--html` report: a directory of pages in the shape of genhtml's
//! output. `index.html` tables the files with verified code; `src/<path>.html`
//! shows one file's functions and its source with every line tinted by the
//! state of the function it belongs to. Each page carries only its own
//! data, so a large crate does not load into the browser all at once. The
//! pages render themselves from `report.html`.

use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use verus_reach::{Graph, Node, Report};

const TEMPLATE: &str = include_str!("report.html");

/// Functions that are not code the user wrote: an `assume_specification`
/// proxy, the twin `const fn` gets for its spec use (`VERUS_UNERASED_PROXY__`,
/// labeled `proxy` by newer reports and by name for older ones), and the
/// helpers `reveal` synthesizes.
fn synthesized(n: &Node) -> bool {
    n.proxy
        || n.name().starts_with("VERUS_UNERASED_PROXY__")
        || n.name().ends_with("__VERUS_REVEAL_INTERNAL__")
}

fn function(n: &Node, graph: &Graph) -> Value {
    json!({
        "name": n.name(),
        "path": n.def_path,
        "mode": n.mode,
        "start": n.span.start_line,
        "end": n.span.end_line,
        "verified": n.is_verified(),
        "reachable": graph.is_reachable(n),
    })
}

/// Where a file's page goes, under the output directory
fn page_path(file: &str) -> PathBuf {
    let mut p = PathBuf::from("src");
    for part in Path::new(file).components() {
        if let std::path::Component::Normal(part) = part {
            p.push(part);
        }
    }
    p.set_extension(format!(
        "{}.html",
        p.extension().map_or(String::new(), |e| e.to_string_lossy().into_owned())
    ));
    p
}

/// The functions of every file, by file, with the labels the pages need
pub fn files<'a>(graph: &'a Graph) -> BTreeMap<&'a str, Vec<&'a Node>> {
    let mut files: BTreeMap<&str, Vec<&Node>> = BTreeMap::new();
    for n in graph.nodes.values().filter(|n| !synthesized(n)) {
        files.entry(&n.span.file).or_default().push(n);
    }
    files
}

fn page(data: Value, title: &str) -> String {
    // The JSON sits in a <script> element, which only `</` can end early
    let data = data.to_string().replace("</", "<\\/");
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
    src: &Path,
    title: &str,
    out: &Path,
) -> Result<(), String> {
    let files = files(graph);
    let crates: Vec<String> =
        reports.iter().map(|r| format!("{} ({})", r.krate, r.crate_type)).collect();
    let roots: Vec<&str> = graph.roots.iter().map(|id| graph.nodes[id].def_path.as_str()).collect();
    let common = json!({
        "title": title,
        "crates": crates,
        "roots": roots,
        "src_root": src.display().to_string(),
        "file_count": files.len(),
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
        let functions: Vec<Value> = nodes.iter().map(|n| function(n, graph)).collect();
        let rel = page_path(file);
        index_files
            .push(json!({ "path": file, "href": rel.to_string_lossy(), "functions": functions }));
        if !nodes.iter().any(|n| n.is_verified()) {
            continue;
        }
        let source = std::fs::read_to_string(src.join(file)).ok();
        let up = vec![".."; rel.components().count() - 1].join("/");
        let data = with(json!({
            "page": "file",
            "up": up,
            "file": { "path": file, "href": "", "functions": functions, "source": source },
            "total": total(&files, graph),
        }));
        write(&rel, page(data, &format!("{file} · {title}")))?;
    }
    let data = with(json!({ "page": "index", "files": index_files }));
    write(Path::new("index.html"), page(data, title))
}

/// The run's totals, the one denominator every page shows
fn total(files: &BTreeMap<&str, Vec<&Node>>, graph: &Graph) -> Value {
    let all: Vec<&Node> = files.values().flatten().copied().collect();
    let fns = all.len();
    let verified = all.iter().filter(|n| n.is_verified()).count();
    let reach = all.iter().filter(|n| graph.is_reachable(n)).count();
    let vreach = all.iter().filter(|n| n.is_verified() && graph.is_reachable(n)).count();
    let mode = |m: &str| {
        let of = all.iter().filter(|n| n.is_verified() && n.mode == m);
        json!([of.clone().filter(|n| graph.is_reachable(n)).count(), of.count()])
    };
    let pct = |a: usize, b: usize| (b > 0).then(|| (100 * a / b) as u64);
    json!({
        "fns": fns, "verified": verified, "reach": reach, "vreach": vreach,
        "exec": mode("exec"), "spec": mode("spec"), "proof": mode("proof"),
        "dead": pct(verified - vreach, verified), "share": pct(vreach, reach), "all": pct(vreach, fns),
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
        serde_json::from_str(&text[start..end].replace("<\\/", "</")).unwrap()
    }

    #[test]
    fn index_lists_every_file_and_pages_the_verified_ones() {
        let (mut reports, graph) = graph();
        // The binary's main is in a file of its own with nothing verified
        reports[1].nodes[0].span.file = "src/main.rs".into();
        let graph2 = Graph::new(&reports, &Roots::default()).unwrap();
        let _ = graph;
        let src = tempfile::tempdir().unwrap();
        std::fs::write(src.path().join("x.rs"), "fn a() {}\n").unwrap();
        let out = tempfile::tempdir().unwrap();
        write(&reports, &graph2, src.path(), "t", out.path()).unwrap();

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
        assert_eq!(x["total"]["verified"], 6);
        assert_eq!(x["total"]["vreach"], 4);
        assert_eq!(x["total"]["reach"], 6);
        assert_eq!(x["total"]["fns"], 8);
        assert_eq!(x["total"]["dead"], 33);
        assert_eq!(x["total"]["share"], 66);
        assert_eq!(x["total"]["proof"], json!([1, 1]));
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
        let names: Vec<&str> = files(&graph)["x.rs"].iter().map(|n| n.name()).collect();
        assert_eq!(names, vec!["is_lt"]);
    }

    #[test]
    fn page_keeps_the_script_element_intact() {
        let text = page(json!({ "name": "a</script><b>" }), "a <b> & c");
        assert!(text.contains("<title>a &lt;b&gt; &amp; c</title>"), "{text}");
        assert!(!text.contains("</script><b>"), "{text}");
        assert!(text.contains("<\\/script><b>"), "{text}");
    }
}
