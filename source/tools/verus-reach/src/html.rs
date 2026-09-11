//! The `--html` report: one self-contained page in the shape of genhtml's
//! output. A table of the files with verified code, and a source view per
//! file with every line tinted by the state of the function it belongs
//! to. The page carries its data as JSON and renders itself; the
//! template is `report.html`.

use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::Path;
use verus_reach::{Graph, Report};

const TEMPLATE: &str = include_str!("report.html");

/// The functions of every file, with the labels the page needs. Sources are
/// read from `src`, the directory the crate was compiled from (paths in the
/// reports are relative to it); a file that is not there gets no source
/// view. Proxies are left out: an `assume_specification` stands for another
/// function's spec and is not code.
pub fn data(reports: &[Report], graph: &Graph, src: &Path, title: &str) -> Value {
    let mut files: BTreeMap<&str, Vec<Value>> = BTreeMap::new();
    for n in graph.nodes.values().filter(|n| !n.proxy) {
        files.entry(&n.span.file).or_default().push(json!({
            "name": n.name(),
            "path": n.def_path,
            "mode": n.mode,
            "start": n.span.start_line,
            "end": n.span.end_line,
            "verified": n.is_verified(),
            "reachable": graph.is_reachable(n),
        }));
    }
    let files: Vec<Value> = files
        .into_iter()
        .map(|(path, functions)| {
            let source = std::fs::read_to_string(src.join(path)).ok();
            json!({ "path": path, "functions": functions, "source": source })
        })
        .collect();
    let crates: Vec<String> =
        reports.iter().map(|r| format!("{} ({})", r.krate, r.crate_type)).collect();
    let roots: Vec<&str> = graph.roots.iter().map(|id| graph.nodes[id].def_path.as_str()).collect();
    json!({
        "title": title,
        "crates": crates,
        "roots": roots,
        "src_root": src.display().to_string(),
        "files": files,
    })
}

pub fn render(reports: &[Report], graph: &Graph, src: &Path, title: &str) -> String {
    let data = data(reports, graph, src, title).to_string();
    // The JSON sits in a <script> element, which only `</` can end early
    let data = data.replace("</", "<\\/");
    let title = title.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;");
    TEMPLATE.replace("__TITLE__", &title).replace("__DATA__", &data)
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

    #[test]
    fn data_labels_every_function_of_a_file() {
        let (reports, graph) = graph();
        let dir = tempfile::tempdir().unwrap();
        let data = data(&reports, &graph, dir.path(), "t");
        let files = data["files"].as_array().unwrap();
        assert_eq!(files.len(), 1);
        assert_eq!(files[0]["path"], "x.rs");
        assert_eq!(files[0]["source"], Value::Null);
        let fns = files[0]["functions"].as_array().unwrap();
        assert_eq!(fns.len(), 8);
        let by_name = |name: &str| fns.iter().find(|f| f["name"] == name).unwrap();
        assert_eq!(by_name("wired")["verified"], true);
        assert_eq!(by_name("wired")["reachable"], true);
        assert_eq!(by_name("inc")["verified"], false);
        assert_eq!(by_name("inc")["reachable"], true);
        assert_eq!(by_name("spec_inc")["mode"], "spec");
        assert_eq!(by_name("spec_inc")["reachable"], false);
        assert_eq!(fns.iter().filter(|f| f["verified"] == true).count(), 6);
        assert_eq!(fns.iter().filter(|f| f["reachable"] == true).count(), 6);
        assert_eq!(data["roots"], json!(["app(bin)::main"]));
    }

    #[test]
    fn data_reads_sources_from_the_src_root() {
        let (reports, graph) = graph();
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("x.rs"), "fn a() {}\n").unwrap();
        let data = data(&reports, &graph, dir.path(), "t");
        assert_eq!(data["files"][0]["source"], "fn a() {}\n");
    }

    #[test]
    fn render_keeps_the_script_element_intact() {
        let mut n = node("lib::evil", true, true);
        n.def_path = "lib::a</script><b>".into();
        let lib = report("lib", "lib", None, vec![n], vec![]);
        let graph = Graph::new(&[lib.clone()], &Roots::default()).unwrap();
        let dir = tempfile::tempdir().unwrap();
        let text = render(&[lib], &graph, dir.path(), "a <b> & c");
        assert!(text.contains("<title>a &lt;b&gt; &amp; c</title>"), "{text}");
        assert!(!text.contains("</script><b>"), "{text}");
        assert!(text.contains("<\\/script><b>"), "{text}");
    }
}
