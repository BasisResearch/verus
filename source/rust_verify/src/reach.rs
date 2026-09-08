//! Static reachability of verified code: the per-crate extraction.
//!
//! Walks the typed HIR of every body in the crate and writes a report with
//! the crate's functions, labeled from VIR (mode, verified, external_body,
//! proxy), and the call edges out of every body. The reports of all crates
//! are merged and searched by `tools/verus-reach`.

use crate::attributes::{GhostBlockAttr, get_ghost_block_opt};
use crate::context::Context;
use crate::verus_items::VerusItem;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{CRATE_DEF_ID, DefId, LOCAL_CRATE, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{BodyId, Expr, ExprKind};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use std::collections::{BTreeSet, HashMap};
use verus_reach::{Node, Report, SCHEMA_VERSION, Span};
use vir::ast::{Function, Krate, Mode, Path};

/// Collects the definitions referenced by one body, including the bodies of
/// closures and inline consts nested in it.
struct Callees<'a, 'tcx> {
    ctxt: &'a Context<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    targets: Vec<DefId>,
}

impl<'a, 'tcx> Visitor<'tcx> for Callees<'a, 'tcx> {
    fn visit_nested_body(&mut self, id: BodyId) {
        let tcx = self.ctxt.tcx;
        let outer = std::mem::replace(&mut self.typeck, tcx.typeck(tcx.hir_body_owner_def_id(id)));
        self.visit_body(tcx.hir_body(id));
        self.typeck = outer;
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if self.is_ghost(expr) {
            return;
        }
        match &expr.kind {
            ExprKind::Path(qpath) => self.visit_res(self.typeck.qpath_res(qpath, expr.hir_id)),
            ExprKind::Struct(qpath, ..) => {
                self.visit_res(self.typeck.qpath_res(qpath, expr.hir_id))
            }
            _ => {}
        }
        // Method calls and overloaded operators
        if let Some(def_id) = self.typeck.type_dependent_def_id(expr.hir_id) {
            self.targets.push(def_id);
        }
        intravisit::walk_expr(self, expr);
    }
}

impl<'a, 'tcx> Callees<'a, 'tcx> {
    fn visit_res(&mut self, res: Res) {
        if let Res::Def(_, def_id) = res {
            self.targets.push(def_id);
        }
    }

    /// Spec clauses (`requires`, `ensures`, ...) and proof blocks. Skipped so
    /// that a `when_used_as_spec` exec function mentioned in a spec does not
    /// count as called.
    fn is_ghost(&self, expr: &Expr<'tcx>) -> bool {
        let tcx = self.ctxt.tcx;
        match &expr.kind {
            ExprKind::Call(Expr { kind: ExprKind::Path(qpath), hir_id, .. }, _) => {
                match self.typeck.qpath_res(qpath, *hir_id) {
                    Res::Def(_, def_id) => matches!(
                        self.ctxt.verus_items.id_to_name.get(&def_id),
                        Some(VerusItem::Spec(_))
                    ),
                    _ => false,
                }
            }
            ExprKind::Block(..) => {
                get_ghost_block_opt(tcx.hir_attrs(expr.hir_id)) == Some(GhostBlockAttr::Proof)
            }
            _ => false,
        }
    }
}

fn callees<'tcx>(ctxt: &Context<'tcx>, def_id: LocalDefId) -> Vec<DefId> {
    let tcx = ctxt.tcx;
    let mut visitor = Callees { ctxt, typeck: tcx.typeck(def_id), targets: vec![] };
    visitor.visit_body(tcx.hir_body_owned_by(def_id));
    visitor.targets
}

fn self_type<'tcx>(tcx: TyCtxt<'tcx>, impl_def: LocalDefId) -> Option<LocalDefId> {
    let ty = tcx.type_of(impl_def).skip_binder().peel_refs();
    ty.ty_adt_def().and_then(|adt| adt.did().as_local())
}

/// The local type a definition belongs to: a constructor, variant, or
/// method of an impl on that type.
fn type_of_def<'tcx>(tcx: TyCtxt<'tcx>, mut def_id: DefId) -> Option<LocalDefId> {
    loop {
        match tcx.def_kind(def_id) {
            DefKind::Ctor(..) | DefKind::Variant => def_id = tcx.parent(def_id),
            DefKind::Struct | DefKind::Enum | DefKind::Union => return def_id.as_local(),
            DefKind::AssocFn | DefKind::AssocConst { .. } => {
                let parent = tcx.parent(def_id).as_local()?;
                return match tcx.def_kind(parent) {
                    DefKind::Impl { .. } => self_type(tcx, parent),
                    _ => None,
                };
            }
            _ => return None,
        }
    }
}

/// Edges that stand in for dispatch we cannot see. A call to a trait method
/// may run any local impl of it. Upstream code (serde, `format!`, sorting,
/// ...) may call any trait impl of a local type once the type is used.
fn dispatch_edges<'tcx>(ctxt: &Context<'tcx>) -> Vec<(DefId, LocalDefId)> {
    let tcx = ctxt.tcx;
    let mut edges = vec![];
    for impl_item in tcx.hir_crate_items(()).impl_items() {
        let def_id = impl_item.owner_id.def_id;
        if let Some(trait_item) = tcx.associated_item(def_id).trait_item_def_id() {
            edges.push((trait_item, def_id));
            if let Some(adt) = self_type(tcx, tcx.local_parent(def_id)) {
                edges.push((adt.to_def_id(), def_id));
            }
        }
    }
    edges
}

/// A function written by the user (not generated by a macro).
fn is_user_fn<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> bool {
    matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
        && !tcx.source_span(def_id).from_expansion()
}

fn has_own_body<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> bool {
    matches!(
        tcx.def_kind(def_id),
        DefKind::Fn
            | DefKind::AssocFn
            | DefKind::Const { .. }
            | DefKind::AssocConst { .. }
            | DefKind::Static { .. }
    )
}

fn vir_path<'tcx>(ctxt: &Context<'tcx>, def_id: DefId) -> Option<Path> {
    crate::rust_to_vir_base::def_id_to_vir_path_option(ctxt.tcx, Some(&ctxt.verus_items), def_id)
}

/// Canonical name, the same from every crate that refers to the item.
fn id_of<'tcx>(ctxt: &Context<'tcx>, def_id: DefId) -> Option<String> {
    let path = vir_path(ctxt, def_id)?;
    let krate = vir::def::krate_to_string_ignore_stable_id(&path.krate);
    let segments: Vec<&str> = path.segments.iter().map(|s| s.as_str()).collect();
    Some(format!("{krate}::{}", segments.join("::")))
}

fn span<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Span {
    let source_map = tcx.sess.source_map();
    let span = tcx.source_span(def_id);
    let lo = source_map.lookup_char_pos(span.lo());
    let hi = source_map.lookup_char_pos(span.hi());
    let file = source_map.filename_for_diagnostics(&lo.file.name).to_string();
    Span { file, start_line: lo.line, end_line: hi.line }
}

/// Labels come from VIR: a function is verified iff Verus built a VIR function for it.
struct Labels<'a> {
    by_name: HashMap<&'a Path, &'a Function>,
    by_proxy: HashMap<&'a Path, &'a Function>,
}

impl<'a> Labels<'a> {
    fn new(krate: &'a Krate) -> Labels<'a> {
        let functions = krate.functions.iter();
        Labels {
            by_name: functions.clone().map(|f| (&f.x.name.path, f)).collect(),
            by_proxy: functions.filter_map(|f| f.x.proxy.as_ref().map(|p| (&p.x, f))).collect(),
        }
    }
}

fn node<'tcx>(ctxt: &Context<'tcx>, labels: &Labels, def_id: LocalDefId, id: String) -> Node {
    let tcx = ctxt.tcx;
    let path = vir_path(ctxt, def_id.to_def_id()).expect("path of a named function");
    let (function, proxy) = match (labels.by_name.get(&path), labels.by_proxy.get(&path)) {
        (Some(f), _) => (Some(*f), false),
        (None, Some(f)) => (Some(*f), true),
        (None, None) => (None, false),
    };
    let mode = function.map(|f| f.x.mode).unwrap_or(Mode::Exec);
    // The target of an `assume_specification` has a spec but an unchecked body
    let external_body =
        function.map_or(false, |f| f.x.attrs.is_external_body || (!proxy && f.x.proxy.is_some()));
    Node {
        id,
        def_path: vir::ast_util::path_as_friendly_rust_name(&path),
        span: span(tcx, def_id),
        mode: format!("{mode}"),
        verified: function.is_some(),
        external_body,
        proxy,
        exported: tcx.effective_visibilities(()).is_exported(def_id),
    }
}

/// Writes this crate's report to the `--reach` directory.
pub(crate) fn run<'tcx>(ctxt: &Context<'tcx>, krate: &Krate) -> Result<(), String> {
    let tcx = ctxt.tcx;
    let labels = Labels::new(krate);

    let mut nodes = vec![];
    let mut edges: BTreeSet<(String, String)> = BTreeSet::new();
    let mut main = None;
    for def_id in tcx.hir_body_owners() {
        if !has_own_body(tcx, def_id) {
            continue;
        }
        let Some(id) = id_of(ctxt, def_id.to_def_id()) else { continue };
        for target in callees(ctxt, def_id) {
            edges.extend(id_of(ctxt, target).map(|t| (id.clone(), t)));
            if let Some(adt) = type_of_def(tcx, target) {
                edges.extend(id_of(ctxt, adt.to_def_id()).map(|t| (id.clone(), t)));
            }
        }
        if is_user_fn(tcx, def_id) {
            if tcx.local_parent(def_id) == CRATE_DEF_ID
                && tcx.item_name(def_id.to_def_id()).as_str() == "main"
            {
                main = Some(id.clone());
            }
            nodes.push(node(ctxt, &labels, def_id, id));
        }
    }
    for (from, to) in dispatch_edges(ctxt) {
        if let (Some(from), Some(to)) = (id_of(ctxt, from), id_of(ctxt, to.to_def_id())) {
            edges.insert((from, to));
        }
    }
    nodes.sort_by(|a, b| a.id.cmp(&b.id));

    let crate_type = if tcx.sess.opts.test {
        "test"
    } else if tcx.crate_types().contains(&rustc_session::config::CrateType::Executable) {
        "bin"
    } else {
        "lib"
    };
    let report = Report {
        schema_version: SCHEMA_VERSION,
        krate: tcx.crate_name(LOCAL_CRATE).to_string(),
        crate_type: crate_type.to_string(),
        main,
        nodes,
        edges: edges.into_iter().collect(),
    };

    let dir = std::path::Path::new(ctxt.cmd_line_args.reach.as_ref().expect("--reach"));
    let path = dir.join(report.file_name());
    let json = serde_json::to_string_pretty(&report).expect("serialize reach report");
    std::fs::create_dir_all(dir)
        .and_then(|()| std::fs::write(&path, json))
        .map_err(|e| format!("could not write {}: {e}", path.display()))
}
