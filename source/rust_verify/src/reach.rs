//! Static reachability of verified code: the per-crate extraction.
//!
//! Walks the typed HIR of every body in the crate and writes a report with
//! the crate's functions, labeled from VIR (mode, verified, external_body,
//! proxy), and the call edges out of every body. The reports of all crates
//! are merged and searched by `tools/verus-reach`.

use crate::attributes::get_ghost_block_opt;
use crate::context::Context;
use crate::verus_items::VerusItem;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{BodyId, Expr, ExprKind};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_session::config::CrateType;
use std::collections::{BTreeSet, HashMap};
use verus_reach::{Node, Report, SCHEMA_VERSION, Span};
use vir::ast::{Function, Krate, Mode, Path};

/// Collects the definitions used by one body: the functions, constructors,
/// and consts it names, the methods it calls, and the local types its
/// expressions have. Closures and consts nested in the body are included.
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
        if let ExprKind::Path(qpath) = &expr.kind {
            if let Res::Def(_, def_id) = self.typeck.qpath_res(qpath, expr.hir_id) {
                self.targets.push(def_id);
            }
        }
        // Method calls and overloaded operators
        if let Some(def_id) = self.typeck.type_dependent_def_id(expr.hir_id) {
            self.targets.push(def_id);
        }
        // A type with an expression of that type counts as used (see `dispatch_edges`)
        if let Some(adt) = self.typeck.expr_ty_opt(expr).and_then(|ty| ty.peel_refs().ty_adt_def())
        {
            if adt.did().is_local() {
                self.targets.push(adt.did());
            }
        }
        intravisit::walk_expr(self, expr);
    }
}

impl<'a, 'tcx> Callees<'a, 'tcx> {
    /// Spec clauses (`requires`, `ensures`, ...), assertions, and ghost
    /// blocks. Skipped so that a `when_used_as_spec` exec function mentioned
    /// there does not count as called.
    fn is_ghost(&self, expr: &Expr<'tcx>) -> bool {
        match &expr.kind {
            ExprKind::Call(Expr { kind: ExprKind::Path(qpath), hir_id, .. }, _) => {
                match self.typeck.qpath_res(qpath, *hir_id) {
                    Res::Def(_, def_id) => matches!(
                        self.ctxt.verus_items.id_to_name.get(&def_id),
                        Some(VerusItem::Spec(_) | VerusItem::Assert(_))
                    ),
                    _ => false,
                }
            }
            ExprKind::Block(..) => {
                get_ghost_block_opt(self.ctxt.tcx.hir_attrs(expr.hir_id)).is_some()
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

/// The local type an associated function or const belongs to.
fn impl_self_type<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<LocalDefId> {
    if !matches!(tcx.def_kind(def_id), DefKind::AssocFn | DefKind::AssocConst { .. }) {
        return None;
    }
    let parent = tcx.parent(def_id).as_local()?;
    match tcx.def_kind(parent) {
        DefKind::Impl { .. } => self_type(tcx, parent),
        _ => None,
    }
}

/// Edges that stand in for dispatch we cannot see. A call to a trait method
/// may run any local impl of it. Upstream code (serde, `format!`, sorting,
/// ...) may call any trait impl of a local type once the type is used.
fn dispatch_edges<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<(DefId, LocalDefId)> {
    let mut edges = vec![];
    for impl_item in tcx.hir_crate_items(()).impl_items() {
        let def_id = impl_item.owner_id.def_id;
        if tcx.def_kind(def_id) != DefKind::AssocFn {
            continue;
        }
        if let Some(trait_item) = tcx.associated_item(def_id).trait_item_def_id() {
            edges.push((trait_item, def_id));
            if let Some(adt) = self_type(tcx, tcx.local_parent(def_id)) {
                edges.push((adt.to_def_id(), def_id));
            }
        }
    }
    edges
}

/// Bodies that are graph nodes of their own. Closures and anonymous consts
/// are visited as part of the body that contains them.
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

/// A function written by the user. Macro-generated functions still get
/// edges, so what they call counts, but they are not reported themselves.
fn is_user_fn<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> bool {
    matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
        && !tcx.source_span(def_id).from_expansion()
}

fn vir_path<'tcx>(ctxt: &Context<'tcx>, def_id: DefId) -> Option<Path> {
    crate::rust_to_vir_base::def_id_to_vir_path_option(ctxt.tcx, Some(&ctxt.verus_items), def_id)
}

fn friendly_name<'tcx>(ctxt: &Context<'tcx>, def_id: DefId) -> Option<String> {
    vir_path(ctxt, def_id).map(|p| vir::ast_util::path_as_friendly_rust_name(&p))
}

fn crate_type<'tcx>(tcx: TyCtxt<'tcx>) -> &'static str {
    if tcx.sess.opts.test {
        "test"
    } else if tcx.crate_types().contains(&CrateType::Executable) {
        "bin"
    } else {
        "lib"
    }
}

/// Canonical name, the same from every crate that refers to the item. The
/// items of an executable are tagged with its crate type, since a package's
/// binary shares its name with the library.
fn id_of<'tcx>(ctxt: &Context<'tcx>, def_id: DefId) -> Option<String> {
    let path = vir_path(ctxt, def_id)?;
    let mut krate = vir::def::krate_to_string_ignore_stable_id(&path.krate);
    if def_id.is_local() && crate_type(ctxt.tcx) != "lib" {
        krate = format!("{krate}({})", crate_type(ctxt.tcx));
    }
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

/// The VIR functions of the crate. Verus builds one for every function it
/// checks; whether the check passed is the exit status of the verus run,
/// not part of the report.
struct Labels<'a> {
    by_name: HashMap<&'a Path, &'a Function>,
    /// Keyed by the path of an `assume_specification` proxy. The function it
    /// maps to is named after the target of the specification.
    by_proxy_path: HashMap<&'a Path, &'a Function>,
}

impl<'a> Labels<'a> {
    fn new(krate: &'a Krate) -> Labels<'a> {
        let functions = krate.functions.iter();
        Labels {
            by_name: functions.clone().map(|f| (&f.x.name.path, f)).collect(),
            by_proxy_path: functions
                .filter_map(|f| f.x.proxy.as_ref().map(|p| (&p.x, f)))
                .collect(),
        }
    }
}

fn node<'tcx>(ctxt: &Context<'tcx>, labels: &Labels, def_id: LocalDefId, id: String) -> Node {
    let tcx = ctxt.tcx;
    let path = vir_path(ctxt, def_id.to_def_id()).expect("path of a named function");
    let (function, proxy, mut external_body) = match labels.by_name.get(&path) {
        // The target of an `assume_specification` has a spec but an unchecked body
        Some(f) => (Some(*f), false, f.x.proxy.is_some()),
        None => match labels.by_proxy_path.get(&path) {
            Some(f) => (Some(*f), true, false),
            None => (None, false, false),
        },
    };
    external_body |= function.map_or(false, |f| f.x.attrs.is_external_body);
    let module = tcx.parent_module_from_def_id(def_id).to_def_id();
    Node {
        id,
        def_path: vir::ast_util::path_as_friendly_rust_name(&path),
        module: friendly_name(ctxt, module).unwrap_or_default(),
        span: span(tcx, def_id),
        mode: format!("{}", function.map(|f| f.x.mode).unwrap_or(Mode::Exec)),
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
    let entry = tcx.entry_fn(()).and_then(|(def_id, _)| def_id.as_local());

    let mut nodes = vec![];
    let mut edges: BTreeSet<(String, String)> = BTreeSet::new();
    for def_id in tcx.hir_body_owners() {
        if !has_own_body(tcx, def_id) {
            continue;
        }
        let Some(id) = id_of(ctxt, def_id.to_def_id()) else { continue };
        for target in callees(ctxt, def_id) {
            edges.extend(id_of(ctxt, target).map(|t| (id.clone(), t)));
            if let Some(adt) = impl_self_type(tcx, target) {
                edges.extend(id_of(ctxt, adt.to_def_id()).map(|t| (id.clone(), t)));
            }
        }
        if is_user_fn(tcx, def_id) || entry == Some(def_id) {
            nodes.push(node(ctxt, &labels, def_id, id));
        }
    }
    for (from, to) in dispatch_edges(tcx) {
        if let (Some(from), Some(to)) = (id_of(ctxt, from), id_of(ctxt, to.to_def_id())) {
            edges.insert((from, to));
        }
    }
    nodes.sort_by(|a, b| a.id.cmp(&b.id));

    let report = Report {
        schema_version: SCHEMA_VERSION,
        krate: tcx.crate_name(LOCAL_CRATE).to_string(),
        crate_type: crate_type(tcx).to_string(),
        main: entry.and_then(|def_id| id_of(ctxt, def_id.to_def_id())),
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
