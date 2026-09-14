//! Static reachability of verified code: the per-crate extraction.
//!
//! Walks the typed HIR of every body in the crate and writes a report with
//! the crate's functions, labeled from VIR (mode, verified, external_body,
//! proxy), and the edges out of every body, each labeled with the context
//! of the reference: compiled code, a contract, or a proof. The reports of
//! all crates are merged and searched by `tools/verus-reach`.

use crate::attributes::get_ghost_block_opt;
use crate::context::Context;
use crate::verus_items::{SpecItem, VerusItem};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{BodyId, Expr, ExprKind};
use rustc_middle::ty::{GenericArgKind, TyCtxt, TypeckResults};
use rustc_session::config::CrateType;
use rustc_span::hygiene::{ExpnKind, MacroKind};
use std::collections::{BTreeSet, HashMap};
use verus_reach::{Edge, EdgeKind, Node, Report, SCHEMA_VERSION, Span};
use vir::ast::{BodyVisibility, Dt, Function, Krate, Mode, Path, TypX};

/// Collects the definitions used by one body: the functions, constructors,
/// and consts it names, the methods it calls, and the local types its
/// expressions have, each with the context it appears in. Closures and
/// consts nested in the body are included.
struct Callees<'a, 'tcx> {
    ctxt: &'a Context<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    /// The context of the expression being visited
    kind: EdgeKind,
    targets: Vec<(DefId, EdgeKind)>,
}

impl<'a, 'tcx> Visitor<'tcx> for Callees<'a, 'tcx> {
    fn visit_nested_body(&mut self, id: BodyId) {
        let tcx = self.ctxt.tcx;
        let outer = std::mem::replace(&mut self.typeck, tcx.typeck(tcx.hir_body_owner_def_id(id)));
        self.visit_body(tcx.hir_body(id));
        self.typeck = outer;
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        // Ghost code nested in compiled code changes the context; ghost
        // code nested in ghost code keeps the outer one
        let outer = self.kind;
        if let (EdgeKind::Call, Some(kind)) = (outer, self.ghost_kind(expr)) {
            self.kind = kind;
        }
        if let ExprKind::Path(qpath) = &expr.kind {
            if let Res::Def(_, def_id) = self.typeck.qpath_res(qpath, expr.hir_id) {
                self.targets.push((def_id, self.kind));
            }
        }
        // Method calls and overloaded operators
        if let Some(def_id) = self.typeck.type_dependent_def_id(expr.hir_id) {
            self.targets.push((def_id, self.kind));
        }
        // A type with an expression of that type counts as used (see
        // `dispatch_edges`), including the types inside it: a `Vec<Item>`
        // handed to serde uses `Item`'s impls
        if let Some(ty) = self.typeck.expr_ty_opt(expr) {
            for arg in ty.walk() {
                let GenericArgKind::Type(t) = arg.kind() else { continue };
                if let Some(adt) = t.peel_refs().ty_adt_def() {
                    if adt.did().is_local() {
                        self.targets.push((adt.did(), self.kind));
                    }
                }
            }
        }
        intravisit::walk_expr(self, expr);
        self.kind = outer;
    }
}

impl<'a, 'tcx> Callees<'a, 'tcx> {
    /// The context an expression opens, if it is ghost code: a spec clause
    /// (`requires`, `ensures`, ...), an assertion, or a ghost block. What is
    /// mentioned there is used by the spec, not called; in particular a
    /// `when_used_as_spec` exec function mentioned there does not run.
    fn ghost_kind(&self, expr: &Expr<'tcx>) -> Option<EdgeKind> {
        match &expr.kind {
            ExprKind::Call(Expr { kind: ExprKind::Path(qpath), hir_id, .. }, _) => {
                let Res::Def(_, def_id) = self.typeck.qpath_res(qpath, *hir_id) else {
                    return None;
                };
                match self.ctxt.verus_items.id_to_name.get(&def_id) {
                    Some(VerusItem::Spec(
                        SpecItem::Requires
                        | SpecItem::Ensures
                        | SpecItem::Recommends
                        | SpecItem::Returns,
                    )) => Some(EdgeKind::Contract),
                    Some(VerusItem::Spec(_) | VerusItem::Assert(_)) => Some(EdgeKind::Proof),
                    _ => None,
                }
            }
            ExprKind::Block(..) => {
                get_ghost_block_opt(self.ctxt.tcx.hir_attrs(expr.hir_id)).map(|_| EdgeKind::Proof)
            }
            _ => None,
        }
    }
}

/// The references of one body. A spec or proof body is ghost code through
/// and through, so everything it names is used, not called.
fn callees<'tcx>(ctxt: &Context<'tcx>, def_id: LocalDefId, mode: Mode) -> Vec<(DefId, EdgeKind)> {
    let tcx = ctxt.tcx;
    let kind = if mode == Mode::Exec { EdgeKind::Call } else { EdgeKind::Proof };
    let mut visitor = Callees { ctxt, typeck: tcx.typeck(def_id), kind, targets: vec![] };
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

/// A function written by the user, and where to report it. Functions a
/// derive or an external macro expands to are not the user's: they still
/// get edges, so what they call counts, but they are not reported. Functions
/// the user's own `macro_rules!` expands to are the user's, reported at the
/// invocation, which is where they are in the source; every function of one
/// invocation shares that span.
fn user_fn_span<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Option<rustc_span::Span> {
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return None;
    }
    let span = tcx.source_span(def_id);
    // The `verus!` macro synthesizes spec accessors for every enum field
    // (`arrow_Variant_field`) with the enum's own span, so they are not
    // from an expansion; but their span is then also the span of the impl
    // that holds them, which a written function's never is.
    let synthesized = tcx.def_kind(tcx.local_parent(def_id)) == DefKind::Impl { of_trait: false }
        && tcx.source_span(tcx.local_parent(def_id)) == span;
    if synthesized {
        return None;
    }
    if !span.from_expansion() {
        return Some(span);
    }
    let expn = span.ctxt().outer_expn_data();
    let local_macro = matches!(expn.kind, ExpnKind::Macro(MacroKind::Bang, _))
        && expn.macro_def_id.map_or(false, |id| id.is_local());
    local_macro.then(|| span.source_callsite())
}

/// The name a `verus!` twin stands for: `VERUS_SPEC__m` holds the spec of
/// the trait method `m`, which the HIR names in calls.
fn spec_twin_target(path: &Path) -> Option<Path> {
    let last = path.last_segment();
    let name = last.strip_prefix(vir::def::VERUS_SPEC)?;
    Some(path.pop_segment().push_segment(std::sync::Arc::new(name.to_string())))
}

/// Helpers `reveal` synthesizes, nested in the revealing body
fn is_reveal_helper(path: &Path) -> bool {
    path.last_segment().ends_with("__VERUS_REVEAL_INTERNAL__")
}

fn is_local_path<'tcx>(ctxt: &Context<'tcx>, path: &Path) -> bool {
    path.krate == crate::rust_to_vir_base::mk_crate_id(ctxt.tcx, LOCAL_CRATE)
}

/// A `verus_builtin` item: spec syntax (`requires`, `assert`, `spec_lt`,
/// ...), not a function anything can reach.
fn is_builtin<'tcx>(ctxt: &Context<'tcx>, def_id: DefId) -> bool {
    matches!(ctxt.verus_items.id_to_name.get(&def_id), Some(item) if !matches!(item, VerusItem::Vstd(..)))
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
    Some(id_of_path(ctxt, &vir_path(ctxt, def_id)?, def_id.is_local()))
}

fn id_of_path<'tcx>(ctxt: &Context<'tcx>, path: &Path, local: bool) -> String {
    let mut krate = vir::def::krate_to_string_ignore_stable_id(&path.krate);
    if local && crate_type(ctxt.tcx) != "lib" {
        krate = format!("{krate}({})", crate_type(ctxt.tcx));
    }
    let segments: Vec<&str> = path.segments.iter().map(|s| s.as_str()).collect();
    format!("{krate}::{}", segments.join("::"))
}

fn span<'tcx>(tcx: TyCtxt<'tcx>, span: rustc_span::Span) -> Span {
    let source_map = tcx.sess.source_map();
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

    /// Spec functions that stand for other items in ghost code, which the
    /// HIR never names: the spec an exec function is read as when
    /// `when_used_as_spec` says so, and the type invariant of a datatype.
    fn implied_edges<'tcx>(&self, ctxt: &Context<'tcx>, krate: &Krate) -> Vec<Edge> {
        let mut edges = vec![];
        for f in krate.functions.iter() {
            // The target of an `assume_specification` may be foreign
            let id = id_of_path(ctxt, &f.x.name.path, is_local_path(ctxt, &f.x.name.path));
            if let Some(proxy) = &f.x.proxy {
                // The contract is written on the proxy; callers name the target
                edges.push(Edge::new(
                    id.clone(),
                    id_of_path(ctxt, &proxy.x, true),
                    EdgeKind::Contract,
                ));
            }
            if let Some(spec) = &f.x.attrs.autospec {
                let local = self.by_name.contains_key(&spec.path);
                edges.push(Edge::new(id, id_of_path(ctxt, &spec.path, local), EdgeKind::Contract));
            } else if f.x.attrs.is_type_invariant_fn {
                let typ = f.x.params.first().map(|p| vir::ast_util::undecorate_typ(&p.x.typ));
                if let Some(TypX::Datatype(Dt::Path(path), ..)) = typ.as_deref() {
                    let local = krate.datatypes.iter().any(|d| d.x.name == Dt::Path(path.clone()));
                    edges.push(Edge::new(id_of_path(ctxt, path, local), id, EdgeKind::Contract));
                }
            }
        }
        edges
    }
}

fn node<'tcx>(
    ctxt: &Context<'tcx>,
    labels: &Labels,
    def_id: LocalDefId,
    id: String,
    at: rustc_span::Span,
) -> Node {
    let tcx = ctxt.tcx;
    let path = vir_path(ctxt, def_id.to_def_id()).expect("path of a named function");
    let (function, mut proxy, mut external_body) = match labels.by_name.get(&path) {
        // The target of an `assume_specification` has a spec but an unchecked body
        Some(f) => (Some(*f), false, f.x.proxy.is_some()),
        None => match labels.by_proxy_path.get(&path) {
            Some(f) => (Some(*f), true, false),
            None => (None, false, false),
        },
    };
    // The twin `verus!` gives a `const fn` for its use in spec code (see
    // `fixup_unerased_proxy_path`) shares the span of the function it
    // stands for and is not code of its own
    proxy |= path.last_segment().starts_with("VERUS_UNERASED_PROXY__");
    // No body to check: `external_body`, or an uninterpreted spec
    external_body |= function.map_or(false, |f| {
        f.x.attrs.is_external_body || matches!(f.x.body_visibility, BodyVisibility::Uninterpreted)
    });
    let module = tcx.parent_module_from_def_id(def_id).to_def_id();
    Node {
        id,
        def_path: vir::ast_util::path_as_friendly_rust_name(&path),
        module: friendly_name(ctxt, module).unwrap_or_default(),
        span: span(tcx, at),
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
    let mut edges: BTreeSet<Edge> = BTreeSet::new();
    for def_id in tcx.hir_body_owners() {
        if !has_own_body(tcx, def_id) {
            continue;
        }
        let Some(path) = vir_path(ctxt, def_id.to_def_id()) else { continue };
        let id = id_of_path(ctxt, &path, true);
        let mode = labels.by_name.get(&path).map_or(Mode::Exec, |f| f.x.mode);
        for (target, kind) in callees(ctxt, def_id, mode) {
            if is_builtin(ctxt, target) {
                continue;
            }
            edges.extend(id_of(ctxt, target).map(|t| Edge::new(id.clone(), t, kind)));
            if let Some(adt) = impl_self_type(tcx, target) {
                edges.extend(id_of(ctxt, adt.to_def_id()).map(|t| Edge::new(id.clone(), t, kind)));
            }
        }
        if let Some(method) = spec_twin_target(&path) {
            // The trait method's contract lives in its twin
            edges.insert(Edge::new(id_of_path(ctxt, &method, true), id, EdgeKind::Contract));
            continue;
        }
        if is_reveal_helper(&path) {
            continue;
        }
        let at = user_fn_span(tcx, def_id)
            .or_else(|| (entry == Some(def_id)).then(|| tcx.source_span(def_id)));
        if let Some(at) = at {
            nodes.push(node(ctxt, &labels, def_id, id, at));
        }
    }
    for (from, to) in dispatch_edges(tcx) {
        if let (Some(from), Some(to)) = (id_of(ctxt, from), id_of(ctxt, to.to_def_id())) {
            edges.insert(Edge::new(from, to, EdgeKind::Call));
        }
    }
    edges.extend(labels.implied_edges(ctxt, krate));
    nodes.sort_by(|a, b| a.id.cmp(&b.id));
    // Nested functions of the same name in one body share an id; keep one
    nodes.dedup_by(|a, b| a.id == b.id);

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
