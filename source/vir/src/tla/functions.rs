//! The only boundary through which the exporter can obtain a function body.
//!
//! Declarations and generated instances are private to this module. Consumers
//! request a call (with all compiler type arguments) or an explicit declaration
//! root. A resolved handle carries both the printable function and its canonical
//! instance identity; type-independent emission does not erase semantic identity.
use super::*;
use std::cell::RefCell;

pub(super) enum FunctionUse<'a> {
    Call(&'a CallTargetKind, &'a Fun, &'a Typs),
    /// A selected declaration, intentionally abstract in its own parameters,
    /// or a previously resolved/synthetic operator. Never use for a call edge.
    Root(&'a Fun),
}

#[derive(Clone)]
pub(super) struct ResolvedFunction {
    function: Function,
    original: Fun,
    arguments: Typs,
}

impl std::ops::Deref for ResolvedFunction {
    type Target = Function;
    fn deref(&self) -> &Function {
        &self.function
    }
}

impl ResolvedFunction {
    pub(super) fn name(&self) -> &Fun {
        &self.function.x.name
    }
    pub(super) fn original(&self) -> &Fun {
        &self.original
    }
    pub(super) fn same_instance(&self, other: &Self) -> bool {
        self.original == other.original
            && crate::ast_util::n_types_equal(&self.arguments, &other.arguments)
    }
}

#[derive(Clone)]
pub(super) struct Functions(RefCell<Registry>);

impl Functions {
    pub(super) fn new(krate: &Krate) -> Self {
        Self(RefCell::new(Registry {
            functions: krate.functions.iter().map(|f| (f.x.name.clone(), f.clone())).collect(),
            instances: Vec::new(),
            assoc_types: krate.assoc_type_impls.clone(),
            trait_impls: krate.trait_impls.clone(),
            trait_arities: krate
                .traits
                .iter()
                .map(|t| (t.x.name.clone(), t.x.typ_params.len() + 1))
                .collect(),
            trait_methods: krate
                .functions
                .iter()
                .filter_map(|f| match &f.x.kind {
                    FunctionKind::TraitMethodImpl { impl_path, method, .. } => {
                        Some(((impl_path.clone(), method.clone()), f.x.name.clone()))
                    }
                    _ => None,
                })
                .collect(),
        }))
    }

    /// Mandatory entry point for calls AND declaration/closure/operator roots.
    /// No raw map lookup or body access is exposed to the exporter.
    pub(super) fn resolve(&self, use_: FunctionUse<'_>) -> Result<ResolvedFunction, String> {
        let mut registry = self.0.borrow_mut();
        let (name, original, arguments) = match use_ {
            FunctionUse::Call(kind, fun, typs) => registry.instantiate(kind, fun, typs)?,
            FunctionUse::Root(fun) => {
                if let Some((base, args, _)) = registry.instances.iter().find(|(_, _, f)| f == fun)
                {
                    (fun.clone(), base.clone(), args.clone())
                } else {
                    let f = registry.functions.get(fun).ok_or("function unavailable")?;
                    let args = Arc::new(
                        f.x.typ_params
                            .iter()
                            .map(|p| Arc::new(TypX::TypParam(p.clone())))
                            .collect(),
                    );
                    (fun.clone(), fun.clone(), args)
                }
            }
        };
        let function = registry.functions.get(&name).cloned().ok_or("function unavailable")?;
        Ok(ResolvedFunction { function, original, arguments })
    }

    /// Equality is conservative on resolution failure, including ambiguous impls.
    pub(super) fn same_call(&self, a: &Expr, b: &Expr) -> bool {
        let resolve = |e: &Expr| match &e.x {
            ExprX::Call { target: CallTarget::Fun(kind, fun, typs, ..), .. } => {
                self.resolve(FunctionUse::Call(kind, fun, typs)).ok()
            }
            _ => None,
        };
        match (resolve(a), resolve(b)) {
            (Some(a), Some(b)) => a.same_instance(&b),
            _ => false,
        }
    }

    pub(super) fn normalize_type(&self, typ: &Typ) -> Typ {
        self.0.borrow().normalize_type(typ)
    }
    pub(super) fn names(&self) -> Vec<Fun> {
        self.0.borrow().functions.keys().cloned().collect()
    }
    pub(super) fn synthetic(
        &self,
        of: &ResolvedFunction,
        params: Vec<Param>,
        body: Option<Expr>,
        ret: &Typ,
    ) -> Fun {
        self.0.borrow_mut().synthetic(of, params, body, ret)
    }
}

/// Name-only classification of compiler-known primitives, never body access.
pub(super) fn compiler_target(kind: &CallTargetKind, fun: &Fun) -> Fun {
    match kind {
        CallTargetKind::DynamicResolved { resolved, .. } => resolved.clone(),
        _ => fun.clone(),
    }
}

#[derive(Clone)]
struct Registry {
    functions: HashMap<Fun, Function>,
    instances: Vec<(Fun, Typs, Fun)>,
    assoc_types: Vec<AssocTypeImpl>,
    trait_impls: Vec<TraitImpl>,
    trait_methods: HashMap<(Path, Fun), Fun>,
    trait_arities: HashMap<Path, usize>,
}

impl Registry {
    /// Match an impl's type pattern against an already checked call. Never
    /// select by method name or receiver alone: every trait argument matters.
    fn match_impl_type(pattern: &Typ, actual: &Typ, subst: &mut HashMap<Ident, Typ>) -> bool {
        match (&**pattern, &**actual) {
            (TypX::TypParam(p), _) => match subst.get(p) {
                Some(t) => crate::ast_util::types_equal(t, actual),
                None => {
                    subst.insert(p.clone(), actual.clone());
                    true
                }
            },
            (TypX::Datatype(p, ps, _), TypX::Datatype(a, ts, _))
                if p == a && ps.len() == ts.len() =>
            {
                ps.iter().zip(ts.iter()).all(|(p, a)| Self::match_impl_type(p, a, subst))
            }
            (TypX::Decorate(pd, pa, p), TypX::Decorate(ad, aa, a)) if pd == ad => {
                let allocator = match (pa, aa) {
                    (None, None) => true,
                    (Some(p), Some(a)) => {
                        Self::match_impl_type(&p.allocator_typ, &a.allocator_typ, subst)
                    }
                    _ => false,
                };
                allocator && Self::match_impl_type(p, a, subst)
            }
            (TypX::Boxed(p), TypX::Boxed(a)) => Self::match_impl_type(p, a, subst),
            _ => crate::ast_util::types_equal(pattern, actual),
        }
    }

    /// Select only when the complete impl inventory has one matching pattern.
    /// Bounds can make overlapping patterns disjoint, but this exporter does
    /// not solve Rust obligations. Keep all such candidates and refuse rather
    /// than guessing which bounds hold. Count impls even if their method or
    /// associated-type definition is unavailable in VIR.
    fn unique_impl(
        &self,
        trait_path: &Path,
        args: &[Typ],
    ) -> Result<(TraitImpl, HashMap<Ident, Typ>), String> {
        if args.iter().any(|t| {
            crate::ast_visitor::typ_visitor_check(t, &mut |t| match &**t {
                TypX::TypParam(_) | TypX::Projection { .. } => Err(()),
                _ => Ok(()),
            })
            .is_err()
        }) {
            return Err("unresolved trait type arguments".into());
        }
        let mut matches = self.trait_impls.iter().filter_map(|i| {
            if i.x.trait_path != *trait_path || i.x.trait_typ_args.len() != args.len() {
                return None;
            }
            let mut subst = HashMap::new();
            i.x.trait_typ_args
                .iter()
                .zip(args)
                .all(|(p, a)| Self::match_impl_type(p, a, &mut subst))
                .then(|| (i.clone(), subst))
        });
        match (matches.next(), matches.next()) {
            (Some(only), None) => Ok(only),
            (None, _) => Err("no matching concrete trait implementation".into()),
            _ => Err("ambiguous concrete trait implementation (impl bounds not resolved)".into()),
        }
    }

    fn normalize_type(&self, typ: &Typ) -> Typ {
        self.normalize_type_at(typ, &mut Vec::new())
    }

    fn normalize_type_at(&self, typ: &Typ, seen: &mut Vec<Typ>) -> Typ {
        // Leave a cyclic or excessively deep projection unresolved. Concrete
        // dispatch then refuses it; it must never select an arbitrary impl.
        if seen.len() >= 64 || seen.iter().any(|t| crate::ast_util::types_equal(t, typ)) {
            return typ.clone();
        }
        seen.push(typ.clone());
        let normalized = crate::ast_visitor::map_typ_visitor_env(typ, seen, &|seen, t| {
            if let TypX::Projection { trait_typ_args, trait_path, name } = &**t {
                if let Ok((implementation, subst)) = self.unique_impl(trait_path, trait_typ_args) {
                    if let Some(a) = self
                        .assoc_types
                        .iter()
                        .find(|a| a.x.impl_path == implementation.x.impl_path && a.x.name == *name)
                    {
                        let replacement = crate::sst_util::subst_typ(&subst, &a.x.typ);
                        return Ok(self.normalize_type_at(&replacement, seen));
                    }
                }
            }
            Ok(t.clone())
        })
        .expect("associated type normalization");
        seen.pop();
        normalized
    }

    /// Preserve existing polymorphic operators when no dispatch or opaque
    /// function depends on their type arguments.
    fn needs_instance(&self, fun: &Fun, seen: &mut HashSet<Fun>) -> bool {
        if !seen.insert(fun.clone()) {
            return false;
        }
        let Some(f) = self.functions.get(fun) else { return false };
        let Some(body) = &f.x.body else { return true };
        crate::ast_visitor::expr_visitor_check(body, &mut |_, e| {
            if let ExprX::Call { target: CallTarget::Fun(kind, callee, ..), .. } = &e.x {
                if vstd_op(&fun_as_friendly_rust_name(callee)).is_some() {
                    return Ok(());
                }
                if matches!(kind, CallTargetKind::Dynamic)
                    || self.needs_instance(&compiler_target(kind, callee), seen)
                {
                    return Err(());
                }
            }
            Ok(())
        })
        .is_err()
    }

    /// Specialize before rendering: type arguments on calls inside a generic
    /// body must be substituted too, including associated type projections.
    fn instantiate(
        &mut self,
        kind: &CallTargetKind,
        fun: &Fun,
        typs: &Typs,
    ) -> Result<(Fun, Fun, Typs), String> {
        let resolved = compiler_target(kind, fun);
        let ts = match kind {
            CallTargetKind::DynamicResolved { typs, .. } if resolved != *fun => typs,
            _ => typs,
        };
        let mut ts: Typs = Arc::new(ts.iter().map(|t| self.normalize_type(t)).collect());
        if vstd_op(&fun_as_friendly_rust_name(&resolved)).is_some() {
            return Ok((resolved.clone(), resolved, ts));
        }
        let mut target = resolved;
        if matches!(kind, CallTargetKind::Dynamic) {
            let declaration = self.functions.get(fun).ok_or("trait declaration unavailable")?;
            let FunctionKind::TraitMethodDecl { trait_path, .. } = &declaration.x.kind else {
                return Err("trait declaration unavailable".into());
            };
            // Only Self and the trait arguments select the impl. A method's
            // own type parameters can remain abstract after that selection.
            let trait_arity =
                *self.trait_arities.get(trait_path).ok_or("trait type parameters unavailable")?;
            let trait_args = ts.get(..trait_arity).ok_or("incomplete trait type arguments")?;
            if trait_args.iter().any(typ_mentions_param) {
                if declaration.x.body.is_some() {
                    return Err("unresolved abstract trait dispatch with a default body".into());
                }
                // A genuinely abstract trait declaration remains a reported table.
            } else {
                let (implementation, mut subst) = self.unique_impl(trait_path, trait_args)?;
                // Synthetic specializations retain FunctionKind. Look up the
                // original declaration, never a previously specialized body.
                let method = self
                    .trait_methods
                    .get(&(implementation.x.impl_path.clone(), fun.clone()))
                    .ok_or("selected trait method unavailable")?;
                let f = self.functions.get(method).ok_or("selected trait method unavailable")?;
                if let FunctionKind::TraitMethodImpl { inherit_body_from: Some(default), .. } =
                    &f.x.kind
                {
                    target = default.clone();
                } else {
                    let method_args = &ts[trait_arity..];
                    let method_params =
                        f.x.typ_params
                            .get(implementation.x.typ_params.len()..)
                            .ok_or("incomplete impl type parameters")?;
                    if method_args.len() != method_params.len() {
                        return Err("incomplete method type arguments".into());
                    }
                    subst.extend(method_params.iter().cloned().zip(method_args.iter().cloned()));
                    let args: Option<Vec<_>> =
                        f.x.typ_params.iter().map(|p| subst.get(p).cloned()).collect();
                    ts = Arc::new(args.ok_or("incomplete concrete impl substitution")?);
                    target = f.x.name.clone();
                }
            }
        }
        let Some(f) = self.functions.get(&target).cloned() else {
            return Ok((target.clone(), target, ts));
        };
        if f.x.typ_params.is_empty() || !self.needs_instance(&target, &mut HashSet::new()) {
            return Ok((target.clone(), target, ts));
        }
        if f.x.typ_params.len() != ts.len() {
            return Err("incomplete function type arguments".into());
        }
        if let Some((_, _, instance)) = self
            .instances
            .iter()
            .find(|(base, args, _)| base == &target && crate::ast_util::n_types_equal(args, &ts))
        {
            return Ok((instance.clone(), target, ts));
        }
        let subst: HashMap<Ident, Typ> =
            f.x.typ_params.iter().cloned().zip(ts.iter().cloned()).collect();
        let specialized = crate::ast_visitor::map_function_visitor_env(
            &f,
            &mut crate::ast_visitor::VisitorScopeMap::new(),
            &mut (),
            &|_, _, e| Ok(e.clone()),
            &|_, _, s| Ok(vec![s.clone()]),
            &|_, t| {
                let t = crate::sst_util::subst_typ(&subst, t);
                Ok(self.normalize_type(&t))
            },
            &|_, _, p| Ok(p.clone()),
        )
        .expect("function type substitution");
        let instance = self.synthetic(
            &specialized,
            specialized.x.params.as_ref().clone(),
            specialized.x.body.clone(),
            &specialized.x.ret.x.typ,
        );
        // synthetic is also used for wrappers, which drop preconditions. An
        // instantiation preserves the complete contract instead.
        let mut x = specialized.x.clone();
        x.name = instance.clone();
        x.typ_params = Arc::new(vec![]);
        self.functions.insert(instance.clone(), specialized.new_x(x));
        self.instances.push((target.clone(), ts.clone(), instance.clone()));
        Ok((instance, target, ts))
    }

    /// A spec fn the export adds beside `of`: `of` renamed (`<name>__tla_closed`)
    /// with the given parameters and body, returning `ret`.
    fn synthetic(
        &mut self,
        of: &Function,
        params: Vec<Param>,
        body: Option<Expr>,
        ret: &Typ,
    ) -> Fun {
        let segments = &of.x.name.path.segments;
        let last = segments.last().map(|s| s.to_string()).unwrap_or_default();
        let mut n = 1;
        let fun = loop {
            let seg = if n == 1 {
                format!("{last}__tla_closed")
            } else {
                format!("{last}__tla_closed{n}")
            };
            let mut segs: Vec<Ident> = segments[..segments.len().saturating_sub(1)].to_vec();
            segs.push(Arc::new(seg));
            let path =
                Arc::new(PathX { krate: of.x.name.path.krate.clone(), segments: Arc::new(segs) });
            let fun = Arc::new(FunX { path });
            if !self.functions.contains_key(&fun) {
                break fun;
            }
            n += 1;
        };
        let mut x = of.x.clone();
        x.name = fun.clone();
        x.params = Arc::new(params);
        x.ret = of.x.ret.new_x(ParamX { typ: ret.clone(), ..of.x.ret.x.clone() });
        x.require = Arc::new(vec![]);
        x.decrease = Arc::new(vec![]);
        x.decrease_when = None;
        x.decrease_by = None;
        x.body = body;
        self.functions.insert(fun.clone(), crate::def::Spanned::new(of.span.clone(), x));
        fun
    }
}
