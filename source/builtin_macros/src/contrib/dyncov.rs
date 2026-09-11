//! Dynamic verified coverage: the `verus_dyncov` mode of the `verus!` macro.
//!
//! In this mode ghost code is erased as in compile mode, and in addition:
//!
//! - every exec function is wrapped so that its calls are counted and
//!   its lowered `requires` (and, for `external_body` functions, its
//!   `ensures`) is evaluated on the real arguments by
//!   `vstd::contrib::dyncov`;
//! - every `assume(e)` in exec code is evaluated and counted;
//! - `fn main` flushes the profile on exit;
//! - every spec function with a body gets a lowered twin, registered by
//!   name so that contracts can call it; and every struct and enum gets a
//!   `DynView` impl so that contracts can look inside it.
//!
//! Lowering is syntactic and total: a spec expression becomes an exec
//! expression of type `Dyn`, and any construct the lowering does not
//! cover becomes `Dyn::Unknown` at that node rather than a compile error.
//! See `vstd::contrib::dyncov::value` for the value model.

use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{ToTokens, format_ident, quote, quote_spanned};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use verus_syn::spanned::Spanned;
use verus_syn::{
    Attribute, BinOp, Block, Ensures, Expr, ExprClosure, Fields, FnArgKind, FnMode, Generics,
    Ident, ImplItem, Item, ItemEnum, ItemFn, ItemStruct, Lit, MatchesOpToken, Member, Meta, Pat,
    Path, Publish, Requires, ReturnType, Signature, Stmt, Type, UnOp, Visibility,
};

/// The runtime paths. `vstd` is `::vstd` or `crate` depending on the crate
/// being compiled.
#[derive(Clone)]
pub(crate) struct Paths {
    pub vstd: TokenStream,
    pub rt: TokenStream,
}

impl Paths {
    pub(crate) fn new() -> Paths {
        let vstd = quote_vstd!(vstd => #vstd);
        let rt = quote! { #vstd::contrib::dyncov };
        Paths { vstd, rt }
    }
}

/// Per-`verus!`-block state.
pub(crate) struct State {
    pub paths: Paths,
    /// The name of this block's spec function table, if the block is a
    /// module-level `verus!` (not `verus_impl!`)
    pub table: Option<Ident>,
    /// Entries of the table: `(owner, name, arity, path to the fn, is_view)`
    pub entries: Vec<(String, String, usize, TokenStream, bool, Vec<String>)>,
    /// Nesting depth of `mod` items inside the block; the table is only
    /// visible at depth 0
    pub mod_depth: u32,
    /// The trait of the impl being visited, by its last segment
    pub impl_trait: Option<String>,
    /// The parameters of the exec fn being visited, for `assume`
    pub fn_params: Vec<Param>,
}

impl State {
    pub(crate) fn new(with_table: bool) -> State {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let table = with_table.then(|| {
            let n = COUNTER.fetch_add(1, Ordering::Relaxed);
            format_ident!("__DYNCOV_TABLE_{}", n)
        });
        State {
            paths: Paths::new(),
            table,
            entries: Vec::new(),
            mod_depth: 0,
            impl_trait: None,
            fn_params: Vec::new(),
        }
    }

    /// The items that close the block: the spec function table and the
    /// constructor that registers it at load time.
    pub(crate) fn finish(&mut self) -> Vec<Item> {
        let Some(table) = &self.table else { return vec![] };
        let rt = &self.paths.rt;
        let ctor = format_ident!("{}_CTOR", table);
        let entries: Vec<TokenStream> = self
            .entries
            .drain(..)
            .map(|(owner, name, arity, path, is_view, params)| {
                quote! { #rt::SpecEntry { owner: #owner, name: #name, arity: #arity, func: #path, is_view: #is_view, params: &[#(#params),*] } }
            })
            .collect();
        let items = quote! {
            #[doc(hidden)]
            #[allow(non_upper_case_globals, dead_code)]
            static #table: #rt::Table = #rt::Table { module: module_path!(), entries: &[#(#entries),*] };
            #[doc(hidden)]
            #[allow(non_upper_case_globals, dead_code)]
            #[used]
            #[cfg_attr(any(target_os = "linux", target_os = "android", target_os = "freebsd", target_os = "netbsd", target_os = "openbsd"), link_section = ".init_array")]
            #[cfg_attr(any(target_os = "macos", target_os = "ios"), link_section = "__DATA,__mod_init_func")]
            #[cfg_attr(windows, link_section = ".CRT$XCU")]
            static #ctor: extern "C" fn() = {
                extern "C" fn __dyncov_ctor() { #rt::register(&#table); }
                __dyncov_ctor
            };
        };
        vec![Item::Verbatim(items)]
    }
}

/// A parameter of an exec function as the contracts see it.
#[derive(Clone)]
pub(crate) struct Param {
    pub name: String,
    /// The expression that views the parameter: `&x`, or `&*x` for a
    /// reference parameter
    pub view_expr: TokenStream,
    pub is_mut_ref: bool,
}

pub(crate) fn params_of(sig: &Signature) -> Vec<Param> {
    let mut out = vec![];
    for arg in sig.inputs.iter() {
        match &arg.kind {
            FnArgKind::Receiver(r) => {
                let span = r.self_token.span;
                let (view_expr, is_mut_ref) = if r.reference.is_some() {
                    (quote_spanned!(span => &*self), r.mutability.is_some())
                } else {
                    (quote_spanned!(span => &self), false)
                };
                out.push(Param { name: "self".into(), view_expr, is_mut_ref });
            }
            FnArgKind::Typed(pt) => {
                let Pat::Ident(pi) = &*pt.pat else { continue };
                let name = pi.ident.clone();
                let span = name.span();
                let (view_expr, is_mut_ref) = match &*pt.ty {
                    Type::Reference(r) => (quote_spanned!(span => &*#name), r.mutability.is_some()),
                    _ => (quote_spanned!(span => &#name), false),
                };
                out.push(Param { name: name.to_string(), view_expr, is_mut_ref });
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Attributes

fn verifier_attr(attrs: &[Attribute], name: &str) -> bool {
    attrs.iter().any(|a| {
        let path = a.path();
        let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
        match segs.as_slice() {
            [v, n] if v == "verifier" && n == name => true,
            [v] if v == "verifier" => match &a.meta {
                Meta::List(list) => list.tokens.to_string() == name,
                _ => false,
            },
            _ => false,
        }
    })
}

pub(crate) fn is_external(attrs: &[Attribute]) -> bool {
    verifier_attr(attrs, "external")
        || verifier_attr(attrs, "external_fn_specification")
        || verifier_attr(attrs, "external_type_specification")
}

pub(crate) fn is_external_body(attrs: &[Attribute]) -> bool {
    verifier_attr(attrs, "external_body")
}

// ---------------------------------------------------------------------------
// Lowering

#[derive(Clone, Default)]
struct Env {
    /// Spec variable → expression producing its `Dyn` value
    vars: HashMap<String, TokenStream>,
    /// `old(x)` → expression
    old: HashMap<String, TokenStream>,
}

impl Env {
    fn bind(&self, name: &str, expr: TokenStream) -> Env {
        let mut env = self.clone();
        env.vars.insert(name.to_string(), expr);
        env
    }
}

struct Lower<'a> {
    paths: &'a Paths,
    /// The impl's `Self` type, by name, and its tokens if it can be named
    /// from a free function (non-generic)
    self_ty: Option<(String, Option<TokenStream>)>,
}

fn dyn_ident(name: &str, span: Span) -> Ident {
    Ident::new(&format!("__dc_{}", name), span)
}

fn ident_str(i: &Ident) -> String {
    i.to_string()
}

fn starts_upper(s: &str) -> bool {
    s.chars().next().map_or(false, |c| c.is_uppercase())
}

fn path_segments(path: &Path) -> Vec<String> {
    path.segments.iter().map(|s| ident_str(&s.ident)).collect()
}

/// Comparison chains are left-nested binaries: `(a <= b) < c`
fn chain_count(expr: &Expr) -> u32 {
    if let Expr::Binary(binary) = expr {
        match binary.op {
            BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_) | BinOp::Eq(_) => {
                1 + chain_count(&binary.left)
            }
            _ => 0,
        }
    } else {
        0
    }
}

impl<'a> Lower<'a> {
    fn unknown(&self, span: Span, reason: &str) -> TokenStream {
        let rt = &self.paths.rt;
        quote_spanned!(span => #rt::Dyn::Unknown(#reason))
    }

    fn view_of(&self, span: Span, expr: TokenStream) -> TokenStream {
        let vstd = &self.paths.vstd;
        quote_spanned!(span => #vstd::dyncov_view!(#expr))
    }

    fn self_name(&self, seg: &str) -> String {
        if seg == "Self" {
            if let Some((name, _)) = &self.self_ty {
                return name.clone();
            }
        }
        seg.to_string()
    }

    /// Substitutes `Self` in a path meant to be evaluated as exec code
    fn exec_path(&self, path: &Path) -> Option<TokenStream> {
        if path.segments.first().map_or(false, |s| s.ident == "Self") {
            let (_, tokens) = self.self_ty.as_ref()?;
            let tokens = tokens.as_ref()?;
            let rest = path.segments.iter().skip(1);
            return Some(quote! { <#tokens>#(::#rest)* });
        }
        Some(path.to_token_stream())
    }

    fn expr(&self, e: &Expr, env: &Env) -> TokenStream {
        let rt = &self.paths.rt;
        let span = e.span();
        match e {
            Expr::Lit(lit) => self.lit(&lit.lit, span),
            Expr::Paren(p) => self.expr(&p.expr, env),
            Expr::Group(g) => self.expr(&g.expr, env),
            Expr::Reference(r) => self.expr(&r.expr, env),
            Expr::View(v) => {
                let x = self.expr(&v.expr, env);
                quote_spanned!(span => #rt::view(&#x))
            }
            Expr::Block(b) => self.block(&b.block, env),
            Expr::Unary(u) => match &u.op {
                UnOp::Deref(_) => self.expr(&u.expr, env),
                UnOp::Not(_) => {
                    let x = self.expr(&u.expr, env);
                    quote_spanned!(span => #rt::not(&#x))
                }
                UnOp::Neg(_) => {
                    let x = self.expr(&u.expr, env);
                    quote_spanned!(span => #rt::neg(&#x))
                }
                UnOp::Forall(_) => self.quantifier(&u.expr, true, env, span),
                UnOp::Exists(_) => self.quantifier(&u.expr, false, env, span),
                UnOp::Choose(_) => self.unknown(span, "choose"),
                UnOp::Proof(_) => self.unknown(span, "proof block"),
                _ => self.unknown(span, "unary operator"),
            },
            Expr::Binary(b) => {
                if chain_count(e) >= 2 {
                    return self.chain(e, env, span);
                }
                let l = self.expr(&b.left, env);
                let r = self.expr(&b.right, env);
                match &b.op {
                    BinOp::Add(_) => quote_spanned!(span => #rt::add(&#l, &#r)),
                    BinOp::Sub(_) => quote_spanned!(span => #rt::sub(&#l, &#r)),
                    BinOp::Mul(_) => quote_spanned!(span => #rt::mul(&#l, &#r)),
                    BinOp::Div(_) => quote_spanned!(span => #rt::div(&#l, &#r)),
                    BinOp::Rem(_) => quote_spanned!(span => #rt::rem(&#l, &#r)),
                    BinOp::BitAnd(_) => quote_spanned!(span => #rt::bitand(&#l, &#r)),
                    BinOp::BitOr(_) => quote_spanned!(span => #rt::bitor(&#l, &#r)),
                    BinOp::BitXor(_) => quote_spanned!(span => #rt::bitxor(&#l, &#r)),
                    BinOp::Shl(_) => quote_spanned!(span => #rt::shl(&#l, &#r)),
                    BinOp::Shr(_) => quote_spanned!(span => #rt::shr(&#l, &#r)),
                    BinOp::And(_) => quote_spanned!(span => #rt::and(#l, || #r)),
                    BinOp::Or(_) => quote_spanned!(span => #rt::or(#l, || #r)),
                    BinOp::Imply(_) => quote_spanned!(span => #rt::implies(#l, || #r)),
                    BinOp::Exply(_) => quote_spanned!(span => #rt::implies(#r, || #l)),
                    BinOp::Equiv(_) => quote_spanned!(span => #rt::equiv(&#l, &#r)),
                    BinOp::Eq(_) | BinOp::BigEq(_) | BinOp::ExtEq(_) | BinOp::ExtDeepEq(_) => {
                        quote_spanned!(span => #rt::eq(&#l, &#r))
                    }
                    BinOp::Ne(_) | BinOp::BigNe(_) | BinOp::ExtNe(_) | BinOp::ExtDeepNe(_) => {
                        quote_spanned!(span => #rt::ne(&#l, &#r))
                    }
                    BinOp::Lt(_) => quote_spanned!(span => #rt::lt(&#l, &#r)),
                    BinOp::Le(_) => quote_spanned!(span => #rt::le(&#l, &#r)),
                    BinOp::Gt(_) => quote_spanned!(span => #rt::gt(&#l, &#r)),
                    BinOp::Ge(_) => quote_spanned!(span => #rt::ge(&#l, &#r)),
                    _ => self.unknown(span, "unsupported operator"),
                }
            }
            Expr::BigAnd(big) => {
                let mut acc = quote_spanned!(span => #rt::Dyn::Bool(true));
                for item in big.exprs.iter() {
                    let x = self.expr(&item.expr, env);
                    acc = quote_spanned!(span => #rt::and(#acc, || #x));
                }
                acc
            }
            Expr::BigOr(big) => {
                let mut acc = quote_spanned!(span => #rt::Dyn::Bool(false));
                for item in big.exprs.iter() {
                    let x = self.expr(&item.expr, env);
                    acc = quote_spanned!(span => #rt::or(#acc, || #x));
                }
                acc
            }
            Expr::Cast(c) => {
                let x = self.expr(&c.expr, env);
                match &*c.ty {
                    Type::Path(tp) if tp.qself.is_none() && tp.path.segments.len() == 1 => {
                        let ty = ident_str(&tp.path.segments[0].ident);
                        match ty.as_str() {
                            "int" | "nat" => x,
                            _ => quote_spanned!(span => #rt::cast(&#x, #ty)),
                        }
                    }
                    _ => self.unknown(span, "unsupported cast"),
                }
            }
            Expr::If(i) => {
                let else_branch = match &i.else_branch {
                    Some((_, e)) => self.expr(e, env),
                    None => quote_spanned!(span => #rt::Dyn::Unit),
                };
                if let Expr::Let(l) = &*i.cond {
                    // `if let pat = e { .. } else { .. }`
                    let scrutinee = self.expr(&l.expr, env);
                    let then = |env: &Env| self.block(&i.then_branch, env);
                    return self.match_arms(
                        scrutinee,
                        vec![(
                            &*l.pat,
                            None,
                            Box::new(then) as Box<dyn Fn(&Env) -> TokenStream + '_>,
                        )],
                        Some(else_branch),
                        env,
                        span,
                    );
                }
                let c = self.expr(&i.cond, env);
                let t = self.block(&i.then_branch, env);
                quote_spanned!(span => #rt::cond(&#c, || #t, || #else_branch))
            }
            Expr::Match(m) => {
                let scrutinee = self.expr(&m.expr, env);
                let arms: Vec<(&Pat, Option<&Expr>, Box<dyn Fn(&Env) -> TokenStream>)> = m
                    .arms
                    .iter()
                    .map(|arm| {
                        let body = &*arm.body;
                        let f = move |env: &Env| self.expr(body, env);
                        (
                            &arm.pat,
                            arm.guard.as_ref().map(|(_, g)| &**g),
                            Box::new(f) as Box<dyn Fn(&Env) -> TokenStream + '_>,
                        )
                    })
                    .collect();
                self.match_arms(scrutinee, arms, None, env, span)
            }
            Expr::Matches(m) => {
                let scrutinee = self.expr(&m.lhs, env);
                let (on_match, on_miss): (Box<dyn Fn(&Env) -> TokenStream + '_>, TokenStream) =
                    match &m.op_expr {
                        None => (
                            Box::new(|_: &Env| quote_spanned!(span => #rt::Dyn::Bool(true))),
                            quote_spanned!(span => #rt::Dyn::Bool(false)),
                        ),
                        Some(op) => {
                            let rhs = &*op.rhs;
                            let miss = match op.op_token {
                                MatchesOpToken::Implies(_) => true,
                                MatchesOpToken::AndAnd(_) | MatchesOpToken::BigAnd => false,
                            };
                            (
                                Box::new(move |env: &Env| self.expr(rhs, env)),
                                quote_spanned!(span => #rt::Dyn::Bool(#miss)),
                            )
                        }
                    };
                self.match_arms(scrutinee, vec![(&m.pat, None, on_match)], Some(on_miss), env, span)
            }
            Expr::Is(i) => {
                let base = self.expr(&i.base, env);
                let v = ident_str(&i.variant_ident);
                quote_spanned!(span => #rt::is_variant(&#base, #v))
            }
            Expr::IsNot(i) => {
                let base = self.expr(&i.base, env);
                let v = ident_str(&i.variant_ident);
                quote_spanned!(span => #rt::not(&#rt::is_variant(&#base, #v)))
            }
            Expr::Has(h) => {
                let l = self.expr(&h.lhs, env);
                let r = self.expr(&h.rhs, env);
                quote_spanned!(span => #rt::call_method(module_path!(), &#l, "contains", &[#r]))
            }
            Expr::HasNot(h) => {
                let l = self.expr(&h.lhs, env);
                let r = self.expr(&h.rhs, env);
                quote_spanned!(span => #rt::not(&#rt::call_method(module_path!(), &#l, "contains", &[#r])))
            }
            Expr::GetField(g) => {
                let base = self.expr(&g.base, env);
                let name = member_name(&g.member);
                quote_spanned!(span => #rt::field(&#base, #name))
            }
            Expr::Field(f) => {
                let base = self.expr(&f.base, env);
                let name = member_name(&f.member);
                quote_spanned!(span => #rt::field(&#base, #name))
            }
            Expr::Index(i) => {
                let base = self.expr(&i.expr, env);
                let idx = self.expr(&i.index, env);
                quote_spanned!(span => #rt::index(&#base, &#idx))
            }
            Expr::Final(f) => match &*f.arg {
                Expr::Path(p) if p.path.segments.len() == 1 => self.expr(&f.arg, env),
                _ => self.unknown(span, "final of a non-parameter"),
            },
            Expr::Path(p) => self.path(&p.path, env, span),
            Expr::Call(c) => self.call(c, env, span),
            Expr::MethodCall(m) => self.method_call(m, env, span),
            Expr::Struct(s) => {
                if s.rest.is_some() {
                    return self.unknown(span, "struct update syntax");
                }
                let (ty, variant) = type_and_variant(&s.path, self);
                let fields: Vec<TokenStream> = s
                    .fields
                    .iter()
                    .map(|f| {
                        let name = member_name(&f.member);
                        let value = self.expr(&f.expr, env);
                        quote_spanned!(span => (#name, #value))
                    })
                    .collect();
                quote_spanned!(span => #rt::Dyn::adt(#ty, #variant, vec![#(#fields),*]))
            }
            Expr::Tuple(t) => {
                if t.elems.is_empty() {
                    return quote_spanned!(span => #rt::Dyn::Unit);
                }
                let elems: Vec<TokenStream> = t.elems.iter().map(|x| self.expr(x, env)).collect();
                quote_spanned!(span => #rt::Dyn::tuple(vec![#(#elems),*]))
            }
            Expr::Macro(m) => {
                let name = m.mac.path.segments.last().map(|s| ident_str(&s.ident));
                match name.as_deref() {
                    Some("seq") | Some("set") => {
                        let parsed = m
                            .mac
                            .parse_body_with(
                                verus_syn::punctuated::Punctuated::<Expr, verus_syn::Token![,]>::parse_terminated,
                            );
                        match parsed {
                            Ok(items) => {
                                let elems: Vec<TokenStream> =
                                    items.iter().map(|x| self.expr(x, env)).collect();
                                if name.as_deref() == Some("seq") {
                                    quote_spanned!(span => #rt::Dyn::seq(vec![#(#elems),*]))
                                } else {
                                    quote_spanned!(span => #rt::Dyn::set(vec![#(#elems),*]))
                                }
                            }
                            Err(_) => self.unknown(span, "macro"),
                        }
                    }
                    _ => self.unknown(span, "macro"),
                }
            }
            Expr::Closure(_) => self.unknown(span, "closure"),
            Expr::Let(_) => self.unknown(span, "let expression"),
            _ => self.unknown(span, "unsupported expression"),
        }
    }

    fn lit(&self, lit: &Lit, span: Span) -> TokenStream {
        let rt = &self.paths.rt;
        match lit {
            Lit::Int(i) => match i.base10_digits().parse::<i128>() {
                Ok(_) => {
                    let l = verus_syn::LitInt::new(&format!("{}i128", i.base10_digits()), span);
                    quote_spanned!(span => #rt::Dyn::Int(#l))
                }
                Err(_) => self.unknown(span, "literal out of range"),
            },
            Lit::Bool(b) => {
                let v = b.value;
                quote_spanned!(span => #rt::Dyn::Bool(#v))
            }
            Lit::Char(c) => quote_spanned!(span => #rt::Dyn::Char(#c)),
            Lit::Byte(b) => quote_spanned!(span => #rt::Dyn::Int(#b as i128)),
            Lit::Str(s) => quote_spanned!(span => #rt::Dyn::Str(::std::rc::Rc::from(#s))),
            Lit::ByteStr(s) => {
                quote_spanned!(span => #rt::Dyn::seq((#s).iter().map(|b| #rt::Dyn::Int(*b as i128)).collect()))
            }
            Lit::Float(f) => {
                let l = verus_syn::LitFloat::new(&format!("{}f64", f.base10_digits()), span);
                quote_spanned!(span => #rt::Dyn::Float(#l))
            }
            _ => self.unknown(span, "literal"),
        }
    }

    fn chain(&self, e: &Expr, env: &Env, span: Span) -> TokenStream {
        // ((e0 <= e1) < e2) becomes e0 <= e1 && e1 < e2, each operand
        // evaluated once
        let rt = &self.paths.rt;
        let mut operands: Vec<&Expr> = vec![];
        let mut ops: Vec<TokenStream> = vec![];
        let mut cur = e;
        loop {
            match cur {
                Expr::Binary(b) if chain_count(cur) >= 1 => {
                    operands.push(&b.right);
                    let op = match b.op {
                        BinOp::Le(_) => quote!(le),
                        BinOp::Lt(_) => quote!(lt),
                        BinOp::Ge(_) => quote!(ge),
                        BinOp::Gt(_) => quote!(gt),
                        _ => quote!(eq),
                    };
                    ops.push(op);
                    cur = &b.left;
                }
                _ => {
                    operands.push(cur);
                    break;
                }
            }
        }
        operands.reverse();
        ops.reverse();
        let names: Vec<Ident> =
            (0..operands.len()).map(|i| format_ident!("__dc_chain_{}", i)).collect();
        let binds: Vec<TokenStream> = operands
            .iter()
            .zip(names.iter())
            .map(|(x, n)| {
                let v = self.expr(x, env);
                quote_spanned!(span => let #n = #v;)
            })
            .collect();
        let mut acc = quote_spanned!(span => #rt::Dyn::Bool(true));
        for (i, op) in ops.iter().enumerate() {
            let l = &names[i];
            let r = &names[i + 1];
            acc = quote_spanned!(span => #rt::and(#acc, || #rt::#op(&#l, &#r)));
        }
        quote_spanned!(span => { #(#binds)* #acc })
    }

    fn block(&self, block: &Block, env: &Env) -> TokenStream {
        let rt = &self.paths.rt;
        let span = block.span();
        let mut env = env.clone();
        let mut stmts: Vec<TokenStream> = vec![];
        let n = block.stmts.len();
        for (i, stmt) in block.stmts.iter().enumerate() {
            match stmt {
                Stmt::Local(local) => {
                    let Some(init) = &local.init else {
                        return self.unknown(span, "let without initializer");
                    };
                    if init.diverge.is_some() {
                        return self.unknown(span, "let-else");
                    }
                    let value = self.expr(&init.expr, &env);
                    match &local.pat {
                        Pat::Ident(pi) if pi.subpat.is_none() => {
                            let name = ident_str(&pi.ident);
                            let id = dyn_ident(&name, pi.ident.span());
                            stmts.push(quote_spanned!(span => let #id = #value;));
                            env = env.bind(&name, quote_spanned!(span => #id.clone()));
                        }
                        Pat::Type(pt) => match &*pt.pat {
                            Pat::Ident(pi) if pi.subpat.is_none() => {
                                let name = ident_str(&pi.ident);
                                let id = dyn_ident(&name, pi.ident.span());
                                stmts.push(quote_spanned!(span => let #id = #value;));
                                env = env.bind(&name, quote_spanned!(span => #id.clone()));
                            }
                            _ => return self.unknown(span, "let pattern"),
                        },
                        pat => {
                            // Destructuring let: bind through the pattern matcher
                            let mut binders = vec![];
                            let p = self.pat(pat, &mut binders);
                            let scrut = format_ident!("__dc_scrut_{}", i);
                            let bvec = format_ident!("__dc_b_{}", i);
                            stmts.push(quote_spanned!(span => let #scrut = #value;));
                            stmts.push(quote_spanned!(span =>
                                let mut #bvec: Vec<#rt::Dyn> = Vec::new();
                                let __dc_ok = #rt::pat_match(&#scrut, &#p, &mut #bvec) == Some(true);
                            ));
                            for (k, b) in binders.iter().enumerate() {
                                let id = dyn_ident(&ident_str(b), b.span());
                                stmts.push(quote_spanned!(span =>
                                    let #id = if __dc_ok { #bvec[#k].clone() } else { #rt::Dyn::Unknown("refutable let") };
                                ));
                                env = env.bind(&ident_str(b), quote_spanned!(span => #id.clone()));
                            }
                        }
                    }
                }
                Stmt::Expr(e, semi) => {
                    if i + 1 == n && semi.is_none() {
                        let value = self.expr(e, &env);
                        stmts.push(value);
                    } else {
                        // Side-effect-free in a spec (asserts, reveals): skip
                    }
                }
                Stmt::Item(_) | Stmt::Macro(_) => {}
            }
        }
        if block.stmts.last().map_or(true, |s| !matches!(s, Stmt::Expr(_, None))) {
            stmts.push(quote_spanned!(span => #rt::Dyn::Unit));
        }
        quote_spanned!(span => { #(#stmts)* })
    }

    /// A `match`-like construct: the arms are tried in order; a pattern
    /// that cannot inspect the scrutinee makes the whole thing `Unknown`.
    fn match_arms(
        &self,
        scrutinee: TokenStream,
        arms: Vec<(&Pat, Option<&Expr>, Box<dyn Fn(&Env) -> TokenStream + '_>)>,
        fallthrough: Option<TokenStream>,
        env: &Env,
        span: Span,
    ) -> TokenStream {
        let rt = &self.paths.rt;
        let mut arm_code: Vec<TokenStream> = vec![];
        for (pat, guard, body) in arms {
            let mut binders = vec![];
            let p = self.pat(pat, &mut binders);
            let mut arm_env = env.clone();
            let mut binds = vec![];
            for (k, b) in binders.iter().enumerate() {
                let name = ident_str(b);
                let id = dyn_ident(&name, b.span());
                binds.push(quote_spanned!(span => let #id = __dc_b[#k].clone();));
                arm_env = arm_env.bind(&name, quote_spanned!(span => #id.clone()));
            }
            let body = body(&arm_env);
            let guard_code = match guard {
                Some(g) => {
                    let g = self.expr(g, &arm_env);
                    quote_spanned!(span =>
                        match #rt::Dyn::verdict(&#g) {
                            #rt::Verdict::True => { break '__dc_m #body; }
                            #rt::Verdict::False => {}
                            #rt::Verdict::Unknown => { break '__dc_m #rt::Dyn::Unknown("match guard"); }
                        }
                    )
                }
                None => quote_spanned!(span => break '__dc_m #body;),
            };
            arm_code.push(quote_spanned!(span =>
                {
                    __dc_b.clear();
                    match #rt::pat_match(&__dc_s, &#p, &mut __dc_b) {
                        Some(true) => { #(#binds)* #guard_code }
                        Some(false) => {}
                        None => { break '__dc_m #rt::Dyn::Unknown("pattern"); }
                    }
                }
            ));
        }
        let end = match fallthrough {
            Some(f) => f,
            None => quote_spanned!(span => #rt::Dyn::Unknown("no arm matched")),
        };
        quote_spanned!(span => {
            let __dc_s = #scrutinee;
            #[allow(unused_mut)]
            let mut __dc_b: Vec<#rt::Dyn> = Vec::new();
            #[allow(unreachable_code, unused_labels)]
            '__dc_m: {
                #(#arm_code)*
                #end
            }
        })
    }

    fn pat(&self, pat: &Pat, binders: &mut Vec<Ident>) -> TokenStream {
        let rt = &self.paths.rt;
        let span = pat.span();
        match pat {
            Pat::Wild(_) => quote_spanned!(span => #rt::Pat::Wild),
            Pat::Ident(pi) => {
                if pi.subpat.is_some() {
                    return quote_spanned!(span => #rt::Pat::Unsupported);
                }
                let name = ident_str(&pi.ident);
                if starts_upper(&name) {
                    quote_spanned!(span => #rt::Pat::Variant("", #name, &[]))
                } else {
                    binders.push(pi.ident.clone());
                    quote_spanned!(span => #rt::Pat::Bind)
                }
            }
            Pat::Lit(l) => match &l.lit {
                Lit::Int(i) => {
                    let l = verus_syn::LitInt::new(&format!("{}i128", i.base10_digits()), span);
                    quote_spanned!(span => #rt::Pat::Int(#l))
                }
                Lit::Bool(b) => {
                    let v = b.value;
                    quote_spanned!(span => #rt::Pat::Bool(#v))
                }
                Lit::Char(c) => quote_spanned!(span => #rt::Pat::Char(#c)),
                Lit::Byte(b) => quote_spanned!(span => #rt::Pat::Int(#b as i128)),
                Lit::Str(s) => quote_spanned!(span => #rt::Pat::Str(#s)),
                _ => quote_spanned!(span => #rt::Pat::Unsupported),
            },
            Pat::Path(p) => {
                let (ty, variant) = type_and_variant(&p.path, self);
                quote_spanned!(span => #rt::Pat::Variant(#ty, #variant, &[]))
            }
            Pat::TupleStruct(ts) => {
                if ts.elems.iter().any(|e| matches!(e, Pat::Rest(_))) {
                    return quote_spanned!(span => #rt::Pat::Unsupported);
                }
                let (ty, variant) = type_and_variant(&ts.path, self);
                let elems: Vec<TokenStream> =
                    ts.elems.iter().map(|e| self.pat(e, binders)).collect();
                quote_spanned!(span => #rt::Pat::Variant(#ty, #variant, &[#(#elems),*]))
            }
            Pat::Struct(s) => {
                let (ty, variant) = type_and_variant(&s.path, self);
                let rest = s.rest.is_some();
                let fields: Vec<TokenStream> = s
                    .fields
                    .iter()
                    .map(|f| {
                        let name = member_name(&f.member);
                        let p = self.pat(&f.pat, binders);
                        quote_spanned!(span => (#name, #p))
                    })
                    .collect();
                quote_spanned!(span => #rt::Pat::Struct(#ty, #variant, &[#(#fields),*], #rest))
            }
            Pat::Tuple(t) => {
                if t.elems.iter().any(|e| matches!(e, Pat::Rest(_))) {
                    return quote_spanned!(span => #rt::Pat::Unsupported);
                }
                let elems: Vec<TokenStream> =
                    t.elems.iter().map(|e| self.pat(e, binders)).collect();
                quote_spanned!(span => #rt::Pat::Tuple(&[#(#elems),*]))
            }
            Pat::Reference(r) => self.pat(&r.pat, binders),
            Pat::Paren(p) => self.pat(&p.pat, binders),
            Pat::Type(t) => self.pat(&t.pat, binders),
            Pat::Or(o) => {
                // Every alternative must bind the same names in the same
                // order; check by count only
                let mut alts = vec![];
                let before = binders.len();
                let mut count = None;
                for case in o.cases.iter() {
                    let mut b = vec![];
                    alts.push(self.pat(case, &mut b));
                    if count.map_or(false, |c| c != b.len()) {
                        return quote_spanned!(span => #rt::Pat::Unsupported);
                    }
                    count = Some(b.len());
                    if binders.len() == before {
                        binders.extend(b);
                    }
                }
                quote_spanned!(span => #rt::Pat::Or(&[#(#alts),*]))
            }
            _ => quote_spanned!(span => #rt::Pat::Unsupported),
        }
    }

    fn path(&self, path: &Path, env: &Env, span: Span) -> TokenStream {
        let rt = &self.paths.rt;
        let segs = path_segments(path);
        if segs.len() == 1 {
            let name = &segs[0];
            if let Some(v) = env.vars.get(name) {
                return v.clone();
            }
            if name == "None" {
                return quote_spanned!(span => #rt::Dyn::option(None));
            }
            if starts_upper(name) {
                // A unit struct, a unit variant, or a constant
                return self.view_of(span, quote_spanned!(span => &#path));
            }
            return self.unknown(span, "unbound variable");
        }
        let last = segs.last().unwrap();
        if starts_upper(last)
            || last.chars().all(|c| c.is_uppercase() || c == '_' || c.is_ascii_digit())
        {
            match self.exec_path(path) {
                Some(p) => self.view_of(span, quote_spanned!(span => &(#p))),
                None => self.unknown(span, "Self in a generic impl"),
            }
        } else {
            self.unknown(span, "function value")
        }
    }

    fn call(&self, c: &verus_syn::ExprCall, env: &Env, span: Span) -> TokenStream {
        let rt = &self.paths.rt;
        let Expr::Path(fp) = &*c.func else {
            return self.unknown(span, "callee");
        };
        let segs = path_segments(&fp.path);
        let args: Vec<&Expr> = c.args.iter().collect();
        let last = segs.last().unwrap().clone();
        if segs.len() == 1 {
            match (last.as_str(), args.as_slice()) {
                ("old", [Expr::Path(p)]) if p.path.segments.len() == 1 => {
                    let name = ident_str(&p.path.segments[0].ident);
                    return match env.old.get(&name) {
                        Some(v) => v.clone(),
                        None => self.unknown(span, "old of a non-parameter"),
                    };
                }
                ("old", _) => return self.unknown(span, "old of a non-parameter"),
                ("Some", [x]) => {
                    let x = self.expr(x, env);
                    return quote_spanned!(span => #rt::Dyn::option(Some(#x)));
                }
                ("Ok", [x]) => {
                    let x = self.expr(x, env);
                    return quote_spanned!(span => #rt::Dyn::adt("core::result::Result", "Ok", vec![("0", #x)]));
                }
                ("Err", [x]) => {
                    let x = self.expr(x, env);
                    return quote_spanned!(span => #rt::Dyn::adt("core::result::Result", "Err", vec![("0", #x)]));
                }
                _ => {}
            }
        }
        // vstd constructors
        if segs.len() >= 2 {
            let first = segs[0].as_str();
            match (first, last.as_str(), args.as_slice()) {
                ("Seq", "empty", []) => return quote_spanned!(span => #rt::Dyn::seq(vec![])),
                ("Set", "empty", []) => return quote_spanned!(span => #rt::Dyn::set(vec![])),
                ("Map", "empty", []) => {
                    return quote_spanned!(span => #rt::Dyn::Map(::std::rc::Rc::new(vec![])));
                }
                ("Seq", "new", [len, Expr::Closure(cl)]) => {
                    let len = self.expr(len, env);
                    return match self.closure1(cl, env) {
                        Some(f) => quote_spanned!(span => #rt::seq_new(&#len, &#f)),
                        None => self.unknown(span, "Seq::new closure"),
                    };
                }
                ("Box" | "Rc" | "Arc", "new", [x]) => return self.expr(x, env),
                _ => {}
            }
        }
        let lowered: Vec<TokenStream> = args.iter().map(|a| self.expr(a, env)).collect();
        if starts_upper(&last) {
            // Tuple struct or tuple variant constructor
            let (ty, variant) = type_and_variant(&fp.path, self);
            let fields: Vec<TokenStream> = lowered
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    let name = i.to_string();
                    quote_spanned!(span => (#name, #v))
                })
                .collect();
            return quote_spanned!(span => #rt::Dyn::adt(#ty, #variant, vec![#(#fields),*]));
        }
        // A spec function, resolved by name at run time (see `call_spec`)
        let qualifier = self.qualifier(&segs[..segs.len() - 1]);
        quote_spanned!(span => #rt::call_spec(module_path!(), #qualifier, #last, &[#(#lowered),*]))
    }

    /// The module or type prefix of a call, with `crate`/`self`/`super`
    /// dropped and `Self` resolved
    fn qualifier(&self, prefix: &[String]) -> String {
        let parts: Vec<String> = prefix
            .iter()
            .filter(|s| !matches!(s.as_str(), "crate" | "self" | "super"))
            .map(|s| self.self_name(s))
            .collect();
        parts.join("::")
    }

    fn closure1(&self, cl: &ExprClosure, env: &Env) -> Option<TokenStream> {
        let rt = &self.paths.rt;
        if cl.inputs.len() != 1 {
            return None;
        }
        let name = closure_binder(&cl.inputs[0].pat)?;
        let id = dyn_ident(&name, cl.span());
        let env = env.bind(&name, quote!(#id.clone()));
        let body = self.expr(&cl.body, &env);
        let span = cl.span();
        Some(quote_spanned!(span => |#id: #rt::Dyn| -> #rt::Dyn { #body }))
    }

    fn method_call(&self, m: &verus_syn::ExprMethodCall, env: &Env, span: Span) -> TokenStream {
        let rt = &self.paths.rt;
        let recv = self.expr(&m.receiver, env);
        let name = ident_str(&m.method);
        let args: Vec<&Expr> = m.args.iter().collect();
        match (name.as_str(), args.as_slice()) {
            ("view" | "deep_view", []) => return quote_spanned!(span => #rt::view(&#recv)),
            ("filter" | "map" | "map_values" | "all" | "any", [Expr::Closure(cl)]) => {
                return match self.closure1(cl, env) {
                    Some(f) => {
                        let op = &name;
                        quote_spanned!(span => #rt::seq_closure_op(&#recv, #op, &#f))
                    }
                    None => self.unknown(span, "closure argument"),
                };
            }
            _ => {}
        }
        let lowered: Vec<TokenStream> = args.iter().map(|a| self.expr(a, env)).collect();
        quote_spanned!(span => #rt::call_method(module_path!(), &#recv, #name, &[#(#lowered),*]))
    }

    /// `forall|x: T, ..| body` / `exists|..| body` over bounded ranges
    fn quantifier(&self, arg: &Expr, forall: bool, env: &Env, span: Span) -> TokenStream {
        let rt = &self.paths.rt;
        let Expr::Closure(cl) = arg else {
            return self.unknown(span, "quantifier");
        };
        let mut vars: Vec<(String, Option<String>, Span)> = vec![];
        for input in cl.inputs.iter() {
            match &input.pat {
                Pat::Type(pt) => {
                    let Some(name) = closure_binder(&pt.pat) else {
                        return self.unknown(span, "quantifier binder");
                    };
                    let ty = match &*pt.ty {
                        Type::Path(tp) => tp.path.segments.last().map(|s| ident_str(&s.ident)),
                        _ => None,
                    };
                    vars.push((name, ty, pt.span()));
                }
                pat => {
                    let Some(name) = closure_binder(pat) else {
                        return self.unknown(span, "quantifier binder");
                    };
                    vars.push((name, None, pat.span()));
                }
            }
        }
        if vars.is_empty() || vars.len() > 3 {
            return self.unknown(span, "quantifier arity");
        }
        // The body is `guard ==> rest` (forall) or `guard && rest` (exists);
        // the guard's conjuncts bound the variables
        let body = strip_attrs(&cl.body);
        let mut constraints: Vec<&Expr> = vec![];
        match body {
            Expr::Binary(b) if forall && matches!(b.op, BinOp::Imply(_)) => {
                conjuncts(&b.left, &mut constraints)
            }
            Expr::Binary(b) if !forall && matches!(b.op, BinOp::And(_)) => {
                conjuncts(&b.left, &mut constraints)
            }
            Expr::BigAnd(big) if !forall => {
                for item in big.exprs.iter() {
                    conjuncts(&item.expr, &mut constraints);
                }
            }
            _ => {}
        }
        // Build nested loops, innermost last
        let mut inner_env = env.clone();
        let mut ids = vec![];
        for (name, _, vspan) in &vars {
            let id = dyn_ident(name, *vspan);
            inner_env = inner_env.bind(name, quote!(#id.clone()));
            ids.push(id);
        }
        let whole = self.expr(&cl.body, &inner_env);
        let mut code = whole;
        let op = if forall { quote!(forall1) } else { quote!(exists1) };
        for (k, (name, ty, _)) in vars.iter().enumerate().rev() {
            let mut bound_env = env.clone();
            for (name2, _, vspan2) in vars.iter().take(k) {
                let id2 = dyn_ident(name2, *vspan2);
                bound_env = bound_env.bind(name2, quote!(#id2.clone()));
            }
            let (lo, hi) = match self.bounds(name, ty.as_deref(), &constraints, &bound_env, span) {
                Some(b) => b,
                None => return self.unknown(span, "unbounded quantifier"),
            };
            let id = &ids[k];
            code = quote_spanned!(span => #rt::#op(&#lo, &#hi, &|#id: #rt::Dyn| -> #rt::Dyn { #code }));
        }
        code
    }

    /// The `[lo, hi)` range of a quantified variable from the guard's
    /// conjuncts, or from its type when it is `u8`, `i8`, or `bool`
    fn bounds(
        &self,
        var: &str,
        ty: Option<&str>,
        constraints: &[&Expr],
        env: &Env,
        span: Span,
    ) -> Option<(TokenStream, TokenStream)> {
        let rt = &self.paths.rt;
        let mut lo: Option<TokenStream> = None;
        let mut hi: Option<TokenStream> = None;
        let is_var = |e: &Expr| matches!(strip_attrs(e), Expr::Path(p) if p.path.segments.len() == 1 && p.path.segments[0].ident == var);
        let one = quote_spanned!(span => #rt::Dyn::Int(1i128));
        for c in constraints {
            // Flatten a chain into (operand, op, operand) triples
            let mut operands: Vec<&Expr> = vec![];
            let mut ops: Vec<&BinOp> = vec![];
            let mut cur = *c;
            loop {
                match cur {
                    Expr::Binary(b)
                        if matches!(
                            b.op,
                            BinOp::Le(_) | BinOp::Lt(_) | BinOp::Ge(_) | BinOp::Gt(_)
                        ) =>
                    {
                        operands.push(&b.right);
                        ops.push(&b.op);
                        cur = &b.left;
                    }
                    Expr::Paren(p) => cur = &p.expr,
                    _ => {
                        operands.push(cur);
                        break;
                    }
                }
            }
            operands.reverse();
            ops.reverse();
            for (i, op) in ops.iter().enumerate() {
                let (l, r) = (operands[i], operands[i + 1]);
                // Normalize to `a < var`, `a <= var`, `var < b`, `var <= b`
                let (lower, strict) = match op {
                    BinOp::Le(_) | BinOp::Lt(_) if is_var(r) => {
                        (Some(l), matches!(op, BinOp::Lt(_)))
                    }
                    BinOp::Ge(_) | BinOp::Gt(_) if is_var(l) => {
                        (Some(r), matches!(op, BinOp::Gt(_)))
                    }
                    _ => (None, false),
                };
                if let Some(b) = lower {
                    let x = self.expr(b, env);
                    lo =
                        Some(if strict { quote_spanned!(span => #rt::add(&#x, &#one)) } else { x });
                    continue;
                }
                let (upper, strict) = match op {
                    BinOp::Le(_) | BinOp::Lt(_) if is_var(l) => {
                        (Some(r), matches!(op, BinOp::Lt(_)))
                    }
                    BinOp::Ge(_) | BinOp::Gt(_) if is_var(r) => {
                        (Some(l), matches!(op, BinOp::Gt(_)))
                    }
                    _ => (None, false),
                };
                if let Some(b) = upper {
                    let x = self.expr(b, env);
                    hi =
                        Some(if strict { x } else { quote_spanned!(span => #rt::add(&#x, &#one)) });
                }
            }
        }
        let zero = quote_spanned!(span => #rt::Dyn::Int(0i128));
        match ty {
            Some("nat" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize") if lo.is_none() => {
                lo = Some(zero.clone())
            }
            _ => {}
        }
        match ty {
            Some("u8") if hi.is_none() => hi = Some(quote_spanned!(span => #rt::Dyn::Int(256i128))),
            Some("i8") => {
                if lo.is_none() {
                    lo = Some(quote_spanned!(span => #rt::Dyn::Int(-128i128)));
                }
                if hi.is_none() {
                    hi = Some(quote_spanned!(span => #rt::Dyn::Int(128i128)));
                }
            }
            Some("bool") => {
                lo = Some(zero);
                hi = Some(quote_spanned!(span => #rt::Dyn::Int(2i128)));
            }
            _ => {}
        }
        Some((lo?, hi?))
    }
}

fn strip_attrs(e: &Expr) -> &Expr {
    match e {
        Expr::Paren(p) if p.attrs.is_empty() => strip_attrs(&p.expr),
        Expr::Group(g) => strip_attrs(&g.expr),
        _ => e,
    }
}

fn conjuncts<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>) {
    match strip_attrs(e) {
        Expr::Binary(b) if matches!(b.op, BinOp::And(_)) => {
            conjuncts(&b.left, out);
            conjuncts(&b.right, out);
        }
        Expr::BigAnd(big) => {
            for item in big.exprs.iter() {
                conjuncts(&item.expr, out);
            }
        }
        e => out.push(e),
    }
}

fn closure_binder(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Ident(pi) if pi.subpat.is_none() => Some(ident_str(&pi.ident)),
        Pat::Type(pt) => closure_binder(&pt.pat),
        Pat::Paren(p) => closure_binder(&p.pat),
        _ => None,
    }
}

fn member_name(m: &Member) -> String {
    match m {
        Member::Named(i) => ident_str(i),
        Member::Unnamed(i) => i.index.to_string(),
    }
}

/// `Token::Number` → ("Token", "Number"); `Foo` → ("Foo", ""); `None` →
/// ("", "None"); `Self::V` → (self type, "V")
fn type_and_variant(path: &Path, lower: &Lower) -> (String, String) {
    let segs = path_segments(path);
    match segs.as_slice() {
        [] => (String::new(), String::new()),
        [one] => match one.as_str() {
            "Some" | "None" | "Ok" | "Err" => (String::new(), one.clone()),
            _ => (one.clone(), String::new()),
        },
        [.., ty, variant] => {
            if starts_upper(ty) || ty == "Self" {
                (lower.self_name(ty), variant.clone())
            } else {
                // `module::Type`
                (variant.clone(), String::new())
            }
        }
    }
}

/// Identifiers mentioned anywhere in a token stream
fn idents_in(ts: &TokenStream, out: &mut Vec<String>) {
    for tt in ts.clone() {
        match tt {
            TokenTree::Ident(i) => out.push(i.to_string()),
            TokenTree::Group(g) => idents_in(&g.stream(), out),
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Wrappers

/// The contracts of an exec function, captured before erasure.
pub(crate) struct Contracts {
    pub requires: Option<Requires>,
    pub ensures: Option<Ensures>,
    pub ret_pat: Option<Pat>,
    pub external_body: bool,
}

pub(crate) fn capture(sig: &Signature, attrs: &[Attribute]) -> Contracts {
    let ret_pat = match &sig.output {
        ReturnType::Type(_, _, Some(ret), _) => Some(ret.1.clone()),
        _ => None,
    };
    Contracts {
        requires: sig.spec.requires.clone(),
        ensures: sig.spec.ensures.clone(),
        ret_pat,
        external_body: is_external_body(attrs),
    }
}

/// Whether the function is an exec function this mode instruments.
pub(crate) fn wrappable(sig: &Signature, attrs: &[Attribute], has_body: bool) -> bool {
    has_body
        && matches!(sig.mode, FnMode::Default | FnMode::Exec(_))
        && sig.constness.is_none()
        && sig.asyncness.is_none()
        && sig.abi.is_none()
        && sig.variadic.is_none()
        && !is_external(attrs)
}

fn ret_type_annotation(sig: &Signature) -> TokenStream {
    match &sig.output {
        ReturnType::Default => quote!(),
        ReturnType::Type(_, _, _, ty) => {
            let s = ty.to_token_stream().to_string();
            if s.contains("impl ") || s.contains("impl<") { quote!() } else { quote!(-> #ty) }
        }
    }
}

fn first_span(sig: &Signature, vis: Option<&Visibility>) -> Span {
    match vis {
        Some(Visibility::Public(p)) => p.span,
        Some(Visibility::Restricted(r)) => r.pub_token.span,
        _ => sig
            .constness
            .map(|t| t.span)
            .or(sig.asyncness.map(|t| t.span))
            .or(sig.unsafety.map(|t| t.span))
            .unwrap_or(sig.fn_token.span),
    }
}

/// Rewrites the body of an exec function into its instrumented form.
pub(crate) fn wrap(
    state: &State,
    sig: &Signature,
    vis: Option<&Visibility>,
    attrs: &mut Vec<Attribute>,
    block: &mut Block,
    contracts: Contracts,
    self_ty: Option<(String, Option<TokenStream>)>,
    is_main: bool,
) {
    let rt = &state.paths.rt;
    let requires: Vec<&Expr> =
        contracts.requires.as_ref().map_or(vec![], |r| r.exprs.exprs.iter().collect());
    let ensures: Vec<&Expr> = if contracts.external_body {
        contracts.ensures.as_ref().map_or(vec![], |e| e.exprs.exprs.iter().collect())
    } else {
        vec![]
    };
    // Every exec function gets a frame, so that calls are counted and
    // taint reaches it; the clauses are evaluated when there are any
    let instrument = true;
    let span = first_span(sig, vis);
    let fn_span = sig.fn_token.span;
    let name = ident_str(&sig.ident);
    let lower = Lower { paths: &state.paths, self_ty };
    let params = params_of(sig);

    // Which parameters the clauses mention
    let mut mentioned: Vec<String> = vec![];
    for e in requires.iter().chain(ensures.iter()) {
        idents_in(&e.to_token_stream(), &mut mentioned);
    }
    if let Some(p) = &contracts.ret_pat {
        idents_in(&p.to_token_stream(), &mut mentioned);
    }

    let mut prologue: Vec<TokenStream> = vec![];
    let mut env = Env::default();
    let unsafe_tok = sig.unsafety.map(|_| quote!(unsafe));
    let body_stmts = std::mem::take(&mut block.stmts);
    let ret_ann = ret_type_annotation(sig);
    let call_body = quote_spanned!(fn_span =>
        (|| #ret_ann { #unsafe_tok { #(#body_stmts)* } })()
    );

    if is_main {
        prologue.push(quote_spanned!(fn_span => let __dyncov_flush = #rt::FlushOnExit;));
    }
    if instrument {
        let kind = if contracts.external_body { quote!(Trusted) } else { quote!(Verified) };
        let register = match (&state.table, state.mod_depth) {
            (Some(table), 0) => quote_spanned!(fn_span => #rt::register(&#table);),
            _ => quote!(),
        };
        prologue.push(quote_spanned!(fn_span =>
            fn __dyncov_probe() {}
            #register
            let __dyncov_guard = #rt::enter(
                #rt::FnId {
                    file: file!(),
                    line: line!(),
                    name: #name,
                    path: ::core::any::type_name_of_val(&__dyncov_probe),
                },
                #rt::Kind::#kind,
            );
        ));
        // The `file!()`/`line!()` must carry the span of the item's first
        // token so that they name the line the static report uses
        prologue = prologue.into_iter().map(|ts| respan_builtin_calls(ts, span)).collect();
        for p in &params {
            if !mentioned.iter().any(|m| m == &p.name) {
                continue;
            }
            let id = dyn_ident(&p.name, fn_span);
            let view = p.view_expr.clone();
            let vstd = &state.paths.vstd;
            prologue.push(
                quote_spanned!(fn_span => let #id = #rt::snapshot(|| #vstd::dyncov_view!(#view));),
            );
            env.old.insert(p.name.clone(), quote!(#id.clone()));
            env.vars.insert(p.name.clone(), quote!(#id.clone()));
        }
        if !requires.is_empty() {
            let clauses: Vec<TokenStream> = requires
                .iter()
                .map(|e| {
                    let l = lower.expr(e, &env);
                    let s = e.span();
                    quote_spanned!(s => (line!(), &|| -> #rt::Dyn { #l }))
                })
                .collect();
            prologue.push(quote_spanned!(fn_span =>
                #rt::pre(&__dyncov_guard, #rt::eval(&[#(#clauses),*]), ::core::panic::Location::caller());
            ));
        }
        if !ensures.is_empty() {
            let mut post_env = env.clone();
            let mut post: Vec<TokenStream> = vec![];
            post.push(quote_spanned!(fn_span => let __dyncov_ret = #call_body;));
            // Mutable reference parameters are re-viewed after the call
            for p in &params {
                if p.is_mut_ref && mentioned.iter().any(|m| m == &p.name) {
                    let id = format_ident!("__dc_post_{}", p.name);
                    let view = p.view_expr.clone();
                    let vstd = &state.paths.vstd;
                    post.push(quote_spanned!(fn_span => let #id = #rt::snapshot(|| #vstd::dyncov_view!(#view));));
                    post_env.vars.insert(p.name.clone(), quote!(#id.clone()));
                }
            }
            let vstd = &state.paths.vstd;
            post.push(quote_spanned!(fn_span => let __dc_ret = #rt::snapshot(|| #vstd::dyncov_view!(&__dyncov_ret));));
            // Bind the return pattern
            match &contracts.ret_pat {
                Some(Pat::Ident(pi)) => {
                    post_env.vars.insert(ident_str(&pi.ident), quote!(__dc_ret.clone()));
                }
                Some(pat) => {
                    let mut binders = vec![];
                    let p = lower.pat(pat, &mut binders);
                    post.push(quote_spanned!(fn_span =>
                        let mut __dc_retb: Vec<#rt::Dyn> = Vec::new();
                        let __dc_ret_ok = #rt::pat_match(&__dc_ret, &#p, &mut __dc_retb) == Some(true);
                    ));
                    for (k, b) in binders.iter().enumerate() {
                        let id = dyn_ident(&ident_str(b), fn_span);
                        post.push(quote_spanned!(fn_span =>
                            let #id = if __dc_ret_ok { __dc_retb[#k].clone() } else { #rt::Dyn::Unknown("return pattern") };
                        ));
                        post_env.vars.insert(ident_str(b), quote!(#id.clone()));
                    }
                }
                None => {}
            }
            let clauses: Vec<TokenStream> = ensures
                .iter()
                .map(|e| {
                    let l = lower.expr(e, &post_env);
                    let s = e.span();
                    quote_spanned!(s => (line!(), &|| -> #rt::Dyn { #l }))
                })
                .collect();
            post.push(quote_spanned!(fn_span =>
                #rt::trusted_post(&__dyncov_guard, #rt::eval(&[#(#clauses),*]));
                __dyncov_ret
            ));
            let stmt: Stmt = Stmt::Expr(
                Expr::Verbatim(quote_spanned!(fn_span => { #(#prologue)* #(#post)* })),
                None,
            );
            block.stmts = vec![stmt];
            attrs.push(verus_syn::parse_quote_spanned!(fn_span => #[track_caller]));
            attrs.push(verus_syn::parse_quote_spanned!(fn_span => #[allow(unused_mut, unused_variables, unused_unsafe, unreachable_code, clippy::all)]));
            return;
        }
        // The caller's location is only needed to attribute a false
        // precondition; `main` may not carry the attribute
        if !requires.is_empty() && !is_main {
            attrs.push(verus_syn::parse_quote_spanned!(fn_span => #[track_caller]));
        }
    }
    attrs.push(verus_syn::parse_quote_spanned!(fn_span => #[allow(unused_mut, unused_variables, unused_unsafe, unreachable_code, clippy::all)]));
    let stmt: Stmt =
        Stmt::Expr(Expr::Verbatim(quote_spanned!(fn_span => { #(#prologue)* #call_body })), None);
    block.stmts = vec![stmt];
}

/// Gives every `file!()`/`line!()` invocation the item's span.
fn respan_builtin_calls(ts: TokenStream, span: Span) -> TokenStream {
    let mut out: Vec<TokenTree> = vec![];
    let mut iter = ts.into_iter().peekable();
    while let Some(tt) = iter.next() {
        match tt {
            TokenTree::Ident(i) if i == "file" || i == "line" => {
                if let Some(TokenTree::Punct(p)) = iter.peek() {
                    if p.as_char() == '!' {
                        let mut i2 = i.clone();
                        i2.set_span(span);
                        out.push(TokenTree::Ident(i2));
                        let mut p2 = match iter.next() {
                            Some(TokenTree::Punct(p)) => p,
                            _ => unreachable!(),
                        };
                        p2.set_span(span);
                        out.push(TokenTree::Punct(p2));
                        if let Some(TokenTree::Group(g)) = iter.next() {
                            let mut g2 = proc_macro2::Group::new(g.delimiter(), g.stream());
                            g2.set_span(span);
                            out.push(TokenTree::Group(g2));
                        }
                        continue;
                    }
                }
                out.push(TokenTree::Ident(i));
            }
            TokenTree::Group(g) => {
                let mut g2 =
                    proc_macro2::Group::new(g.delimiter(), respan_builtin_calls(g.stream(), span));
                g2.set_span(g.span());
                out.push(TokenTree::Group(g2));
            }
            other => out.push(other),
        }
    }
    out.into_iter().collect()
}

/// `assume(e)` in exec code, evaluated over the enclosing function's
/// parameters.
pub(crate) fn lower_assume(
    state: &State,
    e: &Expr,
    self_ty: Option<(String, Option<TokenStream>)>,
) -> Expr {
    let rt = &state.paths.rt;
    let vstd = &state.paths.vstd;
    let span = e.span();
    let lower = Lower { paths: &state.paths, self_ty };
    let mut env = Env::default();
    let mut mentioned = vec![];
    idents_in(&e.to_token_stream(), &mut mentioned);
    let mut binds = vec![];
    for p in &state.fn_params {
        if !mentioned.iter().any(|m| m == &p.name) {
            continue;
        }
        let id = dyn_ident(&p.name, span);
        let view = p.view_expr.clone();
        binds.push(quote_spanned!(span => let #id = #rt::snapshot(|| #vstd::dyncov_view!(#view));));
        env.vars.insert(p.name.clone(), quote!(#id.clone()));
    }
    let l = lower.expr(e, &env);
    Expr::Verbatim(quote_spanned!(span => {
        #(#binds)*
        #rt::assume(#rt::eval(&[(line!(), &|| -> #rt::Dyn { #l })]), ::core::panic::Location::caller());
    }))
}

// ---------------------------------------------------------------------------
// Spec function twins and views

fn is_spec_with_body(sig: &Signature, has_body: bool) -> bool {
    has_body
        && matches!(sig.mode, FnMode::Spec(_) | FnMode::SpecChecked(_))
        && !matches!(sig.publish, Publish::Uninterp(_))
}

/// The twin of a spec function: `fn __dyncov_spec_<name>(args: &[Dyn]) -> Dyn`.
fn twin(
    state: &mut State,
    sig: &Signature,
    block: &Block,
    attrs: &[Attribute],
    owner: Option<(String, Option<TokenStream>)>,
) -> Option<Item> {
    let rt = state.paths.rt.clone();
    let span = sig.ident.span();
    let name = ident_str(&sig.ident);
    let owner_name = owner.as_ref().map(|(n, _)| n.clone()).unwrap_or_default();
    let twin_name = if owner_name.is_empty() {
        format_ident!("__dyncov_spec_{}", name, span = span)
    } else {
        format_ident!("__dyncov_spec_{}_{}", owner_name, name, span = span)
    };
    let mut env = Env::default();
    let mut binds = vec![];
    let mut arity = 0;
    let mut params: Vec<String> = vec![];
    for arg in sig.inputs.iter() {
        let pname = match &arg.kind {
            FnArgKind::Receiver(_) => Some("self".to_string()),
            FnArgKind::Typed(pt) => closure_binder(&pt.pat),
        };
        params.push(match &arg.kind {
            FnArgKind::Receiver(_) => "Self".to_string(),
            FnArgKind::Typed(pt) => type_last_segment(&pt.ty),
        });
        if let Some(pname) = pname {
            let id = dyn_ident(&pname, span);
            binds.push(quote_spanned!(span => let #id = __dc_args[#arity].clone();));
            env.vars.insert(pname, quote!(#id.clone()));
        }
        arity += 1;
    }
    let body = if is_external_body(attrs) {
        quote_spanned!(span => #rt::Dyn::Unknown("external_body spec fn"))
    } else {
        let lower = Lower { paths: &state.paths, self_ty: owner.clone() };
        lower.block(block, &env)
    };
    let is_view = matches!(state.impl_trait.as_deref(), Some("View") | Some("DeepView"))
        && (name == "view" || name == "deep_view");
    let cfgs: Vec<&Attribute> = attrs.iter().filter(|a| a.path().is_ident("cfg")).collect();
    let item = quote_spanned!(span =>
        #(#cfgs)*
        #[doc(hidden)]
        #[allow(non_snake_case, unused_variables, unused_mut, unreachable_code, unused_parens, clippy::all)]
        fn #twin_name(__dc_args: &[#rt::Dyn]) -> #rt::Dyn {
            if __dc_args.len() != #arity { return #rt::Dyn::Unknown("arity"); }
            #(#binds)*
            #body
        }
    );
    if cfgs.is_empty() {
        state.entries.push((owner_name, name, arity, quote!(#twin_name), is_view, params));
    }
    Some(Item::Verbatim(item))
}

/// Twins for the spec functions among module items (called before
/// erasure).
pub(crate) fn twins_for_items(state: &mut State, items: &[Item]) -> Vec<Item> {
    let mut out = vec![];
    if state.mod_depth > 0 {
        return out;
    }
    for item in items {
        if let Item::Fn(ItemFn { sig, block, attrs, semi_token, .. }) = item {
            if is_spec_with_body(sig, semi_token.is_none()) && !is_external(attrs) {
                out.extend(twin(state, sig, block, attrs, None));
            }
        }
    }
    out
}

/// Twins for the spec methods of an impl, as free functions.
pub(crate) fn twins_for_impl(
    state: &mut State,
    self_ty: &Type,
    generics: &Generics,
    items: &[ImplItem],
) -> Vec<Item> {
    let mut out = vec![];
    if state.mod_depth > 0 {
        return out;
    }
    let Some(name) = self_type_name(self_ty) else { return out };
    let nameable = generics.params.is_empty();
    let owner = Some((name, nameable.then(|| self_ty.to_token_stream())));
    for item in items {
        if let ImplItem::Fn(f) = item {
            if is_spec_with_body(&f.sig, f.semi_token.is_none()) && !is_external(&f.attrs) {
                out.extend(twin(state, &f.sig, &f.block, &f.attrs, owner.clone()));
            }
        }
    }
    out
}

/// The last path segment of a parameter type, through references; `""`
/// for anything else (tuples, closures, ...)
fn type_last_segment(ty: &Type) -> String {
    match ty {
        Type::Path(tp) => {
            let Some(seg) = tp.path.segments.last() else { return String::new() };
            let name = ident_str(&seg.ident);
            // `Seq<T>`: the element type tells same-named functions apart
            if let verus_syn::PathArguments::AngleBracketed(args) = &seg.arguments {
                if let (Some(verus_syn::GenericArgument::Type(inner)), 1) =
                    (args.args.first(), args.args.len())
                {
                    let inner = type_last_segment(inner);
                    if !inner.is_empty() {
                        return format!("{name}<{inner}>");
                    }
                }
            }
            name
        }
        Type::Reference(r) => type_last_segment(&r.elem),
        Type::Paren(p) => type_last_segment(&p.elem),
        _ => String::new(),
    }
}

pub(crate) fn self_type_name(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(tp) => tp.path.segments.last().map(|s| ident_str(&s.ident)),
        Type::Reference(r) => self_type_name(&r.elem),
        Type::Paren(p) => self_type_name(&p.elem),
        _ => None,
    }
}

/// `impl DynView for T` for a struct or enum of the block.
pub(crate) fn view_impl(state: &State, item: &Item) -> Option<Item> {
    let rt = &state.paths.rt;
    let vstd = &state.paths.vstd;
    let (attrs, ident, generics, body) = match item {
        Item::Struct(ItemStruct { attrs, ident, generics, fields, .. }) => {
            let (pat, values) = fields_pattern(fields, ident, None, vstd);
            let body = quote! {
                let #pat = self;
                #rt::Dyn::adt(::core::any::type_name::<Self>(), "", vec![#(#values),*])
            };
            (attrs, ident, generics, body)
        }
        Item::Enum(ItemEnum { attrs, ident, generics, variants, .. }) => {
            let arms: Vec<TokenStream> = variants
                .iter()
                .map(|v| {
                    let (pat, values) = fields_pattern(&v.fields, ident, Some(&v.ident), vstd);
                    let vname = ident_str(&v.ident);
                    quote! { #pat => #rt::Dyn::adt(::core::any::type_name::<Self>(), #vname, vec![#(#values),*]), }
                })
                .collect();
            let body = if arms.is_empty() {
                quote! { match *self {} }
            } else {
                quote! { match self { #(#arms)* } }
            };
            (attrs, ident, generics, body)
        }
        _ => return None,
    };
    let cfgs: Vec<&Attribute> = attrs.iter().filter(|a| a.path().is_ident("cfg")).collect();
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let span = ident.span();
    Some(Item::Verbatim(quote_spanned!(span =>
        #(#cfgs)*
        #[automatically_derived]
        #[allow(unused_variables, non_shorthand_field_patterns, clippy::all)]
        impl #impl_generics #rt::DynView for #ident #ty_generics #where_clause {
            fn dyn_view(&self) -> #rt::Dyn {
                #rt::tick();
                #body
            }
        }
    )))
}

fn fields_pattern(
    fields: &Fields,
    ty: &Ident,
    variant: Option<&Ident>,
    vstd: &TokenStream,
) -> (TokenStream, Vec<TokenStream>) {
    let path = match variant {
        Some(v) => quote!(#ty::#v),
        None => quote!(#ty),
    };
    match fields {
        Fields::Named(named) => {
            let names: Vec<&Ident> = named.named.iter().filter_map(|f| f.ident.as_ref()).collect();
            let values = names
                .iter()
                .map(|n| {
                    let s = ident_str(n);
                    quote!((#s, #vstd::dyncov_view!(#n)))
                })
                .collect();
            (quote!(#path { #(#names),* }), values)
        }
        Fields::Unnamed(unnamed) => {
            let names: Vec<Ident> =
                (0..unnamed.unnamed.len()).map(|i| format_ident!("__dc_f{}", i)).collect();
            let values = names
                .iter()
                .enumerate()
                .map(|(i, n)| {
                    let s = i.to_string();
                    quote!((#s, #vstd::dyncov_view!(#n)))
                })
                .collect();
            (quote!(#path(#(#names),*)), values)
        }
        Fields::Unit => (quote!(#path), vec![]),
    }
}
