//! Dynamic verified coverage (`verus --dyncov`).
//!
//! `verus --dyncov` compiles a crate as `--compile` does, with `--cfg
//! verus_dyncov` on the erase-and-compile pass. In that pass this module
//! preprocesses every `verus!` block before the macro erases its ghost
//! code:
//!
//! - every exec function is wrapped: on entry it registers a frame with the
//!   runtime (`vstd::dyncov`, the `verus_dyncov` crate re-exported by the
//!   fork's vstd) and evaluates its `requires` on the real arguments; an
//!   `external_body` function also evaluates its `ensures` on the result;
//! - every spec function with a body gets an exec twin, `exec_<name>`, next
//!   to it, reachable from other modules as `<name>::__dyncov` (a module
//!   with the spec fn's name re-exports the twin, so that a `use` of the
//!   spec fn brings the twin along);
//! - every struct and enum gets an exec model: itself, when it is exec
//!   data, or a mirror with exec fields when it is spec-only.
//!
//! The lowering of spec code to exec code is the `exec_spec` engine of
//! verus-spec-check (vendored in `dependencies/verus-spec-check`), in its
//! dyncov flavor; each contract clause is lowered as a synthetic spec
//! function of the parameters it mentions. Whatever the engine cannot
//! lower becomes `Unknown` at run time: an unsupported clause is recorded
//! as such, and a spec fn without a lowering gets a twin that panics (the
//! runtime catches it). Generated code that fails to type-check is a
//! compile error of the instrumented build; see `verus-reach --dynamic`
//! for how the profiles are read.

use crate::{EraseGhost, VstdKind};
use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use quote::{ToTokens, format_ident, quote, quote_spanned};
use std::collections::HashSet;
use verus_spec_check_exec_spec as engine;
use verus_syn::spanned::Spanned;
use verus_syn::visit::Visit;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{
    Attribute, Block, DataMode, Expr, ExprCall, ExprPath, Fields, FnArgKind, FnMode,
    GenericArgument, GenericParam, Ident, ImplItem, Item, ItemEnum, ItemFn, ItemImpl, ItemStruct,
    Meta, Pat, PathArguments, ReturnType, Signature, Stmt, TraitItem, Type, Visibility,
};

/// Dynamic coverage is a variant of the erase mode of a user crate: vstd's
/// own code is not instrumented (it is not part of a user crate's report).
pub(crate) fn active() -> bool {
    crate::cfg_dyncov()
        && crate::cfg_erase() == EraseGhost::Erase
        && matches!(crate::vstd_kind(), VstdKind::Imported)
}

/// Instruments the items of one `verus!` block (or of one module in it).
pub(crate) fn preprocess_items(items: &mut Vec<Item>) {
    if !active() {
        return;
    }
    let mut pass = Pass { extra: Vec::new(), counter: 0 };
    pass.run(items);
    if !pass.extra.is_empty() {
        // The method traits of the runtime, anonymously, so that nothing
        // the module names is shadowed
        items.push(Item::Verbatim(quote! {
            #[allow(unused_imports)]
            use ::vstd::dyncov::prelude::*;
        }));
    }
    items.extend(pass.extra);
}

struct Pass {
    /// Generated items, appended after the block's own
    extra: Vec<Item>,
    /// Makes the synthetic clause functions' names unique
    counter: usize,
}

fn is_spec(mode: &FnMode) -> bool {
    matches!(mode, FnMode::Spec(_) | FnMode::SpecChecked(_))
}

fn is_exec(mode: &FnMode) -> bool {
    matches!(mode, FnMode::Default | FnMode::Exec(_))
}

/// `#[verifier::external]` / `#[verifier::external_body]` (and the
/// `verifier(...)` spellings).
fn external_attr(attrs: &[Attribute], which: &str) -> bool {
    attrs.iter().any(|attr| {
        let segs: Vec<String> = attr.path().segments.iter().map(|s| s.ident.to_string()).collect();
        (segs.len() == 2 && segs[0] == "verifier" && segs[1] == which)
            || (segs.len() == 1
                && (segs[0] == "verifier" || segs[0] == "verus_verify")
                && match &attr.meta {
                    Meta::List(list) => list.tokens.to_string() == which,
                    _ => false,
                })
    })
}

/// The line a span starts on, for the function ids and the clause records
/// (0 outside a proc-macro invocation, i.e. in unit tests).
fn line_of(span: Span) -> u32 {
    if proc_macro::is_available() { span.unwrap().line() as u32 } else { 0 }
}

/// Whether `VERUS_DYNCOV_DISABLE` (set by `verus --dyncov` on a retry after
/// a compile error in lowered code) names a location inside the source
/// span of an item: `file:line,file:line,...` as rustc reports them.
fn disabled(spans: &[Span]) -> bool {
    if !proc_macro::is_available() {
        return false;
    }
    let Ok(list) = std::env::var("VERUS_DYNCOV_DISABLE") else { return false };
    if list.is_empty() {
        return false;
    }
    let first = spans.first().map(|s| s.unwrap());
    let Some(first) = first else { return false };
    let Some(file) = first.local_file() else { return false };
    let file = file.to_string_lossy().into_owned();
    let start = spans.iter().map(|s| s.unwrap().line()).min().unwrap_or(0);
    let end = spans.iter().map(|s| s.unwrap().end().line()).max().unwrap_or(0);
    list.split(',').any(|entry| {
        let Some((f, l)) = entry.rsplit_once(':') else { return false };
        let Ok(l) = l.parse::<usize>() else { return false };
        let same_file =
            f == file || file.ends_with(&format!("/{f}")) || f.ends_with(&format!("/{file}"));
        same_file && start <= l && l <= end
    })
}

/// The engine emits paths into the verus-spec-check runtime and names spec
/// fn twins `exec_<name>`; the dyncov runtime hosts the same vocabulary,
/// and twins are reached through their shim module so that a `use` of the
/// spec fn suffices:
/// - `::verus_spec_check::X` → `::vstd::dyncov::rt::X`
/// - `::verus_spec_check_vstd_ext::X` → `::vstd::dyncov::vstd_ext::X`
/// - a call `exec_f(..)` / `m::exec_f(..)` → `f::__dyncov(..)` / `m::f::__dyncov(..)`
///   (a method `.exec_f(..)`, an associated `Type::exec_f` or a definition
///   `fn exec_f` is left alone).
fn rewrite_tokens(ts: TokenStream) -> TokenStream {
    let tokens: Vec<TokenTree> = ts.into_iter().collect();
    let mut out: Vec<TokenTree> = Vec::with_capacity(tokens.len());
    let mut i = 0;
    while i < tokens.len() {
        let tt = &tokens[i];
        // `:: verus_spec_check ::` (two joint ':' puncts, then the ident)
        if let TokenTree::Punct(p0) = tt {
            if p0.as_char() == ':' && i + 2 < tokens.len() {
                if let (TokenTree::Punct(p1), TokenTree::Ident(id)) =
                    (&tokens[i + 1], &tokens[i + 2])
                {
                    if p1.as_char() == ':' {
                        let replacement = match id.to_string().as_str() {
                            "verus_spec_check" => Some(quote! { ::vstd::dyncov::rt }),
                            "verus_spec_check_vstd_ext" => {
                                Some(quote! { ::vstd::dyncov::vstd_ext })
                            }
                            _ => None,
                        };
                        if let Some(r) = replacement {
                            out.extend(r);
                            i += 3;
                            continue;
                        }
                    }
                }
            }
        }
        if let TokenTree::Ident(id) = tt {
            let name = id.to_string();
            if let Some(base) = name.strip_prefix("exec_") {
                let is_call = matches!(tokens.get(i + 1), Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis);
                let lowercase = base.chars().next().is_some_and(|c| c.is_lowercase() || c == '_');
                let synthetic = base.starts_with("__dc_");
                // What precedes: `.` (a method), `fn` (a definition), or
                // `::` after an uppercase ident or `Self` (an associated fn)
                let mut skip = false;
                if let Some(prev) = out.last() {
                    match prev {
                        TokenTree::Punct(p) if p.as_char() == '.' => skip = true,
                        TokenTree::Ident(p) if p == "fn" => skip = true,
                        TokenTree::Punct(p) if p.as_char() == ':' => {
                            if out.len() >= 3 {
                                if let TokenTree::Ident(q) = &out[out.len() - 3] {
                                    let qs = q.to_string();
                                    if qs == "Self"
                                        || qs.chars().next().is_some_and(|c| c.is_uppercase())
                                    {
                                        skip = true;
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
                if is_call && lowercase && !synthetic && !skip {
                    let base_id = Ident::new(base, id.span());
                    out.extend(quote_spanned! { id.span() => #base_id::__dyncov });
                    i += 1;
                    continue;
                }
            }
        }
        match tt {
            TokenTree::Group(g) => {
                let mut ng = Group::new(g.delimiter(), rewrite_tokens(g.stream()));
                ng.set_span(g.span());
                out.push(TokenTree::Group(ng));
            }
            other => out.push(other.clone()),
        }
        i += 1;
    }
    out.into_iter().collect()
}

/// Whether a field type is spec-only: the struct or enum then has no
/// runtime values of its own and gets a mirror with exec fields.
fn spec_only_type(ty: &Type) -> bool {
    // A ghost field is erased; the type around it is exec data
    if matches!(path_name(ty).as_deref(), Some("Ghost") | Some("Tracked")) {
        return false;
    }
    let text = ty.to_token_stream().to_string();
    let mut idents = text.split(|c: char| !(c.is_alphanumeric() || c == '_'));
    idents.any(|w| {
        matches!(
            w,
            "Seq"
                | "Set"
                | "Map"
                | "Multiset"
                | "int"
                | "nat"
                | "real"
                | "Ghost"
                | "Tracked"
                | "FnSpec"
                | "spec_fn"
                | "SpecString"
        )
    })
}

/// The spec type an exec value of type `ty` has in a contract: references
/// and boxes are transparent, `Vec`/slices/arrays/`String` are sequences,
/// hash collections are maps and sets. `None` for ghost or unsupported
/// types.
fn spec_ty(ty: &Type) -> Option<Type> {
    match ty {
        Type::Reference(r) => spec_ty(&r.elem),
        Type::Paren(p) => spec_ty(&p.elem),
        Type::Group(g) => spec_ty(&g.elem),
        Type::Slice(s) => {
            let e = spec_ty(&s.elem)?;
            Some(verus_syn::parse_quote! { Seq<#e> })
        }
        Type::Array(a) => {
            let e = spec_ty(&a.elem)?;
            Some(verus_syn::parse_quote! { Seq<#e> })
        }
        Type::Tuple(t) => {
            let elems = t.elems.iter().map(spec_ty).collect::<Option<Vec<_>>>()?;
            Some(verus_syn::parse_quote! { (#(#elems,)*) })
        }
        Type::Path(tp) => {
            if tp.qself.is_some() {
                return None;
            }
            let last = tp.path.segments.last()?;
            let name = last.ident.to_string();
            let args: Vec<&Type> = match &last.arguments {
                PathArguments::AngleBracketed(ab) => ab
                    .args
                    .iter()
                    .filter_map(|a| match a {
                        GenericArgument::Type(t) => Some(t),
                        _ => None,
                    })
                    .collect(),
                PathArguments::None => vec![],
                PathArguments::Parenthesized(_) => return None,
            };
            let single = tp.path.segments.len() == 1;
            match name.as_str() {
                "Ghost" | "Tracked" => None,
                "Vec" | "VecDeque" if args.len() == 1 => {
                    let e = spec_ty(args[0])?;
                    Some(verus_syn::parse_quote! { Seq<#e> })
                }
                "String" | "str" if single => Some(verus_syn::parse_quote! { Seq<char> }),
                "Box" | "Rc" | "Arc" if args.len() == 1 => spec_ty(args[0]),
                "HashMap" | "BTreeMap" if args.len() == 2 => {
                    let k = spec_ty(args[0])?;
                    let v = spec_ty(args[1])?;
                    Some(verus_syn::parse_quote! { Map<#k, #v> })
                }
                "HashSet" | "BTreeSet" if args.len() == 1 => {
                    let e = spec_ty(args[0])?;
                    Some(verus_syn::parse_quote! { Set<#e> })
                }
                _ => {
                    // Any other path: keep it, mapping its type arguments
                    if args.is_empty() {
                        Some(ty.clone())
                    } else {
                        let mapped = args.iter().map(|a| spec_ty(a)).collect::<Option<Vec<_>>>()?;
                        let mut path = tp.path.clone();
                        let last = path.segments.last_mut().unwrap();
                        last.arguments = PathArguments::AngleBracketed(
                            verus_syn::parse_quote! { <#(#mapped),*> },
                        );
                        Some(Type::Path(verus_syn::TypePath { qself: None, path }))
                    }
                }
            }
        }
        _ => None,
    }
}

fn is_primitive_name(name: &str) -> bool {
    matches!(
        name,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "bool"
            | "char"
            | "f32"
            | "f64"
    )
}

/// An expression converting `value` (a place of type `ty`) to the borrowed
/// exec form the twin of a synthetic clause takes for `spec_ty(ty)`.
fn arg_expr(ty: &Type, value: TokenStream) -> TokenStream {
    // A sequence of chars is a string's view: the twin takes `&str`
    fn is_char_seq(inner: &Type) -> bool {
        match inner {
            Type::Slice(s) => path_name(&s.elem).as_deref() == Some("char"),
            Type::Path(_) if path_name(inner).as_deref() == Some("Vec") => {
                match inner {
                    Type::Path(tp) => match &tp.path.segments.last().unwrap().arguments {
                        PathArguments::AngleBracketed(ab) => ab.args.iter().any(|a| {
                            matches!(a, GenericArgument::Type(t) if path_name(t).as_deref() == Some("char"))
                        }),
                        _ => false,
                    },
                    _ => false,
                }
            }
            _ => false,
        }
    }
    let inner_of_ref: Option<&Type> = match ty {
        Type::Reference(r) => Some(&r.elem),
        _ => None,
    };
    if is_char_seq(inner_of_ref.unwrap_or(ty)) {
        return quote! { (&(#value).iter().collect::<::std::string::String>()).as_str() };
    }
    // Ordered collections view as hash collections
    match path_name(inner_of_ref.unwrap_or(ty)).as_deref() {
        Some("BTreeMap") => {
            return quote! { (&(#value).iter().map(|(k, v)| (::core::clone::Clone::clone(k), ::core::clone::Clone::clone(v))).collect::<::std::collections::HashMap<_, _>>()) };
        }
        Some("BTreeSet") => {
            return quote! { (&(#value).iter().cloned().collect::<::std::collections::HashSet<_>>()) };
        }
        _ => {}
    }
    match ty {
        Type::Reference(r) => {
            let inner: &Type = &r.elem;
            let mutable = r.mutability.is_some();
            match inner {
                Type::Slice(_) | Type::Path(_)
                    if matches!(inner, Type::Slice(_))
                        || path_name(inner).as_deref() == Some("str") =>
                {
                    if mutable {
                        quote! { (&*#value) }
                    } else {
                        quote! { (#value) }
                    }
                }
                Type::Array(_) => quote! { (&#value[..]) },
                Type::Path(_) => match path_name(inner).as_deref() {
                    Some("Vec") => quote! { (#value).as_slice() },
                    Some("String") => quote! { (#value).as_str() },
                    Some("Box") | Some("Rc") | Some("Arc") => quote! { (&**#value) },
                    Some("VecDeque") => {
                        quote! { ::vstd::dyncov::rt::__vcheck_vecdeque_slice(#value).as_slice() }
                    }
                    Some(n) if is_primitive_name(n) => quote! { (*#value) },
                    _ => {
                        if mutable {
                            quote! { (&*#value) }
                        } else {
                            quote! { (#value) }
                        }
                    }
                },
                _ => {
                    if mutable {
                        quote! { (&*#value) }
                    } else {
                        quote! { (#value) }
                    }
                }
            }
        }
        Type::Paren(p) => arg_expr(&p.elem, value),
        Type::Group(g) => arg_expr(&g.elem, value),
        Type::Array(_) => quote! { (&#value[..]) },
        Type::Path(_) => match path_name(ty).as_deref() {
            Some("Vec") => quote! { (#value).as_slice() },
            Some("String") => quote! { (#value).as_str() },
            Some("Box") | Some("Rc") | Some("Arc") => quote! { (&*#value) },
            Some("VecDeque") => {
                quote! { ::vstd::dyncov::rt::__vcheck_vecdeque_slice(&#value).as_slice() }
            }
            Some(n) if is_primitive_name(n) => quote! { (#value) },
            _ => quote! { (&#value) },
        },
        _ => quote! { (&#value) },
    }
}

fn path_name(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(tp) => tp.path.segments.last().map(|s| s.ident.to_string()),
        _ => None,
    }
}

/// The idents an expression mentions (single-segment paths), for finding
/// which parameters a clause uses.
fn mentioned_idents(expr: &Expr) -> HashSet<String> {
    struct V(HashSet<String>);
    impl<'a> Visit<'a> for V {
        fn visit_expr_path(&mut self, p: &'a ExprPath) {
            if p.qself.is_none() && p.path.leading_colon.is_none() {
                if let Some(first) = p.path.segments.first() {
                    self.0.insert(first.ident.to_string());
                }
            }
            verus_syn::visit::visit_expr_path(self, p);
        }
    }
    let mut v = V(HashSet::new());
    v.visit_expr(expr);
    v.0
}

fn type_mentions(ty: &Type, names: &HashSet<String>) -> bool {
    struct V<'a>(&'a HashSet<String>, bool);
    impl<'a, 'b> Visit<'b> for V<'a> {
        fn visit_path_segment(&mut self, s: &'b verus_syn::PathSegment) {
            if self.0.contains(&s.ident.to_string()) {
                self.1 = true;
            }
            verus_syn::visit::visit_path_segment(self, s);
        }
    }
    let mut v = V(names, false);
    v.visit_type(ty);
    v.1
}

/// `self` → `__self` and `old(p)` → `__old_p` (when a snapshot of `p` was
/// taken, else `p`: in a `requires`, `old(p)` is the value on entry), so
/// that a clause is an expression over plain parameters.
fn normalize_clause(expr: &mut Expr, snapshotted: &HashSet<String>) {
    struct R<'a>(&'a HashSet<String>);
    impl<'a> VisitMut for R<'a> {
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            // `final(p)` is the post-state of `p`, which a bare `p` denotes
            // in the lowered clause
            if let Expr::Final(f) = e {
                let inner = (*f.arg).clone();
                *e = inner;
            }
            if let Expr::Call(ExprCall { func, args, .. }) = e {
                if let Expr::Path(p) = func.as_ref() {
                    if p.path.is_ident("old") && args.len() == 1 {
                        if let Expr::Path(arg) = &args[0] {
                            if arg.path.segments.len() == 1 {
                                let name = &arg.path.segments[0].ident;
                                let alias = if self.0.contains(&name.to_string()) {
                                    format_ident!("__old_{}", name)
                                } else if name == "self" {
                                    Ident::new("__self", name.span())
                                } else {
                                    name.clone()
                                };
                                *e = verus_syn::parse_quote! { #alias };
                                return;
                            }
                        }
                    }
                }
            }
            verus_syn::visit_mut::visit_expr_mut(self, e);
        }
        fn visit_expr_path_mut(&mut self, p: &mut ExprPath) {
            for seg in p.path.segments.iter_mut() {
                if seg.ident == "self" {
                    seg.ident = Ident::new("__self", seg.ident.span());
                }
            }
            verus_syn::visit_mut::visit_expr_path_mut(self, p);
        }
    }
    R(snapshotted).visit_expr_mut(expr);
}

/// The exec type of a field of a spec-only type: sequences are vectors,
/// sets and maps hash collections, math integers `i128`.
fn exec_field_ty(ty: &Type) -> Type {
    match ty {
        Type::Paren(p) => exec_field_ty(&p.elem),
        Type::Group(g) => exec_field_ty(&g.elem),
        Type::Tuple(t) => {
            let elems: Vec<Type> = t.elems.iter().map(exec_field_ty).collect();
            verus_syn::parse_quote! { (#(#elems,)*) }
        }
        Type::Path(tp) if tp.qself.is_none() => {
            let last = tp.path.segments.last().unwrap();
            let name = last.ident.to_string();
            let args: Vec<Type> = match &last.arguments {
                PathArguments::AngleBracketed(ab) => ab
                    .args
                    .iter()
                    .filter_map(|a| match a {
                        GenericArgument::Type(t) => Some(exec_field_ty(t)),
                        _ => None,
                    })
                    .collect(),
                _ => vec![],
            };
            let single = tp.path.segments.len() == 1;
            match name.as_str() {
                "Seq" if args.len() == 1 => {
                    let e = &args[0];
                    if matches!(e, Type::Path(tp) if tp.path.is_ident("char")) {
                        verus_syn::parse_quote! { ::std::string::String }
                    } else {
                        verus_syn::parse_quote! { ::std::vec::Vec<#e> }
                    }
                }
                "SpecString" if single => verus_syn::parse_quote! { ::std::string::String },
                "Set" if args.len() == 1 => {
                    let e = &args[0];
                    verus_syn::parse_quote! { ::std::collections::HashSet<#e> }
                }
                "Map" if args.len() == 2 => {
                    let (k, v) = (&args[0], &args[1]);
                    verus_syn::parse_quote! { ::std::collections::HashMap<#k, #v> }
                }
                "Multiset" if args.len() == 1 => {
                    let e = &args[0];
                    verus_syn::parse_quote! { ::vstd::dyncov::vstd_ext::ExecMultiset<#e> }
                }
                "int" | "nat" if single => verus_syn::parse_quote! { i128 },
                "real" if single => verus_syn::parse_quote! { f64 },
                _ => {
                    if args.is_empty() {
                        ty.clone()
                    } else {
                        let mut path = tp.path.clone();
                        let last = path.segments.last_mut().unwrap();
                        last.arguments =
                            PathArguments::AngleBracketed(verus_syn::parse_quote! { <#(#args),*> });
                        Type::Path(verus_syn::TypePath { qself: None, path })
                    }
                }
            }
        }
        _ => ty.clone(),
    }
}

/// The names a `#[derive(...)]` of these attributes lists.
fn derived(attrs: &[Attribute]) -> HashSet<String> {
    let mut names = HashSet::new();
    for attr in attrs {
        if attr.path().is_ident("derive") {
            if let Meta::List(list) = &attr.meta {
                for t in list.tokens.clone() {
                    if let TokenTree::Ident(i) = t {
                        names.insert(i.to_string());
                    }
                }
            }
        }
    }
    names
}

/// Lowered code clones values it builds from borrowed parts and compares
/// them structurally: a type declared in `verus!` with no `derive` of its
/// own gets `Clone` and `PartialEq` for the instrumented build (a type
/// that lists derives and leaves these out implements them by hand, as
/// does one with a ghost field; `mirror` is a spec-only type, which has
/// no hand-written impls).
fn ensure_derives(
    attrs: &mut Vec<Attribute>,
    name: &Ident,
    at: Span,
    mirror: bool,
    ghost_field: bool,
) {
    if ghost_field || disabled(&[at]) {
        return;
    }
    let have = derived(attrs);
    let manual = |trait_name: &str| !mirror && impl_in_file(at, trait_name, &name.to_string());
    let mut add: Vec<Ident> = Vec::new();
    if !have.contains("Clone") && !have.contains("Copy") && !manual("Clone") {
        add.push(Ident::new("Clone", at));
    }
    if !have.contains("PartialEq") && !manual("PartialEq") {
        add.push(Ident::new("PartialEq", at));
    }
    if !add.is_empty() {
        attrs.push(verus_syn::parse_quote! { #[derive(#(#add),*)] });
    }
}

/// Whether the source file of `at` has a hand-written `impl <trait> for
/// <name>` (the macro sees one block at a time; the impl may be in another).
fn impl_in_file(at: Span, trait_name: &str, name: &str) -> bool {
    use std::cell::RefCell;
    use std::collections::HashMap;
    thread_local! {
        static FILES: RefCell<HashMap<std::path::PathBuf, String>> = RefCell::new(HashMap::new());
    }
    if !proc_macro::is_available() {
        return false;
    }
    let Some(path) = at.unwrap().local_file() else { return false };
    let text = FILES.with(|f| {
        f.borrow_mut()
            .entry(path.clone())
            .or_insert_with(|| std::fs::read_to_string(&path).unwrap_or_default())
            .clone()
    });
    let needle = format!("{trait_name} for {name}");
    text.match_indices(&needle).any(|(i, _)| {
        let before = &text[..i];
        let after = &text[i + needle.len()..];
        before.trim_end().ends_with("impl")
            || before.trim_end().ends_with('>')
            || after.starts_with(|c: char| !(c.is_alphanumeric() || c == '_'))
                && before.rfind("impl").is_some_and(|j| !before[j..].contains(';'))
    })
}

fn has_ghost_field<'a>(types: impl Iterator<Item = &'a Type>) -> bool {
    types.into_iter().any(|t| matches!(path_name(t).as_deref(), Some("Ghost") | Some("Tracked")))
}

/// Rewrites a spec-only struct, in place, into its exec mirror.
fn mirror_struct(st: &mut ItemStruct) {
    for f in st.fields.iter_mut() {
        f.ty = exec_field_ty(&f.ty);
        f.mode = DataMode::Default;
    }
    st.mode = DataMode::Default;
    st.attrs.retain(|a| !a.path().is_ident("derive"));
    ensure_derives(&mut st.attrs, &st.ident, st.ident.span(), true, false);
}

/// Rewrites a spec-only enum, in place, into its exec mirror.
fn mirror_enum(en: &mut ItemEnum) {
    for v in en.variants.iter_mut() {
        for f in v.fields.iter_mut() {
            f.ty = exec_field_ty(&f.ty);
            f.mode = DataMode::Default;
        }
    }
    en.mode = DataMode::Default;
    en.attrs.retain(|a| !a.path().is_ident("derive"));
    ensure_derives(&mut en.attrs, &en.ident, en.ident.span(), true, false);
}

/// `x is Variant` lowers to `x.exec_is_Variant()`: one predicate per variant.
fn variant_predicates(en: &ItemEnum) -> TokenStream {
    let name = &en.ident;
    let methods = en.variants.iter().map(|v| {
        let variant = &v.ident;
        let method = format_ident!("exec_is_{}", variant);
        let pat = match &v.fields {
            Fields::Named(_) => quote! { #name::#variant { .. } },
            Fields::Unnamed(_) => quote! { #name::#variant(..) },
            Fields::Unit => quote! { #name::#variant },
        };
        quote! {
            #[inline(always)]
            #[allow(non_snake_case, dead_code)]
            pub fn #method(&self) -> bool {
                ::core::matches!(self, #pat)
            }
        }
    });
    quote! {
        #[allow(dead_code)]
        impl #name {
            #(#methods)*
        }
    }
}

/// A parameter as a clause sees it.
struct Param {
    /// Its name in the clause (`__self`, `__old_p`, `r` for the result)
    name: Ident,
    /// Its name as the wrapper mentions it (`p`, `self`, `__dc_ret`)
    exec: TokenStream,
    /// Its exec type, for the conversion to the twin's argument; `None`
    /// for `self`
    ty: Option<Type>,
    /// How the twin receives it, and its spec type; `Err(reason)` when a
    /// clause mentioning it cannot be lowered
    spec: Result<Type, String>,
    /// A snapshot that may have failed: the argument reads through `Option`
    snapshot: bool,
}

impl Pass {
    fn run(&mut self, items: &mut Vec<Item>) {
        // Types first: a spec-only type is replaced by its exec mirror, an
        // enum gets its `is Variant` predicates
        for item in items.iter_mut() {
            match item {
                Item::Struct(st) => {
                    if st.generics.params.is_empty()
                        && !matches!(st.mode, DataMode::Tracked(_))
                        && (matches!(st.mode, DataMode::Ghost(_))
                            || st.fields.iter().any(|f| spec_only_type(&f.ty)))
                    {
                        mirror_struct(st);
                    } else if st.generics.params.is_empty() {
                        let ghost = has_ghost_field(st.fields.iter().map(|f| &f.ty));
                        ensure_derives(&mut st.attrs, &st.ident, st.ident.span(), false, ghost);
                    }
                }
                Item::Enum(en) => {
                    if en.generics.params.is_empty() {
                        if !matches!(en.mode, DataMode::Tracked(_))
                            && (matches!(en.mode, DataMode::Ghost(_))
                                || en
                                    .variants
                                    .iter()
                                    .flat_map(|v| v.fields.iter())
                                    .any(|f| spec_only_type(&f.ty)))
                        {
                            mirror_enum(en);
                        } else {
                            let ghost = has_ghost_field(
                                en.variants.iter().flat_map(|v| v.fields.iter()).map(|f| &f.ty),
                            );
                            ensure_derives(&mut en.attrs, &en.ident, en.ident.span(), false, ghost);
                        }
                        self.push(variant_predicates(en));
                    }
                }
                _ => {}
            }
        }
        for item in items.iter() {
            match item {
                Item::Fn(f) if is_spec(&f.sig.mode) => self.spec_fn_twin(f),
                Item::Impl(imp) => self.impl_spec_twins(imp),
                _ => {}
            }
        }
        for item in items.iter_mut() {
            match item {
                Item::Fn(f) if is_exec(&f.sig.mode) && f.semi_token.is_none() => {
                    if external_attr(&f.attrs, "external") {
                        continue;
                    }
                    let is_main = f.sig.ident == "main" && f.sig.inputs.is_empty();
                    let generics = generic_names(&f.sig.generics, None);
                    self.wrap(&mut f.attrs, &f.vis, &f.sig, &mut f.block, None, &generics, is_main);
                }
                Item::Impl(imp) => {
                    if external_attr(&imp.attrs, "external") {
                        continue;
                    }
                    let self_ty = if imp.generics.params.is_empty() {
                        Some((*imp.self_ty).clone())
                    } else {
                        None
                    };
                    let impl_generics = imp.generics.clone();
                    for ii in imp.items.iter_mut() {
                        if let ImplItem::Fn(m) = ii {
                            if is_exec(&m.sig.mode)
                                && m.semi_token.is_none()
                                && !external_attr(&m.attrs, "external")
                            {
                                let generics = generic_names(&m.sig.generics, Some(&impl_generics));
                                self.wrap(
                                    &mut m.attrs,
                                    &m.vis,
                                    &m.sig,
                                    &mut m.block,
                                    self_ty.as_ref(),
                                    &generics,
                                    false,
                                );
                            }
                        }
                    }
                }
                Item::Trait(tr) => {
                    if external_attr(&tr.attrs, "external") {
                        continue;
                    }
                    for ti in tr.items.iter_mut() {
                        if let TraitItem::Fn(m) = ti {
                            if is_exec(&m.sig.mode) && !external_attr(&m.attrs, "external") {
                                if let Some(block) = m.default.as_mut() {
                                    let generics =
                                        generic_names(&m.sig.generics, Some(&tr.generics));
                                    let vis = Visibility::Inherited;
                                    self.wrap(
                                        &mut m.attrs,
                                        &vis,
                                        &m.sig,
                                        block,
                                        None,
                                        &generics,
                                        false,
                                    );
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn push(&mut self, ts: TokenStream) {
        self.extra.push(Item::Verbatim(ts));
    }

    /// The twin of a free spec fn, and its shim module.
    fn spec_fn_twin(&mut self, f: &ItemFn) {
        if !f.sig.generics.params.is_empty() {
            return;
        }
        let name = &f.sig.ident;
        let exec_name = format_ident!("exec_{}", name);
        let twin = if f.semi_token.is_some() {
            engine::compile_spec_fn_stub_dyncov(&f.sig, &f.vis, None, "uninterpreted")
        } else if disabled(&[f.sig.span(), f.block.span()]) {
            engine::compile_spec_fn_stub_dyncov(
                &f.sig,
                &f.vis,
                None,
                "its lowering does not compile",
            )
        } else {
            match engine::compile_item_dyncov(Item::Fn(f.clone())) {
                Ok(ts) => Ok(ts),
                Err(e) => engine::compile_spec_fn_stub_dyncov(
                    &f.sig,
                    &f.vis,
                    None,
                    &format!("not lowered: {}", e),
                ),
            }
        };
        let Ok(twin) = twin else { return };
        // Every token of the twin carries the spec fn's span, so that a
        // compile error in it is attributed to the spec fn (see `disabled`)
        let twin = engine::respan(twin, f.sig.ident.span());
        let vis = &f.vis;
        let use_vis = match vis {
            Visibility::Inherited => quote! { pub(super) },
            v => quote! { #v },
        };
        let twin = rewrite_tokens(twin);
        self.push(quote! {
            #twin
            #[doc(hidden)]
            #[allow(non_snake_case, unused_imports)]
            #vis mod #name {
                #use_vis use super::#exec_name as __dyncov;
            }
        });
    }

    /// The twins of the spec methods of an impl (inherent or trait), as
    /// inherent methods of the exec model of the type.
    fn impl_spec_twins(&mut self, imp: &ItemImpl) {
        if !imp.generics.params.is_empty() {
            return;
        }
        let self_ident = match imp.self_ty.as_ref() {
            Type::Path(tp) if tp.qself.is_none() && tp.path.segments.len() == 1 => {
                tp.path.segments[0].ident.clone()
            }
            _ => return,
        };
        // The exec model of a type is the type itself
        let exec_self = self_ident.clone();
        for ii in &imp.items {
            let ImplItem::Fn(m) = ii else { continue };
            if !is_spec(&m.sig.mode) || !m.sig.generics.params.is_empty() {
                continue;
            }
            // A trait method is public through the trait; its inherent twin
            // must be too
            let mut method = m.clone();
            if imp.trait_.is_some() {
                method.vis = verus_syn::parse_quote! { pub };
            }
            let one = ItemImpl {
                attrs: vec![],
                trait_: None,
                items: vec![ImplItem::Fn(method.clone())],
                ..imp.clone()
            };
            let m = &method;
            let twin = if m.semi_token.is_some() {
                engine::compile_spec_fn_stub_dyncov(
                    &m.sig,
                    &m.vis,
                    Some(&self_ident),
                    "uninterpreted",
                )
                .map(|ts| quote! { impl #exec_self { #ts } })
            } else if disabled(&[m.sig.span(), m.block.span()]) {
                engine::compile_spec_fn_stub_dyncov(
                    &m.sig,
                    &m.vis,
                    Some(&self_ident),
                    "its lowering does not compile",
                )
                .map(|ts| quote! { impl #exec_self { #ts } })
            } else {
                match engine::compile_item_dyncov(Item::Impl(one)) {
                    Ok(ts) => Ok(ts),
                    Err(e) => engine::compile_spec_fn_stub_dyncov(
                        &m.sig,
                        &m.vis,
                        Some(&self_ident),
                        &format!("not lowered: {}", e),
                    )
                    .map(|ts| quote! { impl #exec_self { #ts } }),
                }
            };
            if let Ok(twin) = twin {
                let twin = engine::respan(twin, m.sig.ident.span());
                self.push(rewrite_tokens(twin));
            }
        }
    }

    /// Lowers one clause as a synthetic spec fn of the parameters it
    /// mentions; returns the code of the clause for the wrapper: a call of
    /// the twin, or the reason it is `Unknown`.
    fn lower_clause(
        &mut self,
        kind: &str,
        fn_name: &Ident,
        index: usize,
        clause: &Expr,
        params: &[Param],
    ) -> Result<TokenStream, String> {
        if disabled(&[clause.span()]) {
            return Err("its lowering does not compile".to_string());
        }
        let mut expr = clause.clone();
        let snapshotted: HashSet<String> = params
            .iter()
            .filter(|p| p.snapshot)
            .filter_map(|p| p.name.to_string().strip_prefix("__old_").map(str::to_string))
            .collect();
        normalize_clause(&mut expr, &snapshotted);
        let used = mentioned_idents(&expr);
        let mut sig_params = Vec::new();
        let mut args = Vec::new();
        let mut snapshots = Vec::new();
        for p in params {
            if !used.contains(&p.name.to_string()) {
                continue;
            }
            let spec = match &p.spec {
                Ok(t) => t,
                Err(reason) => return Err(reason.clone()),
            };
            let name = &p.name;
            sig_params.push(quote! { #name: #spec });
            let value = p.exec.clone();
            let arg = match &p.ty {
                Some(ty) => arg_expr(ty, value),
                None => value,
            };
            args.push(arg);
            if p.snapshot {
                snapshots.push(p.exec.clone());
            }
        }
        self.counter += 1;
        let synth = format_ident!("__dc_{}_{}_{}_{}", kind, fn_name, index, self.counter);
        let exec_synth = format_ident!("exec_{}", synth);
        let span = clause.span();
        let item: ItemFn = match verus_syn::parse2(quote_spanned! { span =>
            spec fn #synth(#(#sig_params),*) -> bool { #expr }
        }) {
            Ok(f) => f,
            Err(e) => return Err(format!("clause does not parse as a spec fn: {e}")),
        };
        let twin = engine::compile_item_dyncov(Item::Fn(item)).map_err(|e| e.to_string())?;
        let twin = engine::respan(twin, span);
        self.push(rewrite_tokens(twin));
        let call = quote! { #exec_synth(#(#args),*) };
        if snapshots.is_empty() {
            Ok(quote! { Ok(#call) })
        } else {
            // A snapshot that could not be taken makes the clause `Unknown`
            let names: Vec<TokenStream> = snapshots.clone();
            Ok(quote! {
                match (#(&#names,)*) {
                    (#(Some(#names),)*) => Ok(#call),
                    _ => Err("snapshot of a parameter failed"),
                }
            })
        }
    }

    /// Wraps an exec function: a frame and the `requires` on entry, and for
    /// an `external_body` function the `ensures` on exit.
    fn wrap(
        &mut self,
        attrs: &mut Vec<Attribute>,
        _vis: &Visibility,
        sig: &Signature,
        block: &mut Block,
        self_ty: Option<&Type>,
        generics: &HashSet<String>,
        is_main: bool,
    ) {
        if sig.constness.is_some()
            || sig.asyncness.is_some()
            || sig.abi.is_some()
            || sig.variadic.is_some()
        {
            return;
        }
        let trusted = external_attr(attrs, "external_body");
        let name = &sig.ident;
        let name_str = name.to_string();
        let line = line_of(sig.fn_token.span);
        let kind = if trusted {
            quote! { Trusted }
        } else {
            quote! { Verified }
        };

        // The parameters as the clauses see them
        let mut params: Vec<Param> = Vec::new();
        let mut unsupported_names: HashSet<String> = HashSet::new();
        let ensures: Vec<Expr> = if trusted {
            sig.spec
                .ensures
                .as_ref()
                .map(|e| e.exprs.exprs.iter().cloned().collect())
                .unwrap_or_default()
        } else {
            vec![]
        };
        let old_params: HashSet<String> = {
            let mut s = HashSet::new();
            for e in &ensures {
                struct V(HashSet<String>);
                impl<'a> Visit<'a> for V {
                    fn visit_expr_call(&mut self, c: &'a ExprCall) {
                        if let Expr::Path(p) = c.func.as_ref() {
                            if p.path.is_ident("old") && c.args.len() == 1 {
                                if let Expr::Path(a) = &c.args[0] {
                                    if a.path.segments.len() == 1 {
                                        self.0.insert(a.path.segments[0].ident.to_string());
                                    }
                                }
                            }
                        }
                        verus_syn::visit::visit_expr_call(self, c);
                    }
                }
                let mut v = V(HashSet::new());
                v.visit_expr(e);
                s.extend(v.0);
            }
            s
        };
        let mut snapshot_stmts: Vec<TokenStream> = Vec::new();
        for arg in &sig.inputs {
            match &arg.kind {
                FnArgKind::Receiver(rcv) => {
                    let spec = match self_ty {
                        Some(t) if arg.tracked.is_none() => Ok(t.clone()),
                        Some(_) => Err("tracked self".to_string()),
                        None => Err("self of a generic impl or a trait".to_string()),
                    };
                    let exec = match (&rcv.reference, &rcv.mutability) {
                        (Some(_), Some(_)) => quote! { (&*self) },
                        (Some(_), None) => quote! { self },
                        (None, _) => quote! { (&self) },
                    };
                    params.push(Param {
                        name: Ident::new("__self", Span::call_site()),
                        exec,
                        ty: None,
                        spec,
                        snapshot: false,
                    });
                }
                FnArgKind::Typed(pt) => {
                    let (ident, ghost_pat) = match pt.pat.as_ref() {
                        Pat::Ident(pi) => (pi.ident.clone(), false),
                        Pat::TupleStruct(ts) if ts.elems.len() == 1 => match ts.elems.first() {
                            Some(Pat::Ident(pi)) => (pi.ident.clone(), true),
                            _ => continue,
                        },
                        _ => continue,
                    };
                    let ghost = ghost_pat
                        || arg.tracked.is_some()
                        || matches!(path_name(&pt.ty).as_deref(), Some("Ghost") | Some("Tracked"));
                    let spec = if ghost {
                        Err(format!("ghost parameter `{ident}`"))
                    } else if type_mentions(&pt.ty, generics) {
                        Err(format!("generic parameter type of `{ident}`"))
                    } else {
                        match spec_ty(&pt.ty) {
                            Some(t) => Ok(t),
                            None => Err(format!("unsupported parameter type of `{ident}`")),
                        }
                    };
                    if spec.is_err() {
                        unsupported_names.insert(ident.to_string());
                    }
                    // `old(p)` of a `&mut` parameter: a clone taken on entry
                    if old_params.contains(&ident.to_string()) {
                        let old_name = format_ident!("__old_{}", ident);
                        let snap = format_ident!("__dc_old_{}", ident);
                        let inner_ty: Type = match pt.ty.as_ref() {
                            Type::Reference(r) => (*r.elem).clone(),
                            t => t.clone(),
                        };
                        snapshot_stmts.push(quote! {
                            let #snap: ::core::option::Option<#inner_ty> =
                                ::vstd::dyncov::snapshot(|| ::core::clone::Clone::clone(&*#ident));
                        });
                        let ref_ty: Type = verus_syn::parse_quote! { &#inner_ty };
                        params.push(Param {
                            name: old_name,
                            exec: quote! { #snap },
                            ty: Some(ref_ty),
                            spec: spec.clone(),
                            snapshot: true,
                        });
                    }
                    params.push(Param {
                        name: ident.clone(),
                        exec: quote! { #ident },
                        ty: Some((*pt.ty).clone()),
                        spec,
                        snapshot: false,
                    });
                }
            }
        }
        // The result, for `ensures`
        let (ret_ident, ret_ty): (Option<Ident>, Option<Type>) = match &sig.output {
            ReturnType::Default => (None, None),
            ReturnType::Type(_, _, pat, ty) => {
                let ident = pat.as_ref().and_then(|p| match &p.1 {
                    Pat::Ident(pi) => Some(pi.ident.clone()),
                    _ => None,
                });
                (ident, Some((**ty).clone()))
            }
        };
        if trusted {
            if let (Some(r), Some(ty)) = (&ret_ident, &ret_ty) {
                let spec = if type_mentions(ty, generics) {
                    Err("generic return type".to_string())
                } else {
                    spec_ty(ty).ok_or_else(|| "unsupported return type".to_string())
                };
                params.push(Param {
                    name: r.clone(),
                    exec: quote! { __dc_ret },
                    ty: Some(ty.clone()),
                    spec,
                    snapshot: false,
                });
            }
        }

        // Clauses
        let requires: Vec<Expr> = sig
            .spec
            .requires
            .as_ref()
            .map(|r| r.exprs.exprs.iter().cloned().collect())
            .unwrap_or_default();
        let lowered = |this: &mut Pass, kind: &str, clauses: &[Expr]| -> Vec<TokenStream> {
            clauses
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    let line = line_of(c.span());
                    let body = match this.lower_clause(kind, name, i, c, &params) {
                        Ok(call) => call,
                        Err(reason) => {
                            let reason = format!("not lowered: {reason}");
                            quote! { Err(#reason) }
                        }
                    };
                    quote! { (#line, &|| -> ::vstd::dyncov::Clause { #body }) }
                })
                .collect()
        };
        let pre_clauses = lowered(self, "req", &requires);
        let post_clauses = if trusted { lowered(self, "ens", &ensures) } else { vec![] };

        let flush = if is_main {
            quote! { let __dc_flush = ::vstd::dyncov::FlushOnExit; }
        } else {
            quote! {}
        };
        let pre = if pre_clauses.is_empty() {
            quote! {}
        } else {
            quote! {
                ::vstd::dyncov::pre(
                    &__dc_guard,
                    ::vstd::dyncov::eval(&[#(#pre_clauses),*]),
                    ::core::panic::Location::caller(),
                );
            }
        };
        let prelude = quote! {
            #flush
            let __dc_guard = ::vstd::dyncov::enter(
                ::vstd::dyncov::FnId { file: ::core::file!(), line: #line, name: #name_str },
                ::vstd::dyncov::Kind::#kind,
            );
            #pre
            #(#snapshot_stmts)*
        };
        if !is_main && !attrs.iter().any(|a| a.path().is_ident("track_caller")) {
            attrs.push(verus_syn::parse_quote! { #[track_caller] });
        }
        let prelude_stmt = Stmt::Expr(Expr::Verbatim(prelude), None);
        if trusted && !post_clauses.is_empty() {
            // The body runs as a closure so that its result can be checked
            let stmts = std::mem::take(&mut block.stmts);
            let inner = Block { brace_token: block.brace_token, stmts };
            let ret_annot = match &ret_ty {
                Some(t) if !t.to_token_stream().to_string().contains("impl ") => quote! { -> #t },
                Some(_) => quote! {},
                None => quote! { -> () },
            };
            let call: Stmt = verus_syn::parse_quote! {
                let __dc_ret = (|| #ret_annot #inner)();
            };
            let post = Stmt::Expr(
                Expr::Verbatim(quote! {
                    ::vstd::dyncov::trusted_post(
                        &__dc_guard,
                        ::vstd::dyncov::eval(&[#(#post_clauses),*]),
                    );
                }),
                None,
            );
            let result = Stmt::Expr(verus_syn::parse_quote! { __dc_ret }, None);
            block.stmts = vec![prelude_stmt, call, post, result];
        } else {
            block.stmts.insert(0, prelude_stmt);
        }
        let _ = unsupported_names;
    }
}

/// The names of the type parameters in scope of a function.
fn generic_names(
    sig: &verus_syn::Generics,
    outer: Option<&verus_syn::Generics>,
) -> HashSet<String> {
    let mut names = HashSet::new();
    for g in sig.params.iter().chain(outer.iter().flat_map(|o| o.params.iter())) {
        if let GenericParam::Type(t) = g {
            names.insert(t.ident.to_string());
        }
    }
    names
}

#[allow(dead_code)]
fn _unused(_: &ItemStruct, _: &ItemEnum, _: &Fields) {}
