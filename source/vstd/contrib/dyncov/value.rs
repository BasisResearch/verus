//! The dynamic value model that lowered contracts evaluate over.
//!
//! Lowering is syntactic (a proc macro sees tokens, not types), so the
//! lowered code cannot be typed. Instead every exec value in scope is
//! converted to a [`Dyn`] value with [`DynView`], and every spec operation
//! is a total function on [`Dyn`] that returns [`Dyn::Unknown`] when it
//! does not apply. An `Unknown` operand makes the result `Unknown`, except
//! for the three-valued connectives, where a `False` operand decides.
//!
//! `int` and `nat` are `i128` with checked arithmetic; an overflow is
//! `Unknown`. `Seq`, `Set`, `Map` are vectors (a set is deduplicated by
//! [`equals`]). A struct or enum the `verus!` macro has seen is an [`Adt`]
//! with named fields; any other value is [`Opaque`] and supports only
//! equality, and only if the type implements `PartialEq`.

use std::any::Any;
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::rc::Rc;

/// The outcome of evaluating a lowered spec expression.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Verdict {
    True,
    Unknown,
    False,
}

impl Verdict {
    pub fn index(self) -> usize {
        match self {
            Verdict::True => 0,
            Verdict::Unknown => 1,
            Verdict::False => 2,
        }
    }

    /// Three-valued conjunction: `False` decides, otherwise `Unknown` taints.
    pub fn and(self, other: Verdict) -> Verdict {
        match (self, other) {
            (Verdict::False, _) | (_, Verdict::False) => Verdict::False,
            (Verdict::Unknown, _) | (_, Verdict::Unknown) => Verdict::Unknown,
            _ => Verdict::True,
        }
    }
}

#[derive(Clone)]
pub enum Dyn {
    /// Could not be computed; the payload says why.
    Unknown(&'static str),
    Unit,
    Bool(bool),
    Int(i128),
    Char(char),
    Float(f64),
    /// A `String`/`str` value: `Seq<char>` in spec.
    Str(Rc<str>),
    Seq(Rc<Vec<Dyn>>),
    /// Deduplicated by [`equals`]
    Set(Rc<Vec<Dyn>>),
    /// Keys deduplicated by [`equals`]
    Map(Rc<Vec<(Dyn, Dyn)>>),
    Tuple(Rc<Vec<Dyn>>),
    Adt(Rc<Adt>),
    Opaque(Rc<Opaque>),
}

/// A struct (empty `variant`) or an enum variant with named or positional
/// (`"0"`, `"1"`, ...) fields.
pub struct Adt {
    pub type_name: &'static str,
    pub variant: &'static str,
    pub fields: Vec<(&'static str, Dyn)>,
}

/// A value of a type the lowering knows nothing about.
pub struct Opaque {
    pub type_name: &'static str,
    pub value: Option<Rc<dyn Any>>,
    pub eq: Option<fn(&dyn Any, &dyn Any) -> bool>,
}

/// Last path segment of a type name, ignoring generic arguments:
/// `alloc::vec::Vec<u8>` is `Vec`.
pub fn short_type_name(name: &str) -> &str {
    let name = match name.find('<') {
        Some(i) => &name[..i],
        None => name,
    };
    name.rsplit("::").next().unwrap_or(name)
}

impl Dyn {
    pub fn adt(
        type_name: &'static str,
        variant: &'static str,
        fields: Vec<(&'static str, Dyn)>,
    ) -> Dyn {
        Dyn::Adt(Rc::new(Adt { type_name, variant, fields }))
    }

    pub fn seq(items: Vec<Dyn>) -> Dyn {
        Dyn::Seq(Rc::new(items))
    }

    pub fn tuple(items: Vec<Dyn>) -> Dyn {
        Dyn::Tuple(Rc::new(items))
    }

    pub fn set(items: Vec<Dyn>) -> Dyn {
        let mut out: Vec<Dyn> = Vec::new();
        for item in items {
            if !out.iter().any(|x| equals(x, &item) == Verdict::True) {
                out.push(item);
            }
        }
        Dyn::Set(Rc::new(out))
    }

    pub fn option(value: Option<Dyn>) -> Dyn {
        match value {
            Some(v) => Dyn::adt("core::option::Option", "Some", vec![("0", v)]),
            None => Dyn::adt("core::option::Option", "None", vec![]),
        }
    }

    pub fn opaque(type_name: &'static str) -> Dyn {
        Dyn::Opaque(Rc::new(Opaque { type_name, value: None, eq: None }))
    }

    pub fn from_verdict(v: Verdict) -> Dyn {
        match v {
            Verdict::True => Dyn::Bool(true),
            Verdict::False => Dyn::Bool(false),
            Verdict::Unknown => Dyn::Unknown("unknown"),
        }
    }

    pub fn verdict(&self) -> Verdict {
        match self {
            Dyn::Bool(true) => Verdict::True,
            Dyn::Bool(false) => Verdict::False,
            _ => Verdict::Unknown,
        }
    }

    pub fn unknown_reason(&self) -> Option<&'static str> {
        match self {
            Dyn::Unknown(r) => Some(r),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i128> {
        match self {
            Dyn::Int(i) => Some(*i),
            _ => None,
        }
    }

    /// Sequence view of a `Seq` or a `Str`
    fn as_items(&self) -> Option<Rc<Vec<Dyn>>> {
        match self {
            Dyn::Seq(v) => Some(v.clone()),
            Dyn::Str(s) => Some(Rc::new(s.chars().map(Dyn::Char).collect())),
            _ => None,
        }
    }

    /// Something a spec mentions and we should say how much we know about
    pub fn describe(&self) -> String {
        match self {
            Dyn::Unknown(r) => format!("unknown({r})"),
            Dyn::Unit => "()".into(),
            Dyn::Bool(b) => b.to_string(),
            Dyn::Int(i) => i.to_string(),
            Dyn::Char(c) => format!("{c:?}"),
            Dyn::Float(f) => f.to_string(),
            Dyn::Str(s) => format!("{s:?}"),
            Dyn::Seq(v) => format!("seq[{}]", v.len()),
            Dyn::Set(v) => format!("set[{}]", v.len()),
            Dyn::Map(v) => format!("map[{}]", v.len()),
            Dyn::Tuple(v) => format!("tuple[{}]", v.len()),
            Dyn::Adt(a) => format!("{}::{}", short_type_name(a.type_name), a.variant),
            Dyn::Opaque(o) => format!("opaque({})", short_type_name(o.type_name)),
        }
    }
}

// ---------------------------------------------------------------------------
// Evaluation budget

thread_local! {
    static BUDGET: Cell<u64> = const { Cell::new(u64::MAX) };
}

/// Raised (by panic) when a lowered spec runs out of steps. Caught by
/// `eval`, which reports `Unknown`.
pub struct BudgetExceeded;

/// Charges one step of the evaluation budget.
pub fn tick() {
    BUDGET.with(|b| {
        let n = b.get();
        if n == 0 {
            std::panic::panic_any(BudgetExceeded);
        }
        b.set(n - 1);
    });
}

pub fn set_budget(steps: u64) {
    BUDGET.with(|b| b.set(steps));
}

// ---------------------------------------------------------------------------
// Equality and connectives

/// Structural equality, `Unknown` when either side is (or contains) a
/// value we cannot compare.
pub fn equals(a: &Dyn, b: &Dyn) -> Verdict {
    tick();
    match (a, b) {
        (Dyn::Unknown(_), _) | (_, Dyn::Unknown(_)) => Verdict::Unknown,
        (Dyn::Unit, Dyn::Unit) => Verdict::True,
        (Dyn::Bool(x), Dyn::Bool(y)) => bv(x == y),
        (Dyn::Int(x), Dyn::Int(y)) => bv(x == y),
        (Dyn::Char(x), Dyn::Char(y)) => bv(x == y),
        (Dyn::Float(x), Dyn::Float(y)) => bv(x.to_bits() == y.to_bits()),
        (Dyn::Str(x), Dyn::Str(y)) => bv(x == y),
        (Dyn::Str(_), Dyn::Seq(_)) | (Dyn::Seq(_), Dyn::Str(_)) => {
            seq_equals(&a.as_items().unwrap(), &b.as_items().unwrap())
        }
        (Dyn::Seq(x), Dyn::Seq(y)) => seq_equals(x, y),
        (Dyn::Tuple(x), Dyn::Tuple(y)) => seq_equals(x, y),
        (Dyn::Set(x), Dyn::Set(y)) => {
            if x.len() != y.len() {
                return Verdict::False;
            }
            let mut result = Verdict::True;
            for item in x.iter() {
                match set_contains(y, item) {
                    Verdict::False => return Verdict::False,
                    v => result = result.and(v),
                }
            }
            result
        }
        (Dyn::Map(x), Dyn::Map(y)) => {
            if x.len() != y.len() {
                return Verdict::False;
            }
            let mut result = Verdict::True;
            for (k, v) in x.iter() {
                match map_get(y, k) {
                    Some(Some(w)) => match equals(v, &w) {
                        Verdict::False => return Verdict::False,
                        r => result = result.and(r),
                    },
                    Some(None) => return Verdict::False,
                    None => result = Verdict::Unknown,
                }
            }
            result
        }
        (Dyn::Adt(x), Dyn::Adt(y)) => {
            if short_type_name(x.type_name) != short_type_name(y.type_name)
                || x.variant != y.variant
                || x.fields.len() != y.fields.len()
            {
                return Verdict::False;
            }
            let mut result = Verdict::True;
            for ((_, p), (_, q)) in x.fields.iter().zip(y.fields.iter()) {
                match equals(p, q) {
                    Verdict::False => return Verdict::False,
                    v => result = result.and(v),
                }
            }
            result
        }
        (Dyn::Opaque(x), Dyn::Opaque(y)) => match (&x.value, &y.value, x.eq) {
            (Some(p), Some(q), Some(eq)) if x.type_name == y.type_name => bv(eq(&**p, &**q)),
            _ => Verdict::Unknown,
        },
        _ => Verdict::False,
    }
}

fn bv(b: bool) -> Verdict {
    if b { Verdict::True } else { Verdict::False }
}

fn seq_equals(x: &[Dyn], y: &[Dyn]) -> Verdict {
    if x.len() != y.len() {
        return Verdict::False;
    }
    let mut result = Verdict::True;
    for (p, q) in x.iter().zip(y.iter()) {
        match equals(p, q) {
            Verdict::False => return Verdict::False,
            v => result = result.and(v),
        }
    }
    result
}

fn set_contains(set: &[Dyn], item: &Dyn) -> Verdict {
    let mut result = Verdict::False;
    for x in set {
        match equals(x, item) {
            Verdict::True => return Verdict::True,
            Verdict::Unknown => result = Verdict::Unknown,
            Verdict::False => {}
        }
    }
    result
}

/// `Some(Some(v))` found, `Some(None)` absent, `None` unknown
fn map_get(map: &[(Dyn, Dyn)], key: &Dyn) -> Option<Option<Dyn>> {
    let mut unknown = false;
    for (k, v) in map {
        match equals(k, key) {
            Verdict::True => return Some(Some(v.clone())),
            Verdict::Unknown => unknown = true,
            Verdict::False => {}
        }
    }
    if unknown { None } else { Some(None) }
}

pub fn eq(a: &Dyn, b: &Dyn) -> Dyn {
    match (a, b) {
        (Dyn::Unknown(r), _) | (_, Dyn::Unknown(r)) => Dyn::Unknown(r),
        _ => match equals(a, b) {
            Verdict::Unknown => Dyn::Unknown("incomparable values"),
            v => Dyn::from_verdict(v),
        },
    }
}

pub fn ne(a: &Dyn, b: &Dyn) -> Dyn {
    not(&eq(a, b))
}

pub fn not(a: &Dyn) -> Dyn {
    tick();
    match a {
        Dyn::Bool(b) => Dyn::Bool(!b),
        Dyn::Unknown(r) => Dyn::Unknown(r),
        _ => Dyn::Unknown("! on non-bool"),
    }
}

/// `a && b`, evaluating `b` only when `a` is not `False`. A `False` on
/// either side decides even if the other side is `Unknown`.
pub fn and(a: Dyn, b: impl FnOnce() -> Dyn) -> Dyn {
    tick();
    match a.verdict() {
        Verdict::False => Dyn::Bool(false),
        va => {
            let b = b();
            match (va, b.verdict()) {
                (_, Verdict::False) => Dyn::Bool(false),
                (Verdict::True, Verdict::True) => Dyn::Bool(true),
                (Verdict::Unknown, _) => a,
                (_, Verdict::Unknown) => b,
                _ => unreachable!(),
            }
        }
    }
}

pub fn or(a: Dyn, b: impl FnOnce() -> Dyn) -> Dyn {
    tick();
    match a.verdict() {
        Verdict::True => Dyn::Bool(true),
        va => {
            let b = b();
            match (va, b.verdict()) {
                (_, Verdict::True) => Dyn::Bool(true),
                (Verdict::False, Verdict::False) => Dyn::Bool(false),
                (Verdict::Unknown, _) => a,
                (_, Verdict::Unknown) => b,
                _ => unreachable!(),
            }
        }
    }
}

pub fn implies(a: Dyn, b: impl FnOnce() -> Dyn) -> Dyn {
    or(not(&a), b)
}

pub fn equiv(a: &Dyn, b: &Dyn) -> Dyn {
    match (a.verdict(), b.verdict()) {
        (Verdict::Unknown, _) => not(&not(a)),
        (_, Verdict::Unknown) => not(&not(b)),
        (x, y) => Dyn::Bool(x == y),
    }
}

/// `if c { t } else { e }` with an `Unknown` condition being `Unknown`.
pub fn cond(c: &Dyn, t: impl FnOnce() -> Dyn, e: impl FnOnce() -> Dyn) -> Dyn {
    tick();
    match c {
        Dyn::Bool(true) => t(),
        Dyn::Bool(false) => e(),
        Dyn::Unknown(r) => Dyn::Unknown(r),
        _ => Dyn::Unknown("if on non-bool"),
    }
}

// ---------------------------------------------------------------------------
// Arithmetic and comparison on `int`

fn ints(a: &Dyn, b: &Dyn) -> Result<(i128, i128), Dyn> {
    match (a, b) {
        (Dyn::Int(x), Dyn::Int(y)) => Ok((*x, *y)),
        (Dyn::Unknown(r), _) | (_, Dyn::Unknown(r)) => Err(Dyn::Unknown(r)),
        _ => Err(Dyn::Unknown("arithmetic on non-int")),
    }
}

fn checked(r: Option<i128>) -> Dyn {
    match r {
        Some(v) => Dyn::Int(v),
        None => Dyn::Unknown("int overflow"),
    }
}

pub fn add(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match (a, b) {
        (Dyn::Seq(x), Dyn::Seq(y)) => {
            let mut v = (**x).clone();
            v.extend(y.iter().cloned());
            Dyn::seq(v)
        }
        (Dyn::Str(x), Dyn::Str(y)) => Dyn::Str(format!("{x}{y}").into()),
        (Dyn::Str(_), Dyn::Seq(_)) | (Dyn::Seq(_), Dyn::Str(_)) => {
            let mut v = (*a.as_items().unwrap()).clone();
            v.extend(b.as_items().unwrap().iter().cloned());
            Dyn::seq(v)
        }
        (Dyn::Set(x), Dyn::Set(y)) => {
            let mut v = (**x).clone();
            v.extend(y.iter().cloned());
            Dyn::set(v)
        }
        _ => match ints(a, b) {
            Ok((x, y)) => checked(x.checked_add(y)),
            Err(e) => e,
        },
    }
}

pub fn sub(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match (a, b) {
        (Dyn::Set(x), Dyn::Set(y)) => {
            let v = x.iter().filter(|i| set_contains(y, i) == Verdict::False).cloned().collect();
            Dyn::Set(Rc::new(v))
        }
        _ => match ints(a, b) {
            Ok((x, y)) => checked(x.checked_sub(y)),
            Err(e) => e,
        },
    }
}

pub fn mul(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match ints(a, b) {
        Ok((x, y)) => checked(x.checked_mul(y)),
        Err(e) => e,
    }
}

/// Euclidean division, as Verus defines `/` on `int`
pub fn div(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match ints(a, b) {
        Ok((_, 0)) => Dyn::Unknown("division by zero"),
        Ok((x, y)) => checked(x.checked_div_euclid(y)),
        Err(e) => e,
    }
}

pub fn rem(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match ints(a, b) {
        Ok((_, 0)) => Dyn::Unknown("division by zero"),
        Ok((x, y)) => checked(x.checked_rem_euclid(y)),
        Err(e) => e,
    }
}

pub fn neg(a: &Dyn) -> Dyn {
    tick();
    match a {
        Dyn::Int(x) => checked(x.checked_neg()),
        Dyn::Unknown(r) => Dyn::Unknown(r),
        _ => Dyn::Unknown("- on non-int"),
    }
}

pub fn bitand(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match ints(a, b) {
        Ok((x, y)) => Dyn::Int(x & y),
        Err(e) => e,
    }
}

pub fn bitor(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match ints(a, b) {
        Ok((x, y)) => Dyn::Int(x | y),
        Err(e) => e,
    }
}

pub fn bitxor(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match ints(a, b) {
        Ok((x, y)) => Dyn::Int(x ^ y),
        Err(e) => e,
    }
}

pub fn shl(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match ints(a, b) {
        Ok((x, y)) if (0..127).contains(&y) => checked(x.checked_shl(y as u32)),
        Ok(_) => Dyn::Unknown("shift out of range"),
        Err(e) => e,
    }
}

pub fn shr(a: &Dyn, b: &Dyn) -> Dyn {
    tick();
    match ints(a, b) {
        Ok((x, y)) if (0..127).contains(&y) => Dyn::Int(x >> y),
        Ok(_) => Dyn::Unknown("shift out of range"),
        Err(e) => e,
    }
}

fn compare(a: &Dyn, b: &Dyn, f: fn(std::cmp::Ordering) -> bool) -> Dyn {
    tick();
    match (a, b) {
        (Dyn::Int(x), Dyn::Int(y)) => Dyn::Bool(f(x.cmp(y))),
        (Dyn::Char(x), Dyn::Char(y)) => Dyn::Bool(f(x.cmp(y))),
        (Dyn::Float(x), Dyn::Float(y)) => match x.partial_cmp(y) {
            Some(o) => Dyn::Bool(f(o)),
            None => Dyn::Bool(false),
        },
        (Dyn::Unknown(r), _) | (_, Dyn::Unknown(r)) => Dyn::Unknown(r),
        _ => Dyn::Unknown("comparison on non-int"),
    }
}

pub fn lt(a: &Dyn, b: &Dyn) -> Dyn {
    compare(a, b, |o| o.is_lt())
}

pub fn le(a: &Dyn, b: &Dyn) -> Dyn {
    compare(a, b, |o| o.is_le())
}

pub fn gt(a: &Dyn, b: &Dyn) -> Dyn {
    compare(a, b, |o| o.is_gt())
}

pub fn ge(a: &Dyn, b: &Dyn) -> Dyn {
    compare(a, b, |o| o.is_ge())
}

/// `e as T`: `int`/`nat` are the identity, integer types truncate as
/// Rust does, `char` converts a code point.
pub fn cast(a: &Dyn, ty: &str) -> Dyn {
    tick();
    let x = match a {
        Dyn::Int(x) => *x,
        Dyn::Char(c) => *c as i128,
        Dyn::Bool(b) => *b as i128,
        Dyn::Unknown(r) => return Dyn::Unknown(r),
        _ => return Dyn::Unknown("cast of non-int"),
    };
    let v = match ty {
        "int" | "nat" | "i128" => x,
        "u8" => x as u8 as i128,
        "u16" => x as u16 as i128,
        "u32" => x as u32 as i128,
        "u64" => x as u64 as i128,
        "usize" => x as usize as i128,
        "u128" => match u128::try_from(x) {
            Ok(v) => match i128::try_from(v) {
                Ok(v) => v,
                Err(_) => return Dyn::Unknown("int overflow"),
            },
            Err(_) => return Dyn::Unknown("cast to u128 of a negative"),
        },
        "i8" => x as i8 as i128,
        "i16" => x as i16 as i128,
        "i32" => x as i32 as i128,
        "i64" => x as i64 as i128,
        "isize" => x as isize as i128,
        "char" => {
            return match u32::try_from(x).ok().and_then(char::from_u32) {
                Some(c) => Dyn::Char(c),
                None => Dyn::Unknown("cast to char out of range"),
            };
        }
        _ => return Dyn::Unknown("unsupported cast"),
    };
    Dyn::Int(v)
}

// ---------------------------------------------------------------------------
// Structure access

/// `x.f`, `x.0`, `x->f`, `x->Variant_f`
pub fn field(a: &Dyn, name: &str) -> Dyn {
    tick();
    match a {
        Dyn::Tuple(v) => match name.parse::<usize>().ok().and_then(|i| v.get(i)) {
            Some(x) => x.clone(),
            None => Dyn::Unknown("no such tuple field"),
        },
        Dyn::Adt(adt) => {
            if let Some((_, x)) = adt.fields.iter().find(|(f, _)| *f == name) {
                return x.clone();
            }
            // `x->Variant_field`
            if let Some(rest) = name.strip_prefix(adt.variant) {
                if let Some(f) = rest.strip_prefix('_') {
                    if let Some((_, x)) = adt.fields.iter().find(|(g, _)| *g == f) {
                        return x.clone();
                    }
                }
            }
            Dyn::Unknown("no such field")
        }
        Dyn::Unknown(r) => Dyn::Unknown(r),
        _ => Dyn::Unknown("field of a value without fields"),
    }
}

/// `s[i]` on a `Seq`, or `m[k]` on a `Map`
pub fn index(a: &Dyn, i: &Dyn) -> Dyn {
    tick();
    match a {
        Dyn::Seq(_) | Dyn::Str(_) => {
            let items = a.as_items().unwrap();
            match i {
                Dyn::Int(n) if *n >= 0 && (*n as u128) < items.len() as u128 => {
                    items[*n as usize].clone()
                }
                Dyn::Int(_) => Dyn::Unknown("index out of range"),
                Dyn::Unknown(r) => Dyn::Unknown(r),
                _ => Dyn::Unknown("non-int index"),
            }
        }
        Dyn::Map(m) => match map_get(m, i) {
            Some(Some(v)) => v,
            Some(None) => Dyn::Unknown("key not in map"),
            None => Dyn::Unknown("unknown key"),
        },
        Dyn::Unknown(r) => Dyn::Unknown(r),
        _ => Dyn::Unknown("index of a non-sequence"),
    }
}

/// `x is Variant`, `x matches Variant(..)` for the variant test only
pub fn is_variant(a: &Dyn, variant: &str) -> Dyn {
    tick();
    match a {
        Dyn::Adt(adt) => Dyn::Bool(adt.variant == variant),
        Dyn::Unknown(r) => Dyn::Unknown(r),
        _ => Dyn::Unknown("variant test on a non-enum"),
    }
}

fn int_arg(args: &[Dyn], i: usize) -> Result<i128, Dyn> {
    match args.get(i) {
        Some(Dyn::Int(n)) => Ok(*n),
        Some(Dyn::Unknown(r)) => Err(Dyn::Unknown(r)),
        Some(_) => Err(Dyn::Unknown("non-int argument")),
        None => Err(Dyn::Unknown("missing argument")),
    }
}

fn to_index(n: i128, len: usize) -> Result<usize, Dyn> {
    if n >= 0 && (n as u128) <= len as u128 {
        Ok(n as usize)
    } else {
        Err(Dyn::Unknown("index out of range"))
    }
}

/// A method call in spec context: the vstd `Seq`/`Set`/`Map`/`Option`
/// vocabulary, the float spec accessors, and `view`/`deep_view`. Methods
/// not listed here are resolved by [`super::call_method`] against the
/// lowered user spec functions.
pub fn builtin_method(recv: &Dyn, name: &str, args: &[Dyn]) -> Option<Dyn> {
    tick();
    if let Dyn::Unknown(r) = recv {
        return Some(Dyn::Unknown(r));
    }
    let r = match (recv, name) {
        (_, "view" | "deep_view") => super::view(recv),
        (_, "spec_index") => index(recv, args.first().unwrap_or(&Dyn::Unknown("missing argument"))),
        (_, "is_some" | "is_Some") => is_variant(recv, "Some"),
        (_, "is_none" | "is_None") => is_variant(recv, "None"),
        (_, "is_ok" | "is_Ok") => is_variant(recv, "Ok"),
        (_, "is_err" | "is_Err") => is_variant(recv, "Err"),
        (Dyn::Adt(adt), "unwrap" | "get_Some_0" | "get_Ok_0" | "arrow_Some_0" | "arrow_Ok_0") => {
            match (adt.variant, adt.fields.first()) {
                ("Some" | "Ok", Some((_, v))) => v.clone(),
                _ => Dyn::Unknown("unwrap of None/Err"),
            }
        }
        (Dyn::Adt(adt), "unwrap_err" | "get_Err_0" | "arrow_Err_0") => {
            match (adt.variant, adt.fields.first()) {
                ("Err", Some((_, v))) => v.clone(),
                _ => Dyn::Unknown("unwrap_err of Ok"),
            }
        }
        (Dyn::Seq(_) | Dyn::Str(_), _) => {
            let items = recv.as_items().unwrap();
            match name {
                "len" => Dyn::Int(items.len() as i128),
                "index" => index(recv, args.first().unwrap_or(&Dyn::Unknown("missing argument"))),
                "first" => items.first().cloned().unwrap_or(Dyn::Unknown("first of empty")),
                "last" => items.last().cloned().unwrap_or(Dyn::Unknown("last of empty")),
                "push" => {
                    let mut v = (*items).clone();
                    v.push(args.first().cloned().unwrap_or(Dyn::Unknown("missing argument")));
                    Dyn::seq(v)
                }
                "add" => add(&Dyn::Seq(items.clone()), args.first().unwrap_or(&Dyn::Unit)),
                "subrange" => match (int_arg(args, 0), int_arg(args, 1)) {
                    (Ok(i), Ok(j)) => match (to_index(i, items.len()), to_index(j, items.len())) {
                        (Ok(i), Ok(j)) if i <= j => Dyn::seq(items[i..j].to_vec()),
                        (Ok(_), Ok(_)) => Dyn::Unknown("subrange bounds reversed"),
                        (Err(e), _) | (_, Err(e)) => e,
                    },
                    (Err(e), _) | (_, Err(e)) => e,
                },
                "take" => match int_arg(args, 0).and_then(|n| to_index(n, items.len())) {
                    Ok(n) => Dyn::seq(items[..n].to_vec()),
                    Err(e) => e,
                },
                "skip" => match int_arg(args, 0).and_then(|n| to_index(n, items.len())) {
                    Ok(n) => Dyn::seq(items[n..].to_vec()),
                    Err(e) => e,
                },
                "drop_first" => {
                    if items.is_empty() {
                        Dyn::Unknown("drop_first of empty")
                    } else {
                        Dyn::seq(items[1..].to_vec())
                    }
                }
                "drop_last" => {
                    if items.is_empty() {
                        Dyn::Unknown("drop_last of empty")
                    } else {
                        Dyn::seq(items[..items.len() - 1].to_vec())
                    }
                }
                "update" => match int_arg(args, 0) {
                    Ok(i) if i >= 0 && (i as u128) < items.len() as u128 => {
                        let mut v = (*items).clone();
                        v[i as usize] =
                            args.get(1).cloned().unwrap_or(Dyn::Unknown("missing argument"));
                        Dyn::seq(v)
                    }
                    Ok(_) => Dyn::Unknown("index out of range"),
                    Err(e) => e,
                },
                "contains" => {
                    let x = args.first().unwrap_or(&Dyn::Unknown("missing argument"));
                    Dyn::from_verdict(set_contains(&items, x))
                }
                "is_prefix_of" | "is_suffix_of" => match args.first() {
                    Some(other) => match other.as_items() {
                        Some(o) => {
                            if items.len() > o.len() {
                                Dyn::Bool(false)
                            } else if name == "is_prefix_of" {
                                Dyn::from_verdict(seq_equals(&items, &o[..items.len()]))
                            } else {
                                Dyn::from_verdict(seq_equals(&items, &o[o.len() - items.len()..]))
                            }
                        }
                        None => Dyn::Unknown("prefix test against a non-sequence"),
                    },
                    None => Dyn::Unknown("missing argument"),
                },
                "to_set" => Dyn::set((*items).clone()),
                "reverse" => Dyn::seq(items.iter().rev().cloned().collect()),
                "no_duplicates" => {
                    let mut result = Verdict::True;
                    'outer: for (i, x) in items.iter().enumerate() {
                        for y in &items[i + 1..] {
                            match equals(x, y) {
                                Verdict::True => {
                                    result = Verdict::False;
                                    break 'outer;
                                }
                                Verdict::Unknown => result = Verdict::Unknown,
                                Verdict::False => {}
                            }
                        }
                    }
                    Dyn::from_verdict(result)
                }
                _ => return None,
            }
        }
        (Dyn::Set(items), _) => match name {
            "len" => Dyn::Int(items.len() as i128),
            "contains" => Dyn::from_verdict(set_contains(
                items,
                args.first().unwrap_or(&Dyn::Unknown("missing argument")),
            )),
            "insert" => {
                let mut v = (**items).clone();
                v.push(args.first().cloned().unwrap_or(Dyn::Unknown("missing argument")));
                Dyn::set(v)
            }
            "remove" => {
                let x = args.first().unwrap_or(&Dyn::Unknown("missing argument"));
                let v = items.iter().filter(|i| equals(i, x) == Verdict::False).cloned().collect();
                Dyn::Set(Rc::new(v))
            }
            "union" => add(recv, args.first().unwrap_or(&Dyn::Unit)),
            "difference" => sub(recv, args.first().unwrap_or(&Dyn::Unit)),
            "intersect" => match args.first() {
                Some(Dyn::Set(o)) => Dyn::Set(Rc::new(
                    items.iter().filter(|i| set_contains(o, i) == Verdict::True).cloned().collect(),
                )),
                _ => Dyn::Unknown("intersect with a non-set"),
            },
            "subset_of" => match args.first() {
                Some(Dyn::Set(o)) => {
                    let mut result = Verdict::True;
                    for i in items.iter() {
                        match set_contains(o, i) {
                            Verdict::False => {
                                result = Verdict::False;
                                break;
                            }
                            v => result = result.and(v),
                        }
                    }
                    Dyn::from_verdict(result)
                }
                _ => Dyn::Unknown("subset_of a non-set"),
            },
            "is_empty" => Dyn::Bool(items.is_empty()),
            "finite" => Dyn::Bool(true),
            _ => return None,
        },
        (Dyn::Map(entries), _) => match name {
            "len" => Dyn::Int(entries.len() as i128),
            "dom" => Dyn::set(entries.iter().map(|(k, _)| k.clone()).collect()),
            "contains_key" => {
                let k = args.first().unwrap_or(&Dyn::Unknown("missing argument"));
                match map_get(entries, k) {
                    Some(found) => Dyn::Bool(found.is_some()),
                    None => Dyn::Unknown("unknown key"),
                }
            }
            "index" => index(recv, args.first().unwrap_or(&Dyn::Unknown("missing argument"))),
            "insert" => {
                let k = args.first().cloned().unwrap_or(Dyn::Unknown("missing argument"));
                let v = args.get(1).cloned().unwrap_or(Dyn::Unknown("missing argument"));
                let mut out: Vec<(Dyn, Dyn)> = entries
                    .iter()
                    .filter(|(x, _)| equals(x, &k) == Verdict::False)
                    .cloned()
                    .collect();
                out.push((k, v));
                Dyn::Map(Rc::new(out))
            }
            "remove" => {
                let k = args.first().unwrap_or(&Dyn::Unknown("missing argument"));
                Dyn::Map(Rc::new(
                    entries
                        .iter()
                        .filter(|(x, _)| equals(x, k) == Verdict::False)
                        .cloned()
                        .collect(),
                ))
            }
            "values" => Dyn::set(entries.iter().map(|(_, v)| v.clone()).collect()),
            "is_empty" => Dyn::Bool(entries.is_empty()),
            _ => return None,
        },
        (Dyn::Float(x), _) => match name {
            "is_finite_spec" => Dyn::Bool(x.is_finite()),
            "is_infinite_spec" => Dyn::Bool(x.is_infinite()),
            "is_nan_spec" => Dyn::Bool(x.is_nan()),
            "is_sign_negative_spec" => Dyn::Bool(x.is_sign_negative()),
            "is_sign_positive_spec" => Dyn::Bool(x.is_sign_positive()),
            "is_normal_spec" => Dyn::Bool(x.is_normal()),
            "is_subnormal_spec" => Dyn::Bool(x.is_subnormal()),
            "to_bits_spec" => Dyn::Int(x.to_bits() as i128),
            _ => return None,
        },
        (Dyn::Char(c), _) => match name {
            "is_ascii_digit" => Dyn::Bool(c.is_ascii_digit()),
            "is_ascii_alphabetic" => Dyn::Bool(c.is_ascii_alphabetic()),
            "is_ascii_alphanumeric" => Dyn::Bool(c.is_ascii_alphanumeric()),
            "is_ascii_whitespace" => Dyn::Bool(c.is_ascii_whitespace()),
            "is_ascii" => Dyn::Bool(c.is_ascii()),
            _ => return None,
        },
        (Dyn::Int(x), _) => match name {
            "abs" => checked(x.checked_abs()),
            "pow" => match int_arg(args, 0) {
                Ok(e) if (0..u32::MAX as i128).contains(&e) => checked(x.checked_pow(e as u32)),
                Ok(_) => Dyn::Unknown("pow exponent out of range"),
                Err(e) => e,
            },
            _ => return None,
        },
        _ => return None,
    };
    Some(r)
}

// ---------------------------------------------------------------------------
// Patterns

/// A pattern of a spec `match`, compiled by the macro. Binders are
/// collected left to right into the binding vector.
pub enum Pat {
    Wild,
    Bind,
    Int(i128),
    Bool(bool),
    Char(char),
    Str(&'static str),
    Tuple(&'static [Pat]),
    /// Tuple struct or variant: type (may be empty), variant (may be
    /// empty for a struct), positional sub-patterns
    Variant(&'static str, &'static str, &'static [Pat]),
    /// Struct or struct variant with named fields; `bool` allows `..`
    Struct(&'static str, &'static str, &'static [(&'static str, Pat)], bool),
    Or(&'static [Pat]),
    Unsupported,
}

/// `Some(true)` on a match, `Some(false)` on a mismatch, `None` when the
/// scrutinee cannot be inspected.
pub fn pat_match(value: &Dyn, pat: &Pat, bindings: &mut Vec<Dyn>) -> Option<bool> {
    tick();
    match pat {
        Pat::Wild => Some(true),
        Pat::Bind => {
            bindings.push(value.clone());
            Some(true)
        }
        Pat::Int(n) => match value {
            Dyn::Int(v) => Some(v == n),
            _ => None,
        },
        Pat::Bool(b) => match value {
            Dyn::Bool(v) => Some(v == b),
            _ => None,
        },
        Pat::Char(c) => match value {
            Dyn::Char(v) => Some(v == c),
            _ => None,
        },
        Pat::Str(s) => match value {
            Dyn::Str(v) => Some(&**v == *s),
            _ => None,
        },
        Pat::Tuple(pats) => match value {
            Dyn::Tuple(items) if items.len() == pats.len() => {
                for (item, p) in items.iter().zip(pats.iter()) {
                    if pat_match(item, p, bindings)? == false {
                        return Some(false);
                    }
                }
                Some(true)
            }
            _ => None,
        },
        Pat::Variant(ty, variant, pats) => match value {
            Dyn::Adt(adt) => {
                if !ty.is_empty() && short_type_name(adt.type_name) != *ty {
                    return None;
                }
                if adt.variant != *variant {
                    return Some(false);
                }
                if adt.fields.len() != pats.len() {
                    return None;
                }
                for ((_, item), p) in adt.fields.iter().zip(pats.iter()) {
                    if pat_match(item, p, bindings)? == false {
                        return Some(false);
                    }
                }
                Some(true)
            }
            _ => None,
        },
        Pat::Struct(ty, variant, fields, rest) => match value {
            Dyn::Adt(adt) => {
                if !ty.is_empty() && short_type_name(adt.type_name) != *ty {
                    return None;
                }
                if adt.variant != *variant {
                    return Some(false);
                }
                if !*rest && adt.fields.len() != fields.len() {
                    return None;
                }
                for (name, p) in fields.iter() {
                    let item = adt.fields.iter().find(|(f, _)| f == name)?;
                    if pat_match(&item.1, p, bindings)? == false {
                        return Some(false);
                    }
                }
                Some(true)
            }
            _ => None,
        },
        Pat::Or(pats) => {
            for p in pats.iter() {
                let mark = bindings.len();
                match pat_match(value, p, bindings)? {
                    true => return Some(true),
                    false => bindings.truncate(mark),
                }
            }
            Some(false)
        }
        Pat::Unsupported => None,
    }
}

// ---------------------------------------------------------------------------
// Views of exec values

/// Conversion of an exec value into the dynamic model. Implemented for the
/// standard types here, and for every struct and enum inside a `verus!`
/// block by the macro.
pub trait DynView {
    fn dyn_view(&self) -> Dyn;
}

macro_rules! int_views {
    ($($t:ty),*) => { $(
        impl DynView for $t {
            fn dyn_view(&self) -> Dyn {
                match i128::try_from(*self) {
                    Ok(v) => Dyn::Int(v),
                    Err(_) => Dyn::Unknown("int overflow"),
                }
            }
        }
    )* };
}

int_views!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl DynView for bool {
    fn dyn_view(&self) -> Dyn {
        Dyn::Bool(*self)
    }
}

impl DynView for char {
    fn dyn_view(&self) -> Dyn {
        Dyn::Char(*self)
    }
}

impl DynView for f64 {
    fn dyn_view(&self) -> Dyn {
        Dyn::Float(*self)
    }
}

impl DynView for f32 {
    fn dyn_view(&self) -> Dyn {
        Dyn::Float(*self as f64)
    }
}

impl DynView for () {
    fn dyn_view(&self) -> Dyn {
        Dyn::Unit
    }
}

impl DynView for str {
    fn dyn_view(&self) -> Dyn {
        Dyn::Str(Rc::from(self))
    }
}

impl DynView for String {
    fn dyn_view(&self) -> Dyn {
        Dyn::Str(Rc::from(self.as_str()))
    }
}

impl<T: ?Sized> DynView for std::marker::PhantomData<T> {
    fn dyn_view(&self) -> Dyn {
        Dyn::Unit
    }
}

impl<T> DynView for verus_builtin::Ghost<T> {
    fn dyn_view(&self) -> Dyn {
        Dyn::Unknown("ghost value")
    }
}

impl<T> DynView for verus_builtin::Tracked<T> {
    fn dyn_view(&self) -> Dyn {
        Dyn::Unknown("tracked value")
    }
}

impl<T: DynView + ?Sized> DynView for &T {
    fn dyn_view(&self) -> Dyn {
        (**self).dyn_view()
    }
}

impl<T: DynView + ?Sized> DynView for &mut T {
    fn dyn_view(&self) -> Dyn {
        (**self).dyn_view()
    }
}

impl<T: DynView + ?Sized> DynView for Box<T> {
    fn dyn_view(&self) -> Dyn {
        (**self).dyn_view()
    }
}

impl<T: DynView + ?Sized> DynView for Rc<T> {
    fn dyn_view(&self) -> Dyn {
        (**self).dyn_view()
    }
}

impl<T: DynView + ?Sized> DynView for std::sync::Arc<T> {
    fn dyn_view(&self) -> Dyn {
        (**self).dyn_view()
    }
}

impl<T: DynView> DynView for [T] {
    fn dyn_view(&self) -> Dyn {
        Dyn::seq(
            self.iter()
                .map(|x| {
                    tick();
                    x.dyn_view()
                })
                .collect(),
        )
    }
}

impl<T: DynView, const N: usize> DynView for [T; N] {
    fn dyn_view(&self) -> Dyn {
        Dyn::seq(self.iter().map(|x| x.dyn_view()).collect())
    }
}

impl<T: DynView> DynView for Vec<T> {
    fn dyn_view(&self) -> Dyn {
        Dyn::seq(
            self.iter()
                .map(|x| {
                    tick();
                    x.dyn_view()
                })
                .collect(),
        )
    }
}

impl<T: DynView> DynView for VecDeque<T> {
    fn dyn_view(&self) -> Dyn {
        Dyn::seq(self.iter().map(|x| x.dyn_view()).collect())
    }
}

impl<T: DynView> DynView for Option<T> {
    fn dyn_view(&self) -> Dyn {
        Dyn::option(self.as_ref().map(|x| x.dyn_view()))
    }
}

impl<T: DynView, E: DynView> DynView for Result<T, E> {
    fn dyn_view(&self) -> Dyn {
        match self {
            Ok(x) => Dyn::adt("core::result::Result", "Ok", vec![("0", x.dyn_view())]),
            Err(e) => Dyn::adt("core::result::Result", "Err", vec![("0", e.dyn_view())]),
        }
    }
}

impl<T: DynView, S> DynView for HashSet<T, S> {
    fn dyn_view(&self) -> Dyn {
        Dyn::set(self.iter().map(|x| x.dyn_view()).collect())
    }
}

impl<T: DynView> DynView for BTreeSet<T> {
    fn dyn_view(&self) -> Dyn {
        Dyn::set(self.iter().map(|x| x.dyn_view()).collect())
    }
}

impl<K: DynView, V: DynView, S> DynView for HashMap<K, V, S> {
    fn dyn_view(&self) -> Dyn {
        Dyn::Map(Rc::new(self.iter().map(|(k, v)| (k.dyn_view(), v.dyn_view())).collect()))
    }
}

impl<K: DynView, V: DynView> DynView for BTreeMap<K, V> {
    fn dyn_view(&self) -> Dyn {
        Dyn::Map(Rc::new(self.iter().map(|(k, v)| (k.dyn_view(), v.dyn_view())).collect()))
    }
}

macro_rules! tuple_views {
    ($(($($T:ident $i:tt),*))*) => { $(
        impl<$($T: DynView),*> DynView for ($($T,)*) {
            fn dyn_view(&self) -> Dyn {
                Dyn::tuple(vec![$(self.$i.dyn_view()),*])
            }
        }
    )* };
}

tuple_views! {
    (A 0)
    (A 0, B 1)
    (A 0, B 1, C 2)
    (A 0, B 1, C 2, D 3)
    (A 0, B 1, C 2, D 3, E 4)
    (A 0, B 1, C 2, D 3, E 4, F 5)
}

/// Autoref-specialized entry point used by generated code: `W` and the
/// three `ViewL*` traits pick, at each use site, the best conversion the
/// type supports without the macro knowing the type. See [`view!`].
pub struct W<T>(pub T);

pub trait ViewL1 {
    fn __dyncov_view(&self) -> Dyn;
}

pub trait ViewL2 {
    fn __dyncov_view(&self) -> Dyn;
}

pub trait ViewL3 {
    fn __dyncov_view(&self) -> Dyn;
}

/// The type has a model
impl<T: DynView + ?Sized> ViewL1 for &&W<&T> {
    fn __dyncov_view(&self) -> Dyn {
        self.0.dyn_view()
    }
}

fn eq_any<T: PartialEq + 'static>(a: &dyn Any, b: &dyn Any) -> bool {
    match (a.downcast_ref::<T>(), b.downcast_ref::<T>()) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

/// The type only supports equality
impl<T: PartialEq + Clone + 'static> ViewL2 for &W<&T> {
    fn __dyncov_view(&self) -> Dyn {
        Dyn::Opaque(Rc::new(Opaque {
            type_name: std::any::type_name::<T>(),
            value: Some(Rc::new(self.0.clone())),
            eq: Some(eq_any::<T>),
        }))
    }
}

/// The type supports nothing
impl<T: ?Sized> ViewL3 for W<&T> {
    fn __dyncov_view(&self) -> Dyn {
        Dyn::opaque(std::any::type_name::<T>())
    }
}

/// Converts an exec value (given by reference) to a [`Dyn`].
#[macro_export]
macro_rules! dyncov_view {
    ($e:expr) => {{
        #[allow(unused_imports)]
        use $crate::contrib::dyncov::{ViewL1, ViewL2, ViewL3};
        (&&&$crate::contrib::dyncov::W($e)).__dyncov_view()
    }};
}
