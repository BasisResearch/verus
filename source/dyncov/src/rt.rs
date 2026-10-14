//! The subset of the `verus_spec_check` runtime that lowered contracts
//! refer to, ported from `dependencies/verus-spec-check/source/runtime`
//! (`spec_int_kani.rs` and the `__vcheck_*` helpers of `lib.rs`), without
//! that crate's proptest, bolero and coverage machinery. The `verus!`
//! macro rewrites the engine's `::verus_spec_check::` paths to
//! `::verus_dyncov::rt::`.
//!
//! Math integers (`int`, `nat`) are modeled by `i128`, as the engine's
//! Kani tier does: every operation is exact while the values fit, and a
//! value outside the model panics, which the clause evaluator turns into
//! `Unknown`.

use std::collections::HashSet;
use std::hash::Hash;

pub mod __vcheck_int {
    //! Verus `int` modeled as `i128`; panics (→ `Unknown`) at the boundary.

    pub type SpecInt = i128;

    pub const RANGE_MSG: &str =
        "dyncov: spec-int arithmetic exceeded the i128 model (out of range)";

    pub trait IntoSpecInt {
        fn into_spec_int(self) -> SpecInt;
    }

    macro_rules! impl_into_spec_int {
        ($($t:ty),* $(,)?) => {
            $(
                impl IntoSpecInt for $t {
                    #[inline]
                    fn into_spec_int(self) -> SpecInt {
                        self as i128
                    }
                }
            )*
        };
    }

    impl_into_spec_int!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);

    impl IntoSpecInt for i128 {
        #[inline]
        fn into_spec_int(self) -> SpecInt {
            self
        }
    }

    impl IntoSpecInt for u128 {
        #[inline]
        fn into_spec_int(self) -> SpecInt {
            i128::try_from(self).unwrap_or_else(|_| panic!("{}", RANGE_MSG))
        }
    }

    /// `char` casts to an integer in spec code (`c as int`).
    impl IntoSpecInt for char {
        #[inline]
        fn into_spec_int(self) -> SpecInt {
            self as u32 as i128
        }
    }

    /// Explicit lift to `SpecInt` (`<expr> as int` / `as nat`).
    #[inline]
    pub fn lift(x: impl IntoSpecInt) -> SpecInt {
        x.into_spec_int()
    }

    #[inline]
    pub fn add(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
        a.into_spec_int().checked_add(b.into_spec_int()).unwrap_or_else(|| panic!("{}", RANGE_MSG))
    }

    #[inline]
    pub fn sub(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
        a.into_spec_int().checked_sub(b.into_spec_int()).unwrap_or_else(|| panic!("{}", RANGE_MSG))
    }

    #[inline]
    pub fn mul(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
        a.into_spec_int().checked_mul(b.into_spec_int()).unwrap_or_else(|| panic!("{}", RANGE_MSG))
    }

    /// Euclidean division, matching Verus spec `/`.
    #[inline]
    pub fn div(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
        let b = b.into_spec_int();
        if b == 0 {
            panic!("__vcheck_int::div: division by zero in contract evaluation");
        }
        a.into_spec_int().checked_div_euclid(b).unwrap_or_else(|| panic!("{}", RANGE_MSG))
    }

    /// Euclidean remainder, matching Verus spec `%`.
    #[inline]
    pub fn rem(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
        let b = b.into_spec_int();
        if b == 0 {
            panic!("__vcheck_int::rem: modulo by zero in contract evaluation");
        }
        a.into_spec_int().checked_rem_euclid(b).unwrap_or_else(|| panic!("{}", RANGE_MSG))
    }

    #[inline]
    pub fn neg(a: impl IntoSpecInt) -> SpecInt {
        a.into_spec_int().checked_neg().unwrap_or_else(|| panic!("{}", RANGE_MSG))
    }

    #[inline]
    pub fn lt(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
        a.into_spec_int() < b.into_spec_int()
    }

    #[inline]
    pub fn le(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
        a.into_spec_int() <= b.into_spec_int()
    }

    #[inline]
    pub fn gt(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
        a.into_spec_int() > b.into_spec_int()
    }

    #[inline]
    pub fn ge(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
        a.into_spec_int() >= b.into_spec_int()
    }

    #[inline]
    pub fn eq(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
        a.into_spec_int() == b.into_spec_int()
    }

    #[inline]
    pub fn ne(a: impl IntoSpecInt, b: impl IntoSpecInt) -> bool {
        a.into_spec_int() != b.into_spec_int()
    }

    macro_rules! to_int {
        ($name:ident, $t:ty) => {
            #[inline]
            pub fn $name(x: impl IntoSpecInt) -> $t {
                let x = x.into_spec_int();
                <$t>::try_from(x).unwrap_or_else(|_| {
                    panic!(
                        "__vcheck_int::{}: value out of range for {}: {}",
                        stringify!($name),
                        stringify!($t),
                        x,
                    )
                })
            }
        };
    }

    to_int!(to_u8, u8);
    to_int!(to_u16, u16);
    to_int!(to_u32, u32);
    to_int!(to_u64, u64);
    to_int!(to_u128, u128);
    to_int!(to_usize, usize);
    to_int!(to_i8, i8);
    to_int!(to_i16, i16);
    to_int!(to_i32, i32);
    to_int!(to_i64, i64);
    to_int!(to_i128, i128);
    to_int!(to_isize, isize);

    /// `x as char` in spec code.
    #[inline]
    pub fn to_char(x: impl IntoSpecInt) -> char {
        let x = x.into_spec_int();
        u32::try_from(x)
            .ok()
            .and_then(char::from_u32)
            .unwrap_or_else(|| panic!("__vcheck_int::to_char: value out of range for char: {}", x))
    }

    /// `x << n` as `x * 2^n`, checked.
    #[inline]
    pub fn shl(a: impl IntoSpecInt, n: impl IntoSpecInt) -> SpecInt {
        let a = a.into_spec_int();
        let n = n.into_spec_int();
        let n = u32::try_from(n).unwrap_or_else(|_| {
            panic!("__vcheck_int::shl: shift count out of range for u32: {}", n)
        });
        if n >= 127 {
            if a == 0 {
                return 0;
            }
            panic!("{}", RANGE_MSG);
        }
        a.checked_mul(1i128 << n).unwrap_or_else(|| panic!("{}", RANGE_MSG))
    }

    /// `x >> n` as floor division by `2^n`.
    #[inline]
    pub fn shr(a: impl IntoSpecInt, n: impl IntoSpecInt) -> SpecInt {
        let a = a.into_spec_int();
        let n = n.into_spec_int();
        let n = u32::try_from(n).unwrap_or_else(|_| {
            panic!("__vcheck_int::shr: shift count out of range for u32: {}", n)
        });
        if n >= 127 {
            return if a < 0 { -1 } else { 0 };
        }
        a >> n
    }

    #[inline]
    pub fn bitand(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
        a.into_spec_int() & b.into_spec_int()
    }

    #[inline]
    pub fn bitor(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
        a.into_spec_int() | b.into_spec_int()
    }

    #[inline]
    pub fn bitxor(a: impl IntoSpecInt, b: impl IntoSpecInt) -> SpecInt {
        a.into_spec_int() ^ b.into_spec_int()
    }
}

pub use __vcheck_int::SpecInt;

/// Converts a value of a user type into the engine's exec model. The dyncov
/// mode of the engine uses every exec type as its own model, so this is
/// the identity (a clone) for the types declared inside `verus!`.
pub trait ToExecModel {
    type Exec;
    fn to_exec_model(&self) -> Self::Exec;
}

/// Marker the engine emits for types whose spec fns have runnable twins.
pub trait VcheckSpecCompanion {
    const PROVIDED: () = ();
}

#[doc(hidden)]
pub fn __vcheck_seq_update<T>(mut v: Vec<T>, i: usize, x: T) -> Vec<T> {
    v[i] = x;
    v
}

#[doc(hidden)]
pub fn __vcheck_str_chars(s: &str) -> Vec<char> {
    s.chars().collect()
}

#[doc(hidden)]
pub fn __vcheck_str_bytes(s: &str) -> &[u8] {
    s.as_bytes()
}

#[doc(hidden)]
pub fn __vcheck_seq_concat<T: Clone>(a: impl AsRef<[T]>, b: impl AsRef<[T]>) -> Vec<T> {
    let (a, b) = (a.as_ref(), b.as_ref());
    let mut out = Vec::with_capacity(a.len() + b.len());
    out.extend_from_slice(a);
    out.extend_from_slice(b);
    out
}

#[doc(hidden)]
pub fn __vcheck_seq_eq<T: PartialEq>(a: impl AsRef<[T]>, b: impl AsRef<[T]>) -> bool {
    a.as_ref() == b.as_ref()
}

#[doc(hidden)]
pub fn __vcheck_vecdeque_slice<T: Clone>(v: &std::collections::VecDeque<T>) -> Vec<T> {
    v.iter().cloned().collect()
}

#[doc(hidden)]
pub fn __vcheck_vecdeque_snapshot<T: Clone>(
    v: &std::collections::VecDeque<T>,
) -> std::collections::VecDeque<T> {
    v.clone()
}

#[doc(hidden)]
pub fn __vcheck_seq_push<T>(mut v: Vec<T>, x: T) -> Vec<T> {
    v.push(x);
    v
}

#[doc(hidden)]
pub fn __vcheck_seq_last<T>(mut v: Vec<T>) -> T {
    v.pop().expect("dyncov: Seq::last on empty sequence")
}

#[doc(hidden)]
pub fn __vcheck_seq_first<T>(v: Vec<T>) -> T {
    v.into_iter().next().expect("dyncov: Seq::first on empty sequence")
}

#[doc(hidden)]
pub fn __vcheck_seq_drop_last<T>(mut v: Vec<T>) -> Vec<T> {
    v.pop();
    v
}

#[doc(hidden)]
pub fn __vcheck_seq_insert<T>(mut v: Vec<T>, i: usize, x: T) -> Vec<T> {
    v.insert(i, x);
    v
}

#[doc(hidden)]
pub fn __vcheck_seq_remove<T>(mut v: Vec<T>, i: usize) -> Vec<T> {
    v.remove(i);
    v
}

#[doc(hidden)]
pub fn __vcheck_seq_contains<T: PartialEq>(v: impl AsRef<[T]>, x: T) -> bool {
    v.as_ref().iter().any(|e| *e == x)
}

#[doc(hidden)]
pub fn __vcheck_seq_to_set<T>(v: impl AsRef<[T]>) -> HashSet<T>
where
    T: Clone + Eq + Hash,
{
    v.as_ref().iter().cloned().collect()
}

#[doc(hidden)]
pub fn __vcheck_set_map<T, U, F>(set: &HashSet<T>, f: F) -> HashSet<U>
where
    T: Clone + Eq + Hash,
    U: Eq + Hash,
    F: Fn(T) -> U,
{
    set.iter().cloned().map(f).collect()
}

#[doc(hidden)]
pub fn __vcheck_iter_remaining<'a, T>(state: (i64, &'a [T])) -> &'a [T] {
    &state.1[state.0 as usize..]
}

#[doc(hidden)]
pub fn __vcheck_seq_reverse<T>(mut v: Vec<T>) -> Vec<T> {
    v.reverse();
    v
}

#[doc(hidden)]
pub fn __vcheck_seq_is_prefix_of<T: PartialEq>(a: impl AsRef<[T]>, b: impl AsRef<[T]>) -> bool {
    b.as_ref().starts_with(a.as_ref())
}

#[doc(hidden)]
pub fn __vcheck_seq_is_suffix_of<T: PartialEq>(a: impl AsRef<[T]>, b: impl AsRef<[T]>) -> bool {
    b.as_ref().ends_with(a.as_ref())
}

/// Owned-value normalizer for `Map::index` results.
pub trait VcheckMapIndexOwned<T> {
    fn vcheck_owned(self) -> T;
}

impl<T: Clone> VcheckMapIndexOwned<T> for T {
    #[inline(always)]
    fn vcheck_owned(self) -> T {
        self
    }
}

impl<T: Clone> VcheckMapIndexOwned<T> for &T {
    #[inline(always)]
    fn vcheck_owned(self) -> T {
        self.clone()
    }
}

/// `exec_*` companions for `Map`-viewed `BTreeMap`.
pub trait VcheckBTreeMapExec<K, V> {
    fn exec_insert(self, key: K, value: V) -> std::collections::BTreeMap<K, V>;
    fn exec_remove(self, key: K) -> std::collections::BTreeMap<K, V>;
    fn exec_get(self, key: K) -> Option<V>;
    fn exec_index(self, key: K) -> V;
}

impl<K: Ord + Clone, V: Clone> VcheckBTreeMapExec<K, V> for &std::collections::BTreeMap<K, V> {
    #[inline(always)]
    fn exec_insert(self, key: K, value: V) -> std::collections::BTreeMap<K, V> {
        let mut m = self.clone();
        let _ = m.insert(key, value);
        m
    }

    #[inline(always)]
    fn exec_remove(self, key: K) -> std::collections::BTreeMap<K, V> {
        let mut m = self.clone();
        let _ = m.remove(&key);
        m
    }

    #[inline(always)]
    fn exec_get(self, key: K) -> Option<V> {
        self.get(&key).cloned()
    }

    #[inline(always)]
    fn exec_index(self, key: K) -> V {
        self.get(&key).cloned().expect("dyncov: Map::index on an absent key")
    }
}

/// `exec_*` companions for `Set`-viewed `BTreeSet`.
pub trait VcheckBTreeSetExec<K> {
    fn exec_insert(self, elem: K) -> std::collections::BTreeSet<K>;
    fn exec_remove(self, elem: K) -> std::collections::BTreeSet<K>;
}

impl<K: Ord + Clone> VcheckBTreeSetExec<K> for &std::collections::BTreeSet<K> {
    #[inline(always)]
    fn exec_insert(self, elem: K) -> std::collections::BTreeSet<K> {
        let mut s = self.clone();
        let _ = s.insert(elem);
        s
    }

    #[inline(always)]
    fn exec_remove(self, elem: K) -> std::collections::BTreeSet<K> {
        let mut s = self.clone();
        let _ = s.remove(&elem);
        s
    }
}

// ---------------------------------------------------------------------------
// Operators of lowered expressions.
//
// The engine's exec forms are values for primitives and references for
// everything else; each operator dispatches on that shape: integers of any
// width (and `SpecInt`) compute in the `int` domain, sequences concatenate,
// and references compare by `PartialEq`/`PartialOrd`. The engine emits
// `::verus_dyncov::rt::dc_add(l, r)` and so on.

pub trait DcAdd<Rhs> {
    type Out;
    fn dc_add(self, rhs: Rhs) -> Self::Out;
}

pub trait DcArith<Rhs> {
    fn dc_sub(self, rhs: Rhs) -> SpecInt;
    fn dc_mul(self, rhs: Rhs) -> SpecInt;
    fn dc_div(self, rhs: Rhs) -> SpecInt;
    fn dc_rem(self, rhs: Rhs) -> SpecInt;
}

pub trait DcOrd<Rhs> {
    fn dc_lt(self, rhs: Rhs) -> bool;
    fn dc_le(self, rhs: Rhs) -> bool;
    fn dc_gt(self, rhs: Rhs) -> bool;
    fn dc_ge(self, rhs: Rhs) -> bool;
}

pub trait DcEq<Rhs> {
    fn dc_eq(self, rhs: Rhs) -> bool;
}

pub trait DcNeg {
    fn dc_neg(self) -> SpecInt;
}

macro_rules! impl_dc_int {
    ($($t:ty),* $(,)?) => {
        $(
            impl<R: __vcheck_int::IntoSpecInt> DcAdd<R> for $t {
                type Out = SpecInt;
                #[inline]
                fn dc_add(self, rhs: R) -> SpecInt { __vcheck_int::add(self, rhs) }
            }
            impl<R: __vcheck_int::IntoSpecInt> DcArith<R> for $t {
                #[inline]
                fn dc_sub(self, rhs: R) -> SpecInt { __vcheck_int::sub(self, rhs) }
                #[inline]
                fn dc_mul(self, rhs: R) -> SpecInt { __vcheck_int::mul(self, rhs) }
                #[inline]
                fn dc_div(self, rhs: R) -> SpecInt { __vcheck_int::div(self, rhs) }
                #[inline]
                fn dc_rem(self, rhs: R) -> SpecInt { __vcheck_int::rem(self, rhs) }
            }
            impl<R: __vcheck_int::IntoSpecInt> DcOrd<R> for $t {
                #[inline]
                fn dc_lt(self, rhs: R) -> bool { __vcheck_int::lt(self, rhs) }
                #[inline]
                fn dc_le(self, rhs: R) -> bool { __vcheck_int::le(self, rhs) }
                #[inline]
                fn dc_gt(self, rhs: R) -> bool { __vcheck_int::gt(self, rhs) }
                #[inline]
                fn dc_ge(self, rhs: R) -> bool { __vcheck_int::ge(self, rhs) }
            }
            impl<R: __vcheck_int::IntoSpecInt> DcEq<R> for $t {
                #[inline]
                fn dc_eq(self, rhs: R) -> bool { __vcheck_int::eq(self, rhs) }
            }
            impl DcNeg for $t {
                #[inline]
                fn dc_neg(self) -> SpecInt { __vcheck_int::neg(self) }
            }
        )*
    };
}

// Integers of any width, and `char` as its code point, compute in the
// `int` domain (the engine lifts untyped literals to `SpecInt`, so an
// expression's type never waits on a literal's).
impl_dc_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, char);

macro_rules! impl_dc_value {
    ($($t:ty),* $(,)?) => {
        $(
            impl DcOrd<$t> for $t {
                #[inline]
                fn dc_lt(self, rhs: $t) -> bool { self < rhs }
                #[inline]
                fn dc_le(self, rhs: $t) -> bool { self <= rhs }
                #[inline]
                fn dc_gt(self, rhs: $t) -> bool { self > rhs }
                #[inline]
                fn dc_ge(self, rhs: $t) -> bool { self >= rhs }
            }
            impl DcEq<$t> for $t {
                #[inline]
                fn dc_eq(self, rhs: $t) -> bool { self == rhs }
            }
        )*
    };
}

impl_dc_value!(bool, f32, f64, ());

/// References (sequences, strings, user types, options, tuples) compare by
/// `PartialEq` and `PartialOrd`.
impl<'a, 'b, T: ?Sized + PartialEq<U>, U: ?Sized> DcEq<&'b U> for &'a T {
    #[inline]
    fn dc_eq(self, rhs: &'b U) -> bool {
        *self == *rhs
    }
}

impl<'a, 'b, T: ?Sized + PartialOrd<U>, U: ?Sized> DcOrd<&'b U> for &'a T {
    #[inline]
    fn dc_lt(self, rhs: &'b U) -> bool {
        *self < *rhs
    }
    #[inline]
    fn dc_le(self, rhs: &'b U) -> bool {
        *self <= *rhs
    }
    #[inline]
    fn dc_gt(self, rhs: &'b U) -> bool {
        *self > *rhs
    }
    #[inline]
    fn dc_ge(self, rhs: &'b U) -> bool {
        *self >= *rhs
    }
}

/// `Seq + Seq` concatenates.
impl<'a, 'b, T: Clone> DcAdd<&'b [T]> for &'a [T] {
    type Out = Vec<T>;
    #[inline]
    fn dc_add(self, rhs: &'b [T]) -> Vec<T> {
        __vcheck_seq_concat(self, rhs)
    }
}

impl<'a, 'b, T: Clone> DcAdd<&'b Vec<T>> for &'a [T] {
    type Out = Vec<T>;
    #[inline]
    fn dc_add(self, rhs: &'b Vec<T>) -> Vec<T> {
        __vcheck_seq_concat(self, rhs.as_slice())
    }
}

impl<'a, 'b> DcAdd<&'b str> for &'a str {
    type Out = String;
    #[inline]
    fn dc_add(self, rhs: &'b str) -> String {
        let mut s = String::from(self);
        s.push_str(rhs);
        s
    }
}

#[inline]
pub fn dc_add<A: DcAdd<B>, B>(a: A, b: B) -> A::Out {
    a.dc_add(b)
}
#[inline]
pub fn dc_sub<A: DcArith<B>, B>(a: A, b: B) -> SpecInt {
    a.dc_sub(b)
}
#[inline]
pub fn dc_mul<A: DcArith<B>, B>(a: A, b: B) -> SpecInt {
    a.dc_mul(b)
}
#[inline]
pub fn dc_div<A: DcArith<B>, B>(a: A, b: B) -> SpecInt {
    a.dc_div(b)
}
#[inline]
pub fn dc_rem<A: DcArith<B>, B>(a: A, b: B) -> SpecInt {
    a.dc_rem(b)
}
#[inline]
pub fn dc_lt<A: DcOrd<B>, B>(a: A, b: B) -> bool {
    a.dc_lt(b)
}
#[inline]
pub fn dc_le<A: DcOrd<B>, B>(a: A, b: B) -> bool {
    a.dc_le(b)
}
#[inline]
pub fn dc_gt<A: DcOrd<B>, B>(a: A, b: B) -> bool {
    a.dc_gt(b)
}
#[inline]
pub fn dc_ge<A: DcOrd<B>, B>(a: A, b: B) -> bool {
    a.dc_ge(b)
}
#[inline]
pub fn dc_eq<A: DcEq<B>, B>(a: A, b: B) -> bool {
    a.dc_eq(b)
}
#[inline]
pub fn dc_ne<A: DcEq<B>, B>(a: A, b: B) -> bool {
    !a.dc_eq(b)
}
#[inline]
pub fn dc_neg<A: DcNeg>(a: A) -> SpecInt {
    a.dc_neg()
}
#[inline]
pub fn dc_bitand(a: impl __vcheck_int::IntoSpecInt, b: impl __vcheck_int::IntoSpecInt) -> SpecInt {
    __vcheck_int::bitand(a, b)
}
#[inline]
pub fn dc_bitor(a: impl __vcheck_int::IntoSpecInt, b: impl __vcheck_int::IntoSpecInt) -> SpecInt {
    __vcheck_int::bitor(a, b)
}
#[inline]
pub fn dc_bitxor(a: impl __vcheck_int::IntoSpecInt, b: impl __vcheck_int::IntoSpecInt) -> SpecInt {
    __vcheck_int::bitxor(a, b)
}
#[inline]
pub fn dc_shl(a: impl __vcheck_int::IntoSpecInt, b: impl __vcheck_int::IntoSpecInt) -> SpecInt {
    __vcheck_int::shl(a, b)
}
#[inline]
pub fn dc_shr(a: impl __vcheck_int::IntoSpecInt, b: impl __vcheck_int::IntoSpecInt) -> SpecInt {
    __vcheck_int::shr(a, b)
}

/// The spec methods of floats (`vstd::float`), by their exec twin names.
pub trait DcFloat {
    fn exec_is_finite_spec(self) -> bool;
    fn exec_is_infinite_spec(self) -> bool;
    fn exec_is_nan_spec(self) -> bool;
    fn exec_is_sign_negative_spec(self) -> bool;
    fn exec_is_sign_positive_spec(self) -> bool;
    fn exec_is_normal_spec(self) -> bool;
    fn exec_is_subnormal_spec(self) -> bool;
}

macro_rules! impl_dc_float {
    ($($t:ty),*) => {
        $(
            impl DcFloat for $t {
                #[inline] fn exec_is_finite_spec(self) -> bool { self.is_finite() }
                #[inline] fn exec_is_infinite_spec(self) -> bool { self.is_infinite() }
                #[inline] fn exec_is_nan_spec(self) -> bool { self.is_nan() }
                #[inline] fn exec_is_sign_negative_spec(self) -> bool { self.is_sign_negative() }
                #[inline] fn exec_is_sign_positive_spec(self) -> bool { self.is_sign_positive() }
                #[inline] fn exec_is_normal_spec(self) -> bool { self.is_normal() }
                #[inline] fn exec_is_subnormal_spec(self) -> bool { self.is_subnormal() }
            }
        )*
    };
}

impl_dc_float!(f32, f64);

#[cfg(test)]
mod dc_tests {
    use super::*;

    #[test]
    fn operators_dispatch_on_shape() {
        assert_eq!(dc_add(1u8, 2usize), 3);
        assert_eq!(dc_add(&[1u8, 2][..], &[3u8][..]), vec![1, 2, 3]);
        assert_eq!(dc_add("a", "b"), "ab");
        assert!(dc_lt(3u8, 300i128));
        assert!(dc_eq(255u8, 255u64));
        assert!(dc_eq(&"x"[..], &"x"[..]));
        assert!(dc_eq(&Some(3u8), &Some(3u8)));
        assert!(dc_lt(&[1u8][..], &[2u8][..]));
        assert!(dc_lt('a', 'b'));
        assert!(dc_le('a', 97u8));
        assert_eq!(dc_add('a', 1), 98);
        assert!(dc_eq(true, true));
        assert_eq!(dc_neg(5u8), -5);
        assert!(1.5f64.exec_is_finite_spec());
    }
}

/// A value flowing into a slot whose type is known: an `int` computation
/// narrows to a fixed-width field or element type; anything else passes
/// through.
pub trait DcInto<T> {
    fn dc_into(self) -> T;
}

impl<T> DcInto<T> for T {
    #[inline(always)]
    fn dc_into(self) -> T {
        self
    }
}

macro_rules! impl_dc_into_int {
    ($($t:ident => $f:ident),* $(,)?) => {
        $(
            impl DcInto<$t> for i128 {
                #[inline(always)]
                fn dc_into(self) -> $t {
                    __vcheck_int::$f(self)
                }
            }
        )*
    };
}

impl_dc_into_int!(u8 => to_u8, u16 => to_u16, u32 => to_u32, u64 => to_u64, u128 => to_u128,
    usize => to_usize, i8 => to_i8, i16 => to_i16, i32 => to_i32, i64 => to_i64, isize => to_isize,
    char => to_char);

#[inline(always)]
pub fn dc_into<A: DcInto<B>, B>(a: A) -> B {
    a.dc_into()
}

/// `x@` and `x.view()` / `x.deep_view()` of a std value: the value itself
/// (a user type's `View` impl gets an inherent `exec_view` twin, which
/// takes precedence).
pub trait DcView {
    type V;
    fn exec_view(self) -> Self::V;
    fn exec_deep_view(self) -> Self::V;
}

macro_rules! impl_dc_view_value {
    ($($t:ty),* $(,)?) => {
        $(
            impl DcView for $t {
                type V = $t;
                #[inline(always)]
                fn exec_view(self) -> $t { self }
                #[inline(always)]
                fn exec_deep_view(self) -> $t { self }
            }
        )*
    };
}

impl_dc_view_value!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, bool, char, f32, f64
);

macro_rules! impl_dc_view_ref {
    ($($t:ty),* $(,)?) => {
        $(
            impl<'a> DcView for &'a $t {
                type V = &'a $t;
                #[inline(always)]
                fn exec_view(self) -> &'a $t { self }
                #[inline(always)]
                fn exec_deep_view(self) -> &'a $t { self }
            }
        )*
    };
}

impl_dc_view_ref!(str);

impl<'a, T> DcView for &'a [T] {
    type V = &'a [T];
    #[inline(always)]
    fn exec_view(self) -> &'a [T] {
        self
    }
    #[inline(always)]
    fn exec_deep_view(self) -> &'a [T] {
        self
    }
}

impl<'a, T> DcView for &'a Vec<T> {
    type V = &'a [T];
    #[inline(always)]
    fn exec_view(self) -> &'a [T] {
        self.as_slice()
    }
    #[inline(always)]
    fn exec_deep_view(self) -> &'a [T] {
        self.as_slice()
    }
}

impl<'a> DcView for &'a String {
    type V = &'a str;
    #[inline(always)]
    fn exec_view(self) -> &'a str {
        self.as_str()
    }
    #[inline(always)]
    fn exec_deep_view(self) -> &'a str {
        self.as_str()
    }
}

impl<'a, T> DcView for &'a Option<T> {
    type V = &'a Option<T>;
    #[inline(always)]
    fn exec_view(self) -> &'a Option<T> {
        self
    }
    #[inline(always)]
    fn exec_deep_view(self) -> &'a Option<T> {
        self
    }
}

impl<'a, T> DcView for &'a Box<T> {
    type V = &'a T;
    #[inline(always)]
    fn exec_view(self) -> &'a T {
        self
    }
    #[inline(always)]
    fn exec_deep_view(self) -> &'a T {
        self
    }
}

impl<'a, K, V> DcView for &'a std::collections::HashMap<K, V> {
    type V = &'a std::collections::HashMap<K, V>;
    #[inline(always)]
    fn exec_view(self) -> Self::V {
        self
    }
    #[inline(always)]
    fn exec_deep_view(self) -> Self::V {
        self
    }
}

impl<'a, K> DcView for &'a HashSet<K> {
    type V = &'a HashSet<K>;
    #[inline(always)]
    fn exec_view(self) -> Self::V {
        self
    }
    #[inline(always)]
    fn exec_deep_view(self) -> Self::V {
        self
    }
}

impl<'a, K: Clone + Hash + Eq, V: Clone> DcView for &'a std::collections::BTreeMap<K, V> {
    type V = std::collections::HashMap<K, V>;
    #[inline(always)]
    fn exec_view(self) -> Self::V {
        self.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
    #[inline(always)]
    fn exec_deep_view(self) -> Self::V {
        self.exec_view()
    }
}

impl<'a, K: Clone + Hash + Eq> DcView for &'a std::collections::BTreeSet<K> {
    type V = HashSet<K>;
    #[inline(always)]
    fn exec_view(self) -> Self::V {
        self.iter().cloned().collect()
    }
    #[inline(always)]
    fn exec_deep_view(self) -> Self::V {
        self.exec_view()
    }
}

/// The spec methods of `Option` and `Result`, by their exec twin names.
pub trait DcOption<T> {
    fn exec_is_some(self) -> bool;
    fn exec_is_none(self) -> bool;
}

impl<'a, T> DcOption<T> for &'a Option<T> {
    #[inline(always)]
    fn exec_is_some(self) -> bool {
        self.is_some()
    }
    #[inline(always)]
    fn exec_is_none(self) -> bool {
        self.is_none()
    }
}

pub trait DcResult<T, E> {
    fn exec_is_ok(self) -> bool;
    fn exec_is_err(self) -> bool;
    fn exec_unwrap(self) -> T;
    fn exec_unwrap_err(self) -> E;
}

impl<'a, T: Clone, E: Clone> DcResult<T, E> for &'a Result<T, E> {
    #[inline(always)]
    fn exec_is_ok(self) -> bool {
        self.is_ok()
    }
    #[inline(always)]
    fn exec_is_err(self) -> bool {
        self.is_err()
    }
    #[inline(always)]
    fn exec_unwrap(self) -> T {
        match self {
            Ok(t) => t.clone(),
            Err(_) => panic!("dyncov: unwrap on Err"),
        }
    }
    #[inline(always)]
    fn exec_unwrap_err(self) -> E {
        match self {
            Err(e) => e.clone(),
            Ok(_) => panic!("dyncov: unwrap_err on Ok"),
        }
    }
}

/// More of vstd's `Seq`, `Set` and `Map` vocabulary.
pub trait DcSeqMore<T> {
    fn exec_no_duplicates(self) -> bool;
    fn exec_to_set(self) -> HashSet<T>;
    fn exec_reverse(self) -> Vec<T>;
    fn exec_is_empty(self) -> bool;
}

impl<'a, T: Clone + PartialEq> DcSeqMore<T> for &'a [T] {
    fn exec_no_duplicates(self) -> bool {
        self.iter().enumerate().all(|(i, x)| !self[..i].contains(x))
    }
    fn exec_to_set(self) -> HashSet<T> {
        panic!("dyncov: Seq::to_set needs Hash + Eq elements (see DcSeqToSet)")
    }
    fn exec_reverse(self) -> Vec<T> {
        let mut v = self.to_vec();
        v.reverse();
        v
    }
    fn exec_is_empty(self) -> bool {
        self.is_empty()
    }
}

pub trait DcSetMore {
    fn exec_finite(self) -> bool;
    fn exec_is_empty(self) -> bool;
}

impl<'a, K> DcSetMore for &'a HashSet<K> {
    #[inline(always)]
    fn exec_finite(self) -> bool {
        true
    }
    #[inline(always)]
    fn exec_is_empty(self) -> bool {
        self.is_empty()
    }
}

pub trait DcMapMore {
    fn exec_finite(self) -> bool;
    fn exec_is_empty(self) -> bool;
}

impl<'a, K, V> DcMapMore for &'a std::collections::HashMap<K, V> {
    #[inline(always)]
    fn exec_finite(self) -> bool {
        true
    }
    #[inline(always)]
    fn exec_is_empty(self) -> bool {
        self.is_empty()
    }
}

/// A name a pattern bound: a reference into the scrutinee. An integer
/// becomes a `SpecInt` value; anything else keeps its reference. The engine
/// emits `dc_val(&x)`: for `x: &u64` the receiver `&&u64` has an impl of
/// its own, for `x: &T` the triple-reference fallback applies by auto-ref.
pub trait DcVal {
    type Out;
    fn dc_val(self) -> Self::Out;
}

macro_rules! impl_dc_val_int {
    ($($t:ty),* $(,)?) => {
        $(
            impl<'a, 'b> DcVal for &'b &'a $t {
                type Out = SpecInt;
                #[inline(always)]
                fn dc_val(self) -> SpecInt { __vcheck_int::lift(**self) }
            }
        )*
    };
}

impl_dc_val_int!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

/// The other primitives are values too (the lowering takes them by value).
macro_rules! impl_dc_val_copy {
    ($($t:ty),* $(,)?) => {
        $(
            impl<'a, 'b> DcVal for &'b &'a $t {
                type Out = $t;
                #[inline(always)]
                fn dc_val(self) -> $t { **self }
            }
        )*
    };
}

impl_dc_val_copy!(bool, char, f32, f64, ());

impl<'a, 'b, 'c, T: ?Sized> DcVal for &'c &'b &'a T {
    type Out = &'a T;
    #[inline(always)]
    fn dc_val(self) -> &'a T {
        **self
    }
}

#[cfg(test)]
mod dc_val_tests {
    use super::*;

    #[test]
    fn pattern_bindings_normalize() {
        let r: &u64 = &5;
        assert_eq!((&r).dc_val(), 5i128);
        let b: &bool = &true;
        assert_eq!((&b).dc_val(), true);
        let f: f64 = 1.5;
        assert_eq!((&f).dc_val(), 1.5);
        let s: &str = "x";
        assert_eq!((&s).dc_val(), "x");
        let v: &Vec<u8> = &vec![1];
        assert_eq!((&v).dc_val().len(), 1);
        let n: u8 = 7;
        assert_eq!((&n).dc_val(), 7i128);
    }
}

/// Executable meanings of the vstd spec functions the lowering knows
/// (called as `::verus_dyncov::rt::vstd_fns::<name>`).
pub mod vstd_fns {
    /// `vstd::std_specs::btree::increasing_seq`: strictly increasing.
    pub fn increasing_seq<K: PartialOrd>(s: &[K]) -> bool {
        s.windows(2).all(|w| w[0] < w[1])
    }
}

#[cfg(test)]
mod vstd_fns_tests {
    #[test]
    fn increasing_seq_is_strict() {
        assert!(super::vstd_fns::increasing_seq::<i32>(&[]));
        assert!(super::vstd_fns::increasing_seq(&["a".to_string(), "b".to_string()]));
        assert!(!super::vstd_fns::increasing_seq(&[1, 1]));
        assert!(!super::vstd_fns::increasing_seq(&[2, 1]));
    }
}
