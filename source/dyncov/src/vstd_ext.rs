//! The `exec_spec` companions of the vstd spec types, as the
//! verus-spec-check engine's generated code expects them (the crate
//! `verus_spec_check_vstd_ext`, itself a copy of `vstd::contrib::exec_spec`),
//! ported without vstd: the traits lose the `DeepView` bounds and the
//! `ensures` that only matter to the verified flavor of the engine. The
//! `verus!` macro rewrites the engine's `::verus_spec_check_vstd_ext::`
//! paths to `::verus_dyncov::vstd_ext::`.
//!
//! The engine's conventions: a value flows in "ref" or "owned" mode;
//! `get_ref` converts an owned value's borrow to its ref form (`&Vec<T>`
//! to `&[T]`, `&String` to `&str`, `&u8` to `u8`) and `get_owned` the ref
//! form back to owned. A spec type `S` names its two exec forms through
//! [`ExecSpecType`]; the dyncov mode of the engine gives every exec type
//! declared inside `verus!` identity impls of all of these traits.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

pub trait ToRef<T> {
    fn get_ref(self) -> T;
}

pub trait ToOwned<T> {
    fn get_owned(self) -> T;
}

pub trait DeepViewClone: Sized {
    fn deep_clone(&self) -> Self;
}

impl<T: Clone> DeepViewClone for T {
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        self.clone()
    }
}

/// A value of any other type reads as a reference to itself (method
/// resolution reaches this impl by auto-ref when no impl above applies
/// to the receiver's own type).
impl<'a, 'b, T: ?Sized> ToRef<&'a T> for &'b &'a T {
    #[inline(always)]
    fn get_ref(self) -> &'a T {
        *self
    }
}

/// ... and clones into its owned form.
impl<'a, 'b, T: Clone> ToOwned<T> for &'b &'a T {
    #[inline(always)]
    fn get_owned(self) -> T {
        (**self).clone()
    }
}

/// The exec forms (owned and borrowed) of a spec type.
pub trait ExecSpecType {
    type ExecOwnedType;
    type ExecRefType<'a>;
}

/// Executable equality of two values in ref form.
pub trait ExecSpecEq<'a>: Sized {
    type Other;
    fn exec_eq(this: Self, other: Self::Other) -> bool;
}

/// Executable `Seq` and `str` indexing.
pub trait ExecSpecIndex<'a>: Sized {
    type Elem;
    fn exec_index(self, index: usize) -> Self::Elem;
}

pub trait ExecSpecLen {
    fn exec_len(self) -> usize;
}

/// The engine compiles `SpecString` (vstd's alias of `Seq<char>`) to
/// `String` / `&str`; this stands for it in paths the engine emits.
pub struct SpecString;

impl ExecSpecType for SpecString {
    type ExecOwnedType = String;
    type ExecRefType<'a> = &'a str;
}

macro_rules! impl_primitives {
    ($($t:ty),* $(,)?) => {
        $(
            impl ExecSpecType for $t {
                type ExecOwnedType = $t;
                type ExecRefType<'a> = $t;
            }

            impl<'a> ToRef<$t> for &'a $t {
                #[inline(always)]
                fn get_ref(self) -> $t {
                    *self
                }
            }

            impl ToOwned<$t> for $t {
                #[inline(always)]
                fn get_owned(self) -> $t {
                    self
                }
            }

            impl<'a> ExecSpecEq<'a> for $t {
                type Other = $t;

                #[inline(always)]
                fn exec_eq(this: Self, other: Self::Other) -> bool {
                    this == other
                }
            }

            impl<'a> ExecSpecEq<'a> for &'a $t {
                type Other = &'a $t;

                #[inline(always)]
                fn exec_eq(this: Self, other: Self::Other) -> bool {
                    this == other
                }
            }
        )*
    };
}

impl_primitives! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
    bool, char, f32, f64, (),
}

macro_rules! impl_exec_spec_tuple {
    ([$( ($T:ident, $n:tt) ),*]) => {
        impl<'a, $($T),*> ToRef<&'a ($($T,)*)> for &'a ($($T,)*) {
            #[inline(always)]
            fn get_ref(self) -> &'a ($($T,)*) {
                self
            }
        }

        impl<'a, $($T: Clone),*> ToOwned<($($T,)*)> for &'a ($($T,)*) {
            #[inline(always)]
            fn get_owned(self) -> ($($T,)*) {
                self.deep_clone()
            }
        }

        impl<'a, $($T),*> ExecSpecEq<'a> for &'a ($($T,)*)
        where
            $( &'a $T: ExecSpecEq<'a, Other = &'a $T>, )*
        {
            type Other = &'a ($($T,)*);

            #[inline(always)]
            #[allow(non_snake_case)]
            fn exec_eq(this: Self, other: Self::Other) -> bool {
                $( <&$T>::exec_eq(&this.$n, &other.$n) )&&*
            }
        }
    };
}

impl_exec_spec_tuple!([(T0, 0)]);
impl_exec_spec_tuple!([(T0, 0), (T1, 1)]);
impl_exec_spec_tuple!([(T0, 0), (T1, 1), (T2, 2)]);
impl_exec_spec_tuple!([(T0, 0), (T1, 1), (T2, 2), (T3, 3)]);

/// A boxed field reads as a reference to its content, as it does in spec
/// code.
impl<'a, T> ToRef<&'a T> for &'a Box<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a T {
        self
    }
}

impl<'a, T> ExecSpecEq<'a> for &'a Box<T>
where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
{
    type Other = &'a Box<T>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        <&T>::exec_eq(this, other)
    }
}

// ---------------------------------------------------------------------------
// Seq: Vec<T> owned, &[T] borrowed

impl<'a, T> ToRef<&'a [T]> for &'a Vec<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a [T] {
        self.as_slice()
    }
}

impl<'a, T: Clone> ToOwned<Vec<T>> for &'a [T] {
    #[inline(always)]
    fn get_owned(self) -> Vec<T> {
        self.iter().map(|x| x.deep_clone()).collect()
    }
}

impl<'a, T> ExecSpecEq<'a> for &'a [T]
where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
{
    type Other = &'a [T];

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        this.len() == other.len()
            && this.iter().zip(other.iter()).all(|(a, b)| <&'a T>::exec_eq(a, b))
    }
}

impl<'a, T> ExecSpecEq<'a> for &'a Vec<T>
where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
{
    type Other = &'a Vec<T>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        <&'a [T]>::exec_eq(this.as_slice(), other.as_slice())
    }
}

impl<'a, T> ExecSpecLen for &'a [T] {
    #[inline(always)]
    fn exec_len(self) -> usize {
        self.len()
    }
}

impl<'a, T> ExecSpecLen for &'a Vec<T> {
    #[inline(always)]
    fn exec_len(self) -> usize {
        self.len()
    }
}

impl<'a, T> ExecSpecIndex<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_index(self, index: usize) -> Self::Elem {
        self.get(index).expect("dyncov: Seq index out of bounds")
    }
}

impl<'a, T> ExecSpecIndex<'a> for &'a Vec<T> {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_index(self, index: usize) -> Self::Elem {
        self.get(index).expect("dyncov: Seq index out of bounds")
    }
}

pub trait ExecSpecSeqAdd<'a, Out>: Sized {
    fn exec_add(self, rhs: Self) -> Out;
}

pub trait ExecSpecSeqPush<'a, Out>: Sized {
    type Elem;
    fn exec_push(self, a: Self::Elem) -> Out;
}

pub trait ExecSpecSeqUpdate<'a, Out>: Sized {
    type Elem;
    fn exec_update(self, i: usize, a: Self::Elem) -> Out;
}

pub trait ExecSpecSeqSubrange<'a>: Sized {
    fn exec_subrange(self, start_inclusive: usize, end_exclusive: usize) -> Self;
}

pub trait ExecSpecSeqEmpty: Sized {
    fn exec_empty() -> Self;
}

pub trait ExecSpecSeqToMultiset<'a>: Sized {
    type Elem: Hash + Eq;
    fn exec_to_multiset(self) -> ExecMultiset<Self::Elem>;
}

pub trait ExecSpecSeqDropFirst<'a>: Sized {
    fn exec_drop_first(self) -> Self;
}

pub trait ExecSpecSeqDropLast<'a>: Sized {
    fn exec_drop_last(self) -> Self;
}

pub trait ExecSpecSeqTake<'a>: Sized {
    fn exec_take(self, n: usize) -> Self;
}

pub trait ExecSpecSeqSkip<'a>: Sized {
    fn exec_skip(self, n: usize) -> Self;
}

pub trait ExecSpecSeqLast<'a>: Sized {
    type Elem;
    fn exec_last(self) -> Self::Elem;
}

pub trait ExecSpecSeqFirst<'a>: Sized {
    type Elem;
    fn exec_first(self) -> Self::Elem;
}

pub trait ExecSpecSeqIsPrefixOf<'a>: Sized {
    type Other;
    fn exec_is_prefix_of(self, other: Self::Other) -> bool;
}

pub trait ExecSpecSeqIsSuffixOf<'a>: Sized {
    type Other;
    fn exec_is_suffix_of(self, other: Self::Other) -> bool;
}

pub trait ExecSpecSeqContains<'a>: Sized {
    type Elem;
    fn exec_contains(self, needle: Self::Elem) -> bool;
}

pub trait ExecSpecSeqIndexOf<'a>: Sized {
    type Elem;
    fn exec_index_of(self, needle: Self::Elem) -> usize;
}

pub trait ExecSpecSeqIndexOfFirst<'a>: Sized {
    type Elem;
    fn exec_index_of_first(self, needle: Self::Elem) -> Option<usize>;
}

pub trait ExecSpecSeqIndexOfLast<'a>: Sized {
    type Elem;
    fn exec_index_of_last(self, needle: Self::Elem) -> Option<usize>;
}

impl<'a, T: Clone> ExecSpecSeqAdd<'a, Vec<T>> for &'a [T] {
    #[inline(always)]
    fn exec_add(self, rhs: Self) -> Vec<T> {
        self.get_owned().into_iter().chain(rhs.get_owned()).collect()
    }
}

impl<'a, T: Clone> ExecSpecSeqPush<'a, Vec<T>> for &'a [T] {
    type Elem = T;

    #[inline(always)]
    fn exec_push(self, a: Self::Elem) -> Vec<T> {
        let mut v = self.get_owned();
        v.push(a);
        v
    }
}

impl<'a, T: Clone> ExecSpecSeqUpdate<'a, Vec<T>> for &'a [T] {
    type Elem = T;

    #[inline(always)]
    fn exec_update(self, i: usize, a: Self::Elem) -> Vec<T> {
        let mut v: Vec<T> = self.get_owned();
        v[i] = a;
        v
    }
}

impl<'a, T> ExecSpecSeqSubrange<'a> for &'a [T] {
    #[inline(always)]
    fn exec_subrange(self, start_inclusive: usize, end_exclusive: usize) -> Self {
        &self[start_inclusive..end_exclusive]
    }
}

impl<T> ExecSpecSeqEmpty for Vec<T> {
    #[inline(always)]
    fn exec_empty() -> Self {
        Vec::new()
    }
}

impl<'a, T: Clone + Hash + Eq> ExecSpecSeqToMultiset<'a> for &'a [T] {
    type Elem = T;

    #[inline(always)]
    fn exec_to_multiset(self) -> ExecMultiset<Self::Elem> {
        let mut mset = ExecMultiset { m: HashMap::new() };
        for e in self.iter() {
            match mset.m.remove_entry(e) {
                Some((k, c)) => {
                    mset.m.insert(k, c + 1);
                }
                None => {
                    mset.m.insert(e.clone(), 1);
                }
            }
        }
        mset
    }
}

impl<'a, T> ExecSpecSeqDropFirst<'a> for &'a [T] {
    #[inline(always)]
    fn exec_drop_first(self) -> Self {
        &self[1..]
    }
}

impl<'a, T> ExecSpecSeqDropLast<'a> for &'a [T] {
    #[inline(always)]
    fn exec_drop_last(self) -> Self {
        &self[..self.len() - 1]
    }
}

impl<'a, T> ExecSpecSeqTake<'a> for &'a [T] {
    #[inline(always)]
    fn exec_take(self, n: usize) -> Self {
        &self[..n]
    }
}

impl<'a, T> ExecSpecSeqSkip<'a> for &'a [T] {
    #[inline(always)]
    fn exec_skip(self, n: usize) -> Self {
        &self[n..]
    }
}

impl<'a, T> ExecSpecSeqLast<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_last(self) -> Self::Elem {
        self.last().expect("dyncov: Seq::last on empty sequence")
    }
}

impl<'a, T> ExecSpecSeqFirst<'a> for &'a [T] {
    type Elem = &'a T;

    #[inline(always)]
    fn exec_first(self) -> Self::Elem {
        self.first().expect("dyncov: Seq::first on empty sequence")
    }
}

impl<'a, T: PartialEq> ExecSpecSeqIsPrefixOf<'a> for &'a [T] {
    type Other = &'a [T];

    #[inline(always)]
    fn exec_is_prefix_of(self, other: Self::Other) -> bool {
        other.starts_with(self)
    }
}

impl<'a, T: PartialEq> ExecSpecSeqIsSuffixOf<'a> for &'a [T] {
    type Other = &'a [T];

    #[inline(always)]
    fn exec_is_suffix_of(self, other: Self::Other) -> bool {
        other.ends_with(self)
    }
}

impl<'a, T: PartialEq> ExecSpecSeqContains<'a> for &'a [T] {
    type Elem = T;

    #[inline(always)]
    fn exec_contains(self, needle: Self::Elem) -> bool {
        self.iter().any(|e| *e == needle)
    }
}

impl<'a, T: PartialEq> ExecSpecSeqIndexOf<'a> for &'a [T] {
    type Elem = T;

    #[inline(always)]
    fn exec_index_of(self, needle: Self::Elem) -> usize {
        self.iter().position(|e| *e == needle).unwrap_or(self.len())
    }
}

impl<'a, T: PartialEq> ExecSpecSeqIndexOfFirst<'a> for &'a [T] {
    type Elem = T;

    #[inline(always)]
    fn exec_index_of_first(self, needle: Self::Elem) -> Option<usize> {
        self.iter().position(|e| *e == needle)
    }
}

impl<'a, T: PartialEq> ExecSpecSeqIndexOfLast<'a> for &'a [T] {
    type Elem = T;

    #[inline(always)]
    fn exec_index_of_last(self, needle: Self::Elem) -> Option<usize> {
        self.iter().rposition(|e| *e == needle)
    }
}

// ---------------------------------------------------------------------------
// String: String owned, &str borrowed (a Seq<char>)

impl<'a> ToRef<&'a str> for &'a String {
    #[inline(always)]
    fn get_ref(self) -> &'a str {
        self.as_str()
    }
}

impl<'a> ToOwned<String> for &'a str {
    #[inline(always)]
    fn get_owned(self) -> String {
        self.to_string()
    }
}

impl<'a> ExecSpecEq<'a> for &'a str {
    type Other = &'a str;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        this == other
    }
}

impl<'a> ExecSpecEq<'a> for &'a String {
    type Other = &'a String;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        this == other
    }
}

impl<'a> ExecSpecLen for &'a str {
    #[inline(always)]
    fn exec_len(self) -> usize {
        self.chars().count()
    }
}

impl<'a> ExecSpecLen for &'a String {
    #[inline(always)]
    fn exec_len(self) -> usize {
        self.chars().count()
    }
}

impl<'a> ExecSpecIndex<'a> for &'a str {
    type Elem = char;

    #[inline(always)]
    fn exec_index(self, index: usize) -> Self::Elem {
        self.chars().nth(index).expect("dyncov: str index out of bounds")
    }
}

impl<'a> ExecSpecIndex<'a> for &'a String {
    type Elem = char;

    #[inline(always)]
    fn exec_index(self, index: usize) -> Self::Elem {
        self.chars().nth(index).expect("dyncov: str index out of bounds")
    }
}

/// The byte offset of the `n`-th char, or the length for `n == chars`.
fn char_offset(s: &str, n: usize) -> usize {
    s.char_indices().nth(n).map(|(i, _)| i).unwrap_or(s.len())
}

impl<'a> ExecSpecSeqSubrange<'a> for &'a str {
    #[inline(always)]
    fn exec_subrange(self, start_inclusive: usize, end_exclusive: usize) -> Self {
        &self[char_offset(self, start_inclusive)..char_offset(self, end_exclusive)]
    }
}

impl<'a> ExecSpecSeqTake<'a> for &'a str {
    #[inline(always)]
    fn exec_take(self, n: usize) -> Self {
        &self[..char_offset(self, n)]
    }
}

impl<'a> ExecSpecSeqSkip<'a> for &'a str {
    #[inline(always)]
    fn exec_skip(self, n: usize) -> Self {
        &self[char_offset(self, n)..]
    }
}

impl<'a> ExecSpecSeqDropFirst<'a> for &'a str {
    #[inline(always)]
    fn exec_drop_first(self) -> Self {
        &self[char_offset(self, 1)..]
    }
}

impl<'a> ExecSpecSeqDropLast<'a> for &'a str {
    #[inline(always)]
    fn exec_drop_last(self) -> Self {
        let n = self.chars().count();
        &self[..char_offset(self, n.saturating_sub(1))]
    }
}

impl<'a> ExecSpecSeqLast<'a> for &'a str {
    type Elem = char;

    #[inline(always)]
    fn exec_last(self) -> char {
        self.chars().last().expect("dyncov: Seq::last on empty string")
    }
}

impl<'a> ExecSpecSeqFirst<'a> for &'a str {
    type Elem = char;

    #[inline(always)]
    fn exec_first(self) -> char {
        self.chars().next().expect("dyncov: Seq::first on empty string")
    }
}

impl<'a> ExecSpecSeqContains<'a> for &'a str {
    type Elem = char;

    #[inline(always)]
    fn exec_contains(self, needle: char) -> bool {
        self.chars().any(|c| c == needle)
    }
}

impl<'a> ExecSpecSeqIndexOf<'a> for &'a str {
    type Elem = char;

    #[inline(always)]
    fn exec_index_of(self, needle: char) -> usize {
        self.chars().position(|c| c == needle).unwrap_or_else(|| self.chars().count())
    }
}

impl<'a> ExecSpecSeqIsPrefixOf<'a> for &'a str {
    type Other = &'a str;

    #[inline(always)]
    fn exec_is_prefix_of(self, other: Self::Other) -> bool {
        other.starts_with(self)
    }
}

impl<'a> ExecSpecSeqIsSuffixOf<'a> for &'a str {
    type Other = &'a str;

    #[inline(always)]
    fn exec_is_suffix_of(self, other: Self::Other) -> bool {
        other.ends_with(self)
    }
}

impl<'a> ExecSpecSeqPush<'a, String> for &'a str {
    type Elem = char;

    #[inline(always)]
    fn exec_push(self, a: char) -> String {
        let mut s = String::from(self);
        s.push(a);
        s
    }
}

impl<'a> ExecSpecSeqAdd<'a, String> for &'a str {
    #[inline(always)]
    fn exec_add(self, rhs: Self) -> String {
        let mut s = String::from(self);
        s.push_str(rhs);
        s
    }
}

impl<'a> ExecSpecSeqUpdate<'a, String> for &'a str {
    type Elem = char;

    #[inline(always)]
    fn exec_update(self, i: usize, a: char) -> String {
        self.chars().enumerate().map(|(j, c)| if j == i { a } else { c }).collect()
    }
}

// ---------------------------------------------------------------------------
// Option

impl<'a, T> ToRef<&'a Option<T>> for &'a Option<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a Option<T> {
        self
    }
}

impl<'a, T: Clone> ToOwned<Option<T>> for &'a Option<T> {
    #[inline(always)]
    fn get_owned(self) -> Option<T> {
        self.deep_clone()
    }
}

impl<'a, T> ExecSpecEq<'a> for &'a Option<T>
where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
{
    type Other = &'a Option<T>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        match (this, other) {
            (Some(t1), Some(t2)) => <&'a T>::exec_eq(t1, t2),
            (None, None) => true,
            _ => false,
        }
    }
}

pub trait ExecSpecOptionUnwrap<'a>: Sized {
    type Elem;
    fn exec_unwrap(self) -> Self::Elem;
}

impl<'a, T: Clone> ExecSpecOptionUnwrap<'a> for &'a Option<T> {
    type Elem = T;

    #[inline(always)]
    fn exec_unwrap(self) -> Self::Elem {
        self.deep_clone().expect("dyncov: unwrap on None")
    }
}

// ---------------------------------------------------------------------------
// Result

impl<'a, T, E> ToRef<&'a Result<T, E>> for &'a Result<T, E> {
    #[inline(always)]
    fn get_ref(self) -> &'a Result<T, E> {
        self
    }
}

impl<'a, T: Clone, E: Clone> ToOwned<Result<T, E>> for &'a Result<T, E> {
    #[inline(always)]
    fn get_owned(self) -> Result<T, E> {
        self.deep_clone()
    }
}

impl<'a, T, E> ExecSpecEq<'a> for &'a Result<T, E>
where
    &'a T: ExecSpecEq<'a, Other = &'a T>,
    &'a E: ExecSpecEq<'a, Other = &'a E>,
{
    type Other = &'a Result<T, E>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        match (this, other) {
            (Ok(a), Ok(b)) => <&'a T>::exec_eq(a, b),
            (Err(a), Err(b)) => <&'a E>::exec_eq(a, b),
            _ => false,
        }
    }
}

// ---------------------------------------------------------------------------
// Set: HashSet<K>

impl<'a, K> ToRef<&'a HashSet<K>> for &'a HashSet<K> {
    #[inline(always)]
    fn get_ref(self) -> &'a HashSet<K> {
        self
    }
}

impl<'a, K: Clone + Hash + Eq> ToOwned<HashSet<K>> for &'a HashSet<K> {
    #[inline(always)]
    fn get_owned(self) -> HashSet<K> {
        self.deep_clone()
    }
}

impl<'a, K: Hash + Eq> ExecSpecEq<'a> for &'a HashSet<K> {
    type Other = &'a HashSet<K>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        this == other
    }
}

impl<'a, K> ExecSpecLen for &'a HashSet<K> {
    #[inline(always)]
    fn exec_len(self) -> usize {
        self.len()
    }
}

pub trait ExecSpecSetContains<'a>: Sized {
    type Elem;
    fn exec_contains(self, elem: Self::Elem) -> bool;
}

pub trait ExecSpecSetInsert<'a, Out>: Sized {
    type Elem;
    fn exec_insert(self, elem: Self::Elem) -> Out;
}

pub trait ExecSpecSetRemove<'a, Out>: Sized {
    type Elem;
    fn exec_remove(self, elem: Self::Elem) -> Out;
}

pub trait ExecSpecSetUnion<'a, Out>: Sized {
    fn exec_union(self, other: Self) -> Out;
}

pub trait ExecSpecSetIntersect<'a, Out>: Sized {
    fn exec_intersect(self, other: Self) -> Out;
}

pub trait ExecSpecSetDifference<'a, Out>: Sized {
    fn exec_difference(self, other: Self) -> Out;
}

pub trait ExecSpecSetEmpty: Sized {
    fn exec_empty() -> Self;
}

impl<'a, K: Hash + Eq> ExecSpecSetContains<'a> for &'a HashSet<K> {
    type Elem = K;

    #[inline(always)]
    fn exec_contains(self, elem: Self::Elem) -> bool {
        self.contains(&elem)
    }
}

impl<'a, K: Clone + Hash + Eq> ExecSpecSetInsert<'a, HashSet<K>> for &'a HashSet<K> {
    type Elem = K;

    #[inline(always)]
    fn exec_insert(self, elem: Self::Elem) -> HashSet<K> {
        let mut s = self.deep_clone();
        s.insert(elem);
        s
    }
}

impl<'a, K: Clone + Hash + Eq> ExecSpecSetRemove<'a, HashSet<K>> for &'a HashSet<K> {
    type Elem = K;

    #[inline(always)]
    fn exec_remove(self, elem: Self::Elem) -> HashSet<K> {
        let mut s = self.deep_clone();
        s.remove(&elem);
        s
    }
}

impl<'a, K: Clone + Hash + Eq> ExecSpecSetUnion<'a, HashSet<K>> for &'a HashSet<K> {
    #[inline(always)]
    fn exec_union(self, other: Self) -> HashSet<K> {
        self.union(other).map(|k| k.deep_clone()).collect()
    }
}

impl<'a, K: Clone + Hash + Eq> ExecSpecSetIntersect<'a, HashSet<K>> for &'a HashSet<K> {
    #[inline(always)]
    fn exec_intersect(self, other: Self) -> HashSet<K> {
        self.intersection(other).map(|k| k.deep_clone()).collect()
    }
}

impl<'a, K: Clone + Hash + Eq> ExecSpecSetDifference<'a, HashSet<K>> for &'a HashSet<K> {
    #[inline(always)]
    fn exec_difference(self, other: Self) -> HashSet<K> {
        self.difference(other).map(|k| k.deep_clone()).collect()
    }
}

impl<K> ExecSpecSetEmpty for HashSet<K> {
    #[inline(always)]
    fn exec_empty() -> Self {
        HashSet::new()
    }
}

// ---------------------------------------------------------------------------
// Map: HashMap<K, V>

impl<'a, K, V> ToRef<&'a HashMap<K, V>> for &'a HashMap<K, V> {
    #[inline(always)]
    fn get_ref(self) -> &'a HashMap<K, V> {
        self
    }
}

impl<'a, K: Clone + Hash + Eq, V: Clone> ToOwned<HashMap<K, V>> for &'a HashMap<K, V> {
    #[inline(always)]
    fn get_owned(self) -> HashMap<K, V> {
        self.deep_clone()
    }
}

impl<'a, K: Hash + Eq, V> ExecSpecEq<'a> for &'a HashMap<K, V>
where
    &'a V: ExecSpecEq<'a, Other = &'a V>,
{
    type Other = &'a HashMap<K, V>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        this.len() == other.len()
            && this.iter().all(|(k, v)| other.get(k).map_or(false, |w| <&'a V>::exec_eq(v, w)))
    }
}

impl<'a, K, V> ExecSpecLen for &'a HashMap<K, V> {
    #[inline(always)]
    fn exec_len(self) -> usize {
        self.len()
    }
}

pub trait ExecSpecMapDom<'a, Out>: Sized {
    fn exec_dom(self) -> Out;
}

pub trait ExecSpecMapGet<'a>: Sized {
    type Key;
    type Value;
    fn exec_get(self, key: Self::Key) -> Option<Self::Value>;
}

pub trait ExecSpecMapContainsKey<'a>: Sized {
    type Key;
    fn exec_contains_key(self, key: Self::Key) -> bool;
}

pub trait ExecSpecMapInsert<'a, Out>: Sized {
    type Key;
    type Value;
    fn exec_insert(self, key: Self::Key, value: Self::Value) -> Out;
}

pub trait ExecSpecMapRemove<'a, Out>: Sized {
    type Key;
    fn exec_remove(self, key: Self::Key) -> Out;
}

pub trait ExecSpecMapEmpty: Sized {
    fn exec_empty() -> Self;
}

impl<'a, K: Clone + Hash + Eq, V> ExecSpecMapDom<'a, HashSet<K>> for &'a HashMap<K, V> {
    #[inline(always)]
    fn exec_dom(self) -> HashSet<K> {
        self.keys().map(|k| k.deep_clone()).collect()
    }
}

impl<'a, K: Hash + Eq, V: Clone> ExecSpecMapGet<'a> for &'a HashMap<K, V> {
    type Key = K;
    type Value = V;

    #[inline(always)]
    fn exec_get(self, key: Self::Key) -> Option<Self::Value> {
        self.get(&key).map(|v| v.deep_clone())
    }
}

impl<'a, K: Hash + Eq, V> ExecSpecMapContainsKey<'a> for &'a HashMap<K, V> {
    type Key = K;

    #[inline(always)]
    fn exec_contains_key(self, key: Self::Key) -> bool {
        self.contains_key(&key)
    }
}

impl<'a, K: Hash + Eq, V> ExecSpecIndex<'a> for &'a HashMap<K, V>
where
    K: From<usize>,
{
    type Elem = &'a V;

    #[inline(always)]
    fn exec_index(self, index: usize) -> Self::Elem {
        self.get(&K::from(index)).expect("dyncov: Map::index on an absent key")
    }
}

impl<'a, K: Clone + Hash + Eq, V: Clone> ExecSpecMapInsert<'a, HashMap<K, V>>
    for &'a HashMap<K, V>
{
    type Key = K;
    type Value = V;

    #[inline(always)]
    fn exec_insert(self, key: Self::Key, value: Self::Value) -> HashMap<K, V> {
        let mut m = self.deep_clone();
        m.insert(key, value);
        m
    }
}

impl<'a, K: Clone + Hash + Eq, V: Clone> ExecSpecMapRemove<'a, HashMap<K, V>>
    for &'a HashMap<K, V>
{
    type Key = K;

    #[inline(always)]
    fn exec_remove(self, key: Self::Key) -> HashMap<K, V> {
        let mut m = self.deep_clone();
        m.remove(&key);
        m
    }
}

impl<K, V> ExecSpecMapEmpty for HashMap<K, V> {
    #[inline(always)]
    fn exec_empty() -> Self {
        HashMap::new()
    }
}

// ---------------------------------------------------------------------------
// Multiset

/// The exec form of `Multiset<T>`: element → count.
#[derive(Clone, Debug)]
pub struct ExecMultiset<T: Hash + Eq> {
    pub m: HashMap<T, usize>,
}

impl<T: Hash + Eq> ExecMultiset<T> {
    pub fn count_of(&self, t: &T) -> usize {
        self.m.get(t).copied().unwrap_or(0)
    }
}

impl<'a, T: Hash + Eq> ToRef<&'a ExecMultiset<T>> for &'a ExecMultiset<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a ExecMultiset<T> {
        self
    }
}

impl<'a, T: Clone + Hash + Eq> ToOwned<ExecMultiset<T>> for &'a ExecMultiset<T> {
    #[inline(always)]
    fn get_owned(self) -> ExecMultiset<T> {
        self.deep_clone()
    }
}

impl<'a, T: Hash + Eq> ExecSpecEq<'a> for &'a ExecMultiset<T> {
    type Other = &'a ExecMultiset<T>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        this.m.len() == other.m.len() && this.m.iter().all(|(k, c)| other.m.get(k) == Some(c))
    }
}

impl<'a, T: Hash + Eq> ExecSpecLen for &'a ExecMultiset<T> {
    #[inline(always)]
    fn exec_len(self) -> usize {
        self.m.values().sum()
    }
}

pub trait ExecSpecMultisetCount<'a>: Sized {
    type Elem;
    fn exec_count(self, elem: Self::Elem) -> usize;
}

impl<'a, T: Hash + Eq> ExecSpecMultisetCount<'a> for &'a ExecMultiset<T> {
    type Elem = T;

    #[inline(always)]
    fn exec_count(self, elem: Self::Elem) -> usize {
        self.count_of(&elem)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seq_companions() {
        let v = vec![1u8, 2, 3];
        let s: &[u8] = (&v).get_ref();
        assert_eq!(s.exec_len(), 3);
        assert_eq!(*s.exec_index(1), 2);
        assert_eq!(s.exec_subrange(1, 3), &[2, 3]);
        assert!(<&[u8]>::exec_eq(s.exec_take(2), &[1, 2]));
        assert_eq!(s.exec_push(4), vec![1, 2, 3, 4]);
        assert!(s.exec_is_prefix_of(&[1, 2, 3, 4]));
        assert!(s.exec_contains(3));
        assert_eq!(s.exec_index_of_first(9), None);
        let w: Vec<u8> = s.get_owned();
        assert_eq!(w, v);
        assert!(<&(u8, Vec<u8>)>::exec_eq(&(1, vec![2]), &(1, vec![2])));
    }

    #[test]
    fn string_and_option() {
        let s = String::from("héllo");
        let r: &str = (&s).get_ref();
        assert_eq!(r.exec_len(), 5);
        assert_eq!(r.exec_index(1), 'é');
        let o = Some(3u8);
        assert_eq!((&o).exec_unwrap(), 3);
        assert!(<&Option<u8>>::exec_eq(&o, &Some(3)));
    }
}
