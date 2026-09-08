use crate::ast::{AssertId, Ident};
use std::sync::Arc;

pub const PREFIX_LABEL: &str = "%%location_label%%";
pub const GLOBAL_PREFIX_LABEL: &str = "%%global_location_label%%";
const BREAK_LABEL: &str = "%%break_label%%";
pub const SWITCH_LABEL: &str = "%%switch_label%%";
pub const FUNCTION: &str = "%%Function%%";
pub const ARRAY: &str = "%%array%%";
pub const LAMBDA: &str = "%%lambda%%";
pub const CHOOSE: &str = "%%choose%%";
pub const HOLE: &str = "%%hole%%";
pub const APPLY: &str = "%%apply%%";
pub const TEMP: &str = "%%x%%";
pub const SKOLEM_ID_PREFIX: &str = "skolem";
pub const ARRAY_QID: &str = "__AIR_ARRAY_QID__";

pub fn mk_skolem_id(qid: &str) -> String {
    format!("{}_{}", crate::def::SKOLEM_ID_PREFIX, qid)
}

pub(crate) fn break_label(label: &Ident) -> Ident {
    Arc::new(format!("{}{}", BREAK_LABEL, label))
}

// ---------------------------------------------------------------------------
// Provenance tags: the symbols Verus puts on the wire as `:assert-id` so that
// cvc5's `(get-assertion-sources)` can name, per preprocessed assertion, the
// goals, hypotheses and axioms it was derived from. A tag must be a bare
// SMT-LIB symbol: no colons (an unquoted attribute value cannot contain
// them) and no `|` quoting (sise, which parses the solver's replies, cannot
// read it). `!`, `.`, `%` and `_` are all legal in a simple symbol and are
// what AIR identifiers already use.

/// Prefix of a goal tag: `aid_3_1_2` is the `AssertId` `[3, 1, 2]`.
pub const ASSERT_ID_PREFIX: &str = "aid_";
/// Prefix of an axiom tag: `ax_` followed by the axiom's AIR identifier.
pub const AXIOM_TAG_PREFIX: &str = "ax_";
/// Prefix of a hypothesis tag: `hyp_7` is `HypId(7)`.
pub const HYP_TAG_PREFIX: &str = "hyp_";
/// The tag of the negated query assertion, which holds every goal.
pub const QUERY_TAG: &str = "query";

/// Identifies one hypothesis (`requires` clause or straight-line `assume`)
/// within a query; minted per function in `ast_to_sst`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct HypId(pub u64);

/// Where a top-level assertion came from, as put on the wire.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ProvenanceTag {
    /// A goal (the negated query or a labelled assertion inside it).
    Assert(AssertId),
    /// A module-level axiom, by its AIR identifier.
    Axiom(Ident),
    /// A hypothesis of the function being checked.
    Hyp(HypId),
    /// The negated query itself: the one assertion all the goals live in.
    Query,
}

/// `[3, 1, 2]` -> `aid_3_1_2`. An empty id prints as `aid_`.
pub fn assert_id_to_symbol(id: &AssertId) -> String {
    let parts: Vec<String> = id.iter().map(|n| n.to_string()).collect();
    format!("{}{}", ASSERT_ID_PREFIX, parts.join("_"))
}

/// Inverse of [`assert_id_to_symbol`]; `None` if `s` is not such a symbol.
pub fn symbol_to_assert_id(s: &str) -> Option<AssertId> {
    let rest = s.strip_prefix(ASSERT_ID_PREFIX)?;
    if rest.is_empty() {
        return Some(Arc::new(vec![]));
    }
    let parts: Option<Vec<u64>> = rest.split('_').map(|p| p.parse::<u64>().ok()).collect();
    parts.map(Arc::new)
}

/// Whether `prefix` is an ancestor of, or equal to, `id`. `AssertId`s are
/// paths: `[3]` is a prefix of `[3, 1, 2]`, and of itself.
pub fn is_prefix(prefix: &AssertId, id: &AssertId) -> bool {
    prefix.len() <= id.len() && prefix.iter().zip(id.iter()).all(|(a, b)| a == b)
}

/// Make an AIR identifier safe as a bare SMT-LIB symbol: the only character
/// AIR identifiers may carry that a simple symbol may not is `:`.
fn sanitize_symbol(s: &str) -> String {
    s.replace(':', "_")
}

impl ProvenanceTag {
    /// The bare symbol put on the wire.
    pub fn to_symbol(&self) -> String {
        match self {
            ProvenanceTag::Assert(id) => assert_id_to_symbol(id),
            ProvenanceTag::Axiom(ident) => {
                format!("{}{}", AXIOM_TAG_PREFIX, sanitize_symbol(ident))
            }
            ProvenanceTag::Hyp(HypId(n)) => format!("{}{}", HYP_TAG_PREFIX, n),
            ProvenanceTag::Query => QUERY_TAG.to_string(),
        }
    }

    /// Inverse of [`ProvenanceTag::to_symbol`] for symbols this module
    /// produced; `None` for anything else (cvc5 prints `?` for an untagged
    /// input, and prelude axioms are untagged until they are given tags).
    /// An axiom identifier that contained `:` comes back sanitised.
    pub fn from_symbol(s: &str) -> Option<ProvenanceTag> {
        if s == QUERY_TAG {
            return Some(ProvenanceTag::Query);
        }
        if let Some(id) = symbol_to_assert_id(s) {
            return Some(ProvenanceTag::Assert(id));
        }
        if let Some(n) = s.strip_prefix(HYP_TAG_PREFIX) {
            return n.parse::<u64>().ok().map(|n| ProvenanceTag::Hyp(HypId(n)));
        }
        if let Some(ident) = s.strip_prefix(AXIOM_TAG_PREFIX) {
            if !ident.is_empty() {
                return Some(ProvenanceTag::Axiom(Arc::new(ident.to_string())));
            }
        }
        None
    }
}

#[cfg(test)]
mod provenance_tests {
    use super::*;

    fn aid(v: &[u64]) -> AssertId {
        Arc::new(v.to_vec())
    }

    #[test]
    fn assert_id_symbol_roundtrip() {
        for v in [&[][..], &[0][..], &[3, 1, 2][..], &[u64::MAX, 7][..]] {
            let id = aid(v);
            let s = assert_id_to_symbol(&id);
            assert!(s.starts_with("aid_"));
            assert_eq!(symbol_to_assert_id(&s).as_deref(), Some(&*id));
        }
        assert_eq!(assert_id_to_symbol(&aid(&[3, 1, 2])), "aid_3_1_2");
    }

    #[test]
    fn assert_id_symbol_rejects_others() {
        for s in ["aid_3_x", "aid3", "hyp_3", "ax_f", "aid_3__1", "", "aid_-1"] {
            assert_eq!(symbol_to_assert_id(s), None, "{}", s);
        }
    }

    #[test]
    fn prefix() {
        assert!(is_prefix(&aid(&[]), &aid(&[3])));
        assert!(is_prefix(&aid(&[3]), &aid(&[3, 1, 2])));
        assert!(is_prefix(&aid(&[3, 1, 2]), &aid(&[3, 1, 2])));
        assert!(!is_prefix(&aid(&[3, 1, 2]), &aid(&[3, 1])));
        assert!(!is_prefix(&aid(&[3, 2]), &aid(&[3, 1, 2])));
    }

    #[test]
    fn tag_symbols_roundtrip() {
        let tags = [
            ProvenanceTag::Assert(aid(&[5, 0])),
            ProvenanceTag::Hyp(HypId(7)),
            ProvenanceTag::Axiom(Arc::new("fixture!ax_f_nonneg.".to_string())),
            ProvenanceTag::Axiom(Arc::new("fuel%vstd!seq.axiom_seq_len.".to_string())),
            ProvenanceTag::Query,
        ];
        for t in tags.iter() {
            let s = t.to_symbol();
            assert_eq!(ProvenanceTag::from_symbol(&s).as_ref(), Some(t), "{}", s);
        }
        assert_eq!(tags[0].to_symbol(), "aid_5_0");
        assert_eq!(tags[1].to_symbol(), "hyp_7");
        assert_eq!(tags[2].to_symbol(), "ax_fixture!ax_f_nonneg.");
        assert_eq!(tags[4].to_symbol(), "query");
    }

    #[test]
    fn tag_symbols_are_bare_and_sise_readable() {
        let tags = [
            ProvenanceTag::Assert(aid(&[3, 1, 2])),
            ProvenanceTag::Hyp(HypId(0)),
            ProvenanceTag::Axiom(Arc::new("a::b%c!d.".to_string())),
        ];
        let symbols: Vec<String> = tags.iter().map(|t| t.to_symbol()).collect();
        for s in symbols.iter() {
            assert!(!s.contains(':'), "{}", s);
            assert!(!s.contains('|'), "{}", s);
            assert!(!s.contains(char::is_whitespace), "{}", s);
        }
        // the reply cvc5 sends is read back with sise; each tag must be one atom
        let text = format!("({})", symbols.join(" "));
        let mut parser = sise::Parser::new(text.as_str());
        let node = sise::parse_tree(&mut parser).expect("sise parses the tag list");
        match node {
            sise::TreeNode::List(atoms) => {
                let got: Vec<String> = atoms
                    .into_iter()
                    .map(|a| match a {
                        sise::TreeNode::Atom(s) => s,
                        other => panic!("not an atom: {:?}", other),
                    })
                    .collect();
                assert_eq!(got, symbols);
            }
            other => panic!("not a list: {:?}", other),
        }
        assert_eq!(symbols[2], "ax_a__b%c!d.");
    }

    #[test]
    fn unknown_symbols_are_not_tags() {
        for s in ["?", "", "ax_", "hyp_x", "user_fixture__check_4", "%%location_label%%0"] {
            assert_eq!(ProvenanceTag::from_symbol(s), None, "{}", s);
        }
    }
}
