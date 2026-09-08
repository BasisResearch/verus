//! Showing AIR symbols and terms as the source that produced them.
//!
//! Verus mangles source names on the way to AIR: a path becomes
//! `krate!seg.seg.`, a value is boxed as `(I x)`, a function gains a `%`
//! prefix and a `?` suffix. A reader of solver output — the provenance
//! report, and anything downstream of it — must show the source spelling
//! instead, or it leaks an encoding its audience never chose.
//!
//! It does not do that by inverting the mangling. The mangling is **not
//! injective**: `krate_to_string` maps `\`, `{` and `}` all onto
//! `PREFIX_ESCAPE`, so several distinct crate names share one encoding and
//! no inverse exists. Even where an inverse would exist, writing one is a
//! second copy of the encoding that silently drifts from the first.
//!
//! Instead the encoders record what they encoded, as they encode it
//! (`NameCtxt::record_source_name`), and this module looks the answer up.
//! The only structure it needs is the set of prefixes and box heads the
//! encoders use, which is enumerated in [`crate::def::AIR_SYMBOL_PREFIXES`]
//! and [`crate::def::AIR_BOX_HEADS`] and held exhaustive by a test.

use crate::def::{AIR_BOX_HEADS, AIR_GLOBAL_SUFFIX, AIR_SYMBOL_PREFIXES};
use sise::TreeNode as Node;
use std::collections::HashMap;

/// AIR symbol -> the source name it was encoded from, as the encoders
/// recorded it (`NameCtxt::record_source_name`, collected per crate into
/// `GlobalCtx::air_source_names`).
pub type SourceNames = HashMap<String, String>;

/// The source name behind one AIR symbol: the recorded name of the longest
/// suffix of `symbol` left after stripping the encoders' prefixes and the
/// global `?`. `None` when nothing recorded it (a prelude symbol such as
/// `Add`, or a name minted by another context).
pub fn source_symbol(names: &SourceNames, symbol: &str) -> Option<String> {
    let mut rest = symbol.strip_suffix(AIR_GLOBAL_SUFFIX).unwrap_or(symbol);
    // strip encoder prefixes, longest first: the set is not prefix-free
    // (`proj%` is a prefix of `proj%%`, `tmp%` of `tmp%%`), so a shortest-
    // first walk would stop inside a longer prefix and look up a stem that
    // was never recorded.
    loop {
        if let Some(name) = names.get(rest).cloned() {
            return Some(name);
        }
        let mut prefixes: Vec<&&str> = AIR_SYMBOL_PREFIXES.iter().collect();
        prefixes.sort_by_key(|p| std::cmp::Reverse(p.len()));
        match prefixes.into_iter().find(|p| rest.starts_with(**p) && rest.len() > p.len()) {
            Some(p) => rest = &rest[p.len()..],
            None => return None,
        }
    }
}

/// Whether an application head is a box or unbox, which a source rendering
/// drops: the value inside is what the user wrote.
fn is_box_head(head: &str) -> bool {
    AIR_BOX_HEADS.contains(&head)
        || head.starts_with(crate::def::PREFIX_BOX)
        || head.starts_with(crate::def::PREFIX_UNBOX)
}

fn render_node(names: &SourceNames, node: &Node) -> String {
    match node {
        Node::Atom(a) => source_symbol(names, a).unwrap_or_else(|| a.clone()),
        Node::List(items) => {
            // `(I x)` / `(Poly%D. x)` and their unboxes: show `x`
            if items.len() == 2 {
                if let Node::Atom(head) = &items[0] {
                    if is_box_head(head) {
                        return render_node(names, &items[1]);
                    }
                }
            }
            // `(Add a b)` is `a + b` to the reader
            if items.len() == 3 {
                if let Node::Atom(head) = &items[0] {
                    if let Some(op) = infix_operator(head) {
                        return format!(
                            "{} {} {}",
                            render_node(names, &items[1]),
                            op,
                            render_node(names, &items[2])
                        );
                    }
                }
            }
            let parts: Vec<String> = items.iter().map(|i| render_node(names, i)).collect();
            match parts.split_first() {
                // an application prints as the source would write it
                Some((head, args)) if !args.is_empty() => {
                    format!("{}({})", head, args.join(", "))
                }
                Some((only, _)) => only.clone(),
                None => String::new(),
            }
        }
    }
}

/// The prelude's arithmetic symbols and how the source writes them. These
/// are not encoded from a source name, so nothing records them; they are
/// named constants in [`crate::def`] and mapped here by those constants.
fn infix_operator(head: &str) -> Option<&'static str> {
    Some(match head {
        h if h == crate::def::ADD => "+",
        h if h == crate::def::SUB => "-",
        h if h == crate::def::MUL => "*",
        h if h == crate::def::EUC_DIV => "/",
        h if h == crate::def::EUC_MOD => "%",
        _ => return None,
    })
}

/// One SMT term, rendered in source spelling: boxes dropped, mangled
/// symbols replaced by what they were encoded from, applications written
/// `f(a, b)`. Falls back to the term as given when it does not parse.
pub fn render_term(names: &SourceNames, term: &str) -> String {
    let mut parser = sise::Parser::new(term);
    match sise::parse_tree(&mut parser) {
        Ok(node) => render_node(names, &node),
        Err(_) => term.to_string(),
    }
}

/// One instantiation vector (`(t1 t2)`) as a comma-separated source list.
pub fn render_vector(names: &SourceNames, vector: &str) -> String {
    let mut parser = sise::Parser::new(vector);
    match sise::parse_tree(&mut parser) {
        Ok(Node::List(items)) => {
            items.iter().map(|i| render_node(names, i)).collect::<Vec<_>>().join(", ")
        }
        Ok(node) => render_node(names, &node),
        Err(_) => vector.to_string(),
    }
}

#[cfg(test)]
mod tests {
    /// Every `PREFIX_` constant the encoders define must be listed in
    /// `AIR_SYMBOL_PREFIXES`, or a symbol carrying it is looked up with the
    /// prefix still attached and silently renders as the raw AIR name. The
    /// check reads the constants out of the source itself, so adding one
    /// without listing it fails here rather than in a user's report.
    #[test]
    fn every_prefix_is_listed() {
        let src = include_str!("def.rs");
        let mut missing = Vec::new();
        for line in src.lines() {
            let line = line.trim();
            let Some(rest) = line.split("const ").nth(1) else { continue };
            let Some((name, value)) = rest.split_once(": &str = ") else { continue };
            if !name.starts_with("PREFIX_") {
                continue;
            }
            let value = value.trim_end_matches(';');
            let Some(value) = value.strip_prefix('"').and_then(|v| v.strip_suffix('"')) else {
                continue; // an alias to another constant, not a literal prefix
            };
            if !crate::def::AIR_SYMBOL_PREFIXES.contains(&value) {
                missing.push(format!("{name} = {value:?}"));
            }
        }
        assert!(
            missing.is_empty(),
            "these encoder prefixes are not in def::AIR_SYMBOL_PREFIXES, so symbols carrying \
             them cannot be rendered in source spelling: {missing:?}"
        );
    }
}
