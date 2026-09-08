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
pub type SourceNames = HashMap<String, SourceName>;

#[derive(Clone, Debug)]
pub enum SourceName {
    Symbol(String),
    /// An infix operator, as the source writes it (`+`). Recorded where the
    /// encoder emits the symbol, from the same table `to_user_string` uses.
    Operator(String),
    /// Cast targets indexed by the emitted range arguments. A shared head
    /// such as `uClip` can represent several widths in the same query.
    Cast {
        symbol: String,
        types: HashMap<Vec<String>, String>,
    },
    Constructor {
        name: String,
        fields: Vec<String>,
        style: crate::ast::CtorPrintStyle,
    },
    Field(String),
}

impl SourceName {
    pub fn name(&self) -> &str {
        match self {
            Self::Symbol(name)
            | Self::Field(name)
            | Self::Operator(name)
            | Self::Constructor { name, .. } => name,
            Self::Cast { symbol, .. } => symbol,
        }
    }

    fn constructor(&self, args: &[String]) -> Option<String> {
        let Self::Constructor { name, fields, style } = self else { return None };
        if args.len() != fields.len() {
            return None;
        }
        use crate::ast::CtorPrintStyle;
        Some(match style {
            CtorPrintStyle::Const => name.clone(),
            CtorPrintStyle::Parens => format!("{}({})", name, args.join(", ")),
            CtorPrintStyle::Tuple => {
                let comma = if args.len() == 1 { "," } else { "" };
                format!("({}{comma})", args.join(", "))
            }
            CtorPrintStyle::Braces => {
                let fields: Vec<_> = fields
                    .iter()
                    .zip(args.iter())
                    .map(|(field, arg)| format!("{field}: {arg}"))
                    .collect();
                format!("{} {{ {} }}", name, fields.join(", "))
            }
        })
    }
}

/// Module and worker contexts may record different widths of the same clip.
/// Merge their range records instead of replacing an entire cast family.
pub(crate) fn merge_source_names(names: &mut SourceNames, other: SourceNames) {
    for (symbol, name) in other {
        match (names.get_mut(&symbol), name) {
            (Some(SourceName::Cast { types, .. }), SourceName::Cast { types: other, .. }) => {
                types.extend(other);
            }
            (_, name) => {
                names.insert(symbol, name);
            }
        }
    }
}

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
        if let Some(name) = names.get(rest) {
            return Some(name.name().to_string());
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
        Node::Atom(a) => names
            .get(a)
            .and_then(|n| n.constructor(&[]))
            .or_else(|| source_symbol(names, a))
            .unwrap_or_else(|| a.clone()),
        Node::List(items) => {
            // `(I x)` / `(Poly%D. x)` and their unboxes: show `x`
            if items.len() == 2 {
                if let Node::Atom(head) = &items[0] {
                    if is_box_head(head) {
                        return render_node(names, &items[1]);
                    }
                }
            }
            // SMT-LIB's binders are wire syntax rather than encoded names, so
            // they render structurally: `(let ((x e)) b)` reads `let x = e in b`.
            if let Some(Node::Atom(head)) = items.first() {
                if head == "let" && items.len() == 3 {
                    if let Node::List(bindings) = &items[1] {
                        let binds: Vec<String> = bindings
                            .iter()
                            .filter_map(|b| match b {
                                Node::List(pair) if pair.len() == 2 => Some(format!(
                                    "{} = {}",
                                    render_node(names, &pair[0]),
                                    render_node(names, &pair[1])
                                )),
                                _ => None,
                            })
                            .collect();
                        if !binds.is_empty() && binds.len() == bindings.len() {
                            return format!(
                                "let {} in {}",
                                binds.join(", "),
                                render_node(names, &items[2])
                            );
                        }
                    }
                }
            }
            // `(Add a b)` is `a + b`, and `(nClip x)` is `x as nat`, from
            // what the encoders recorded when they emitted those symbols.
            if let Some(Node::Atom(head)) = items.first() {
                match names.get(head) {
                    Some(SourceName::Operator(op)) if items.len() == 3 => {
                        return format!(
                            "({} {} {})",
                            render_node(names, &items[1]),
                            op,
                            render_node(names, &items[2])
                        );
                    }
                    // clips take the range arguments first, the value last
                    Some(SourceName::Cast { types, .. }) if items.len() > 1 => {
                        let range_args: Option<Vec<String>> = items[1..items.len() - 1]
                            .iter()
                            .map(|arg| match arg {
                                Node::Atom(atom) => Some(atom.clone()),
                                Node::List(_) => None,
                            })
                            .collect();
                        if let Some(ty) = range_args.as_ref().and_then(|args| types.get(args)) {
                            return format!(
                                "({} as {})",
                                render_node(names, items.last().unwrap()),
                                ty
                            );
                        }
                    }
                    _ => {}
                }
            }
            if let Some(Node::Atom(head)) = items.first() {
                match names.get(head) {
                    Some(SourceName::Field(field)) if items.len() > 1 => {
                        // Accessor encoders put type arguments before the receiver.
                        return format!("{}.{}", render_node(names, items.last().unwrap()), field);
                    }
                    Some(name @ SourceName::Constructor { fields, .. })
                        if items.len() == fields.len() + 1 =>
                    {
                        let args: Vec<String> =
                            items[1..].iter().map(|i| render_node(names, i)).collect();
                        if let Some(constructor) = name.constructor(&args) {
                            return constructor;
                        }
                    }
                    _ => {}
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
    use super::*;
    use crate::ast::{CrateId, CtorPrintStyle, Dt, PathX, VarIdent, VarIdentDisambiguate, Variant};
    use crate::def::NameCtxt;
    use std::sync::Arc;

    /// The renderer knows an AIR symbol is an operator only because the
    /// encoder recorded it as one when it emitted it; there is no table here
    /// restating that. `sst_to_air::record_op` does the recording in the
    /// pipeline, from `sst_util::binary_op_str`.
    #[test]
    fn arithmetic_preserves_grouping_through_boxes() {
        let mut names = SourceNames::new();
        for (symbol, op) in [
            (crate::def::ADD, "+"),
            (crate::def::SUB, "-"),
            (crate::def::MUL, "*"),
            (crate::def::EUC_DIV, "/"),
            (crate::def::EUC_MOD, "%"),
        ] {
            names.insert(symbol.to_string(), SourceName::Operator(op.to_string()));
        }
        let ctx = NameCtxt::new();
        record_cast(&ctx, crate::def::NAT_CLIP, crate::ast::IntRange::Nat, "nat");
        merge_source_names(&mut names, ctx.source_names());
        for (term, expected) in [
            ("((nClip (Add x y)))", "((x + y) as nat)"),
            ("((I (Mul (Add x y) z)))", "((x + y) * z)"),
            ("((I (Sub x (Sub y z))))", "(x - (y - z))"),
            ("((EucDiv x (Mul y z)))", "(x / (y * z))"),
            ("((EucMod (Add x y) z))", "((x + y) % z)"),
        ] {
            assert_eq!(render_vector(&names, term), expected);
        }
    }

    fn record_cast(ctx: &NameCtxt, symbol: &str, range: crate::ast::IntRange, typ: &str) {
        let application = crate::sst_to_air::apply_range_fun(
            symbol,
            &range,
            vec![air::ast_util::str_var("value")],
        );
        ctx.record_source_cast(&application, typ);
    }

    #[test]
    fn cast_targets_preserve_all_emitted_range_arguments() {
        use crate::ast::IntRange;
        use crate::def::{CHAR_CLIP, I_CLIP, NAT_CLIP, U_CLIP};
        let ctx = NameCtxt::new();
        for (symbol, range, typ) in [
            (U_CLIP, IntRange::U(8), "u8"),
            (U_CLIP, IntRange::U(16), "u16"),
            (U_CLIP, IntRange::U(64), "u64"),
            (U_CLIP, IntRange::USize, "usize"),
            (I_CLIP, IntRange::I(8), "i8"),
            (I_CLIP, IntRange::I(16), "i16"),
            (I_CLIP, IntRange::I(64), "i64"),
            (I_CLIP, IntRange::ISize, "isize"),
            (NAT_CLIP, IntRange::Nat, "nat"),
            (CHAR_CLIP, IntRange::Char, "char"),
        ] {
            record_cast(&ctx, symbol, range, typ);
        }
        for (term, expected) in [
            ("(uClip 8 value)", "(value as u8)"),
            ("(uClip 16 value)", "(value as u16)"),
            ("(uClip 64 value)", "(value as u64)"),
            ("(uClip SZ value)", "(value as usize)"),
            ("(iClip 8 value)", "(value as i8)"),
            ("(iClip 16 value)", "(value as i16)"),
            ("(iClip 64 value)", "(value as i64)"),
            ("(iClip SZ value)", "(value as isize)"),
            ("(nClip value)", "(value as nat)"),
            ("(charClip value)", "(value as char)"),
            ("(uClip 8 (iClip 16 value))", "((value as i16) as u8)"),
            // Do not discard range arguments or guess a target for unrecorded forms.
            ("(uClip 32 value)", "uClip(32, value)"),
            ("(uClip value)", "uClip(value)"),
            ("(uClip (+ 8 8) value)", "uClip(+(8, 8), value)"),
        ] {
            assert_eq!(render_term(&ctx.source_names(), term), expected);
        }
    }

    #[test]
    fn cast_ranges_survive_context_merges_in_either_order() {
        use crate::ast::IntRange;
        let first = NameCtxt::new();
        let second = NameCtxt::new();
        record_cast(&first, crate::def::U_CLIP, IntRange::U(8), "u8");
        record_cast(&second, crate::def::U_CLIP, IntRange::U(16), "u16");
        for (mut names, other) in [
            (first.source_names(), second.source_names()),
            (second.source_names(), first.source_names()),
        ] {
            merge_source_names(&mut names, other);
            assert_eq!(
                render_vector(&names, "((uClip 8 value) (uClip 16 value))"),
                "(value as u8), (value as u16)"
            );
        }
    }

    /// Bitwise operators are emitted through the same recording path as
    /// arithmetic, so they read as source writes them rather than as the
    /// prelude heads. The clip the encoder wraps the result in stays visible,
    /// because the source cast is real.
    #[test]
    fn bitwise_operators_read_as_source_writes_them() {
        let mut names = SourceNames::new();
        for (symbol, op) in [
            (crate::def::BIT_XOR, "^"),
            (crate::def::BIT_AND, "&"),
            (crate::def::BIT_OR, "|"),
            (crate::def::BIT_SHL, "<<"),
            (crate::def::BIT_SHR, ">>"),
        ] {
            names.insert(symbol.to_string(), SourceName::Operator(op.to_string()));
        }
        let ctx = NameCtxt::new();
        record_cast(&ctx, crate::def::U_CLIP, crate::ast::IntRange::U(8), "u8");
        merge_source_names(&mut names, ctx.source_names());
        for (term, expected) in [
            ("(bitxor x y)", "(x ^ y)"),
            ("(bitand x y)", "(x & y)"),
            ("(bitor x y)", "(x | y)"),
            ("(bitshl x y)", "(x << y)"),
            ("(bitshr x y)", "(x >> y)"),
            ("(uClip 8 (bitand x y))", "((x & y) as u8)"),
        ] {
            assert_eq!(render_term(&names, term), expected);
        }
    }

    /// Floats keep a separate encoder head per operation, so each renders as
    /// source writes it. A shared spelling would have collapsed add and divide
    /// into one, which is why the table gives them individually.
    #[test]
    fn float_operators_keep_one_spelling_each() {
        let mut names = SourceNames::new();
        for (symbol, op) in [
            (crate::def::IEEE_FLOAT_ADD, "+"),
            (crate::def::IEEE_FLOAT_SUB, "-"),
            (crate::def::IEEE_FLOAT_MUL, "*"),
            (crate::def::IEEE_FLOAT_DIV, "/"),
            (crate::def::IEEE_FLOAT_EQ, "=="),
            (crate::def::IEEE_FLOAT_LE, "<="),
            (crate::def::IEEE_FLOAT_LT, "<"),
        ] {
            names.insert(symbol.to_string(), SourceName::Operator(op.to_string()));
        }
        for (term, expected) in [
            ("(ieee_float_add x y)", "(x + y)"),
            ("(ieee_float_div x y)", "(x / y)"),
            ("(ieee_float_eq x y)", "(x == y)"),
            ("(ieee_float_le x y)", "(x <= y)"),
            ("(ieee_float_add (ieee_float_mul x y) z)", "((x * y) + z)"),
        ] {
            assert_eq!(render_term(&names, term), expected);
        }
    }

    /// `let` is SMT-LIB wire syntax, so it is rendered from its shape rather
    /// than looked up as an encoded name, and its bound body still is.
    #[test]
    fn let_binders_read_as_bindings() {
        let mut names = SourceNames::new();
        names.insert(crate::def::ADD.to_string(), SourceName::Operator("+".to_string()));
        assert_eq!(
            render_term(&names, "(let ((_let_1 5)) (Add _let_1 _let_1))"),
            "let _let_1 = 5 in (_let_1 + _let_1)"
        );
        assert_eq!(
            render_term(&names, "(let ((a 1) (b 2)) (Add a b))"),
            "let a = 1, b = 2 in (a + b)"
        );
    }

    #[test]
    fn variable_names_come_from_the_forward_encoder() {
        let ctx = NameCtxt::new();
        let param =
            ctx.var_ident(&VarIdent(Arc::new("amount".into()), VarIdentDisambiguate::VirParam));
        let shadow = ctx.var_ident(&VarIdent(
            Arc::new("amount".into()),
            VarIdentDisambiguate::VirRenumbered { is_stmt: true, does_shadow: true, id: 2 },
        ));
        let names = ctx.source_names();
        assert_eq!(render_vector(&names, &format!("((I {param}))")), "amount");
        assert_eq!(source_symbol(&names, &shadow).as_deref(), Some("amount (binding 2)"));
        assert_eq!(source_symbol(&names, "unrecorded!"), None);
    }

    fn constructor(ctx: &NameCtxt, name: &str, fields: &[&str], style: CtorPrintStyle) -> String {
        let path = Arc::new(PathX {
            krate: CrateId::Internal,
            segments: Arc::new(vec![Arc::new("Example".into())]),
        });
        let variant = Variant {
            name: Arc::new(name.into()),
            fields: Arc::new(
                fields
                    .iter()
                    .map(|field| {
                        air::ast_util::ident_binder(
                            &Arc::new(field.to_string()),
                            &(
                                Arc::new(crate::ast::TypX::Int(crate::ast::IntRange::Int)),
                                crate::ast::Mode::Spec,
                                crate::ast::Visibility { restricted_to: None },
                            ),
                        )
                    })
                    .collect(),
            ),
            ctor_style: style,
        };
        let dt = Dt::Path(path);
        let symbol = ctx.variant_ident(&dt, name);
        ctx.record_source_constructor(&symbol, &variant);
        // Subsequent uses must not replace the constructor's metadata with a plain name.
        assert_eq!(symbol, ctx.variant_ident(&dt, name));
        symbol.to_string()
    }

    #[test]
    fn constructors_use_the_declared_style_and_field_order() {
        let ctx = NameCtxt::new();
        let point = constructor(&ctx, "Point", &["y", "x"], CtorPrintStyle::Braces);
        let some = constructor(&ctx, "Some", &["0"], CtorPrintStyle::Parens);
        let none = constructor(&ctx, "None", &[], CtorPrintStyle::Const);
        let unit = constructor(&ctx, "Unit", &[], CtorPrintStyle::Tuple);
        let singleton = constructor(&ctx, "Singleton", &["0"], CtorPrintStyle::Tuple);
        let names = ctx.source_names();
        assert_eq!(render_term(&names, &format!("({point} (I 2) (I 1))")), "Point { y: 2, x: 1 }");
        assert_eq!(render_term(&names, &format!("({some} (I 5))")), "Some(5)");
        assert_eq!(render_term(&names, &none), "None");
        assert_eq!(render_term(&names, &unit), "()");
        assert_eq!(render_term(&names, &format!("({singleton} 5)")), "(5,)");
    }

    #[test]
    fn field_access_uses_the_recorded_receiver_and_field() {
        let ctx = NameCtxt::new();
        let path = Arc::new(PathX {
            krate: CrateId::Internal,
            segments: Arc::new(vec![Arc::new("Point".into())]),
        });
        let point =
            ctx.var_ident(&VarIdent(Arc::new("point".into()), VarIdentDisambiguate::VirParam));
        let variant = Arc::new("Point".into());
        let field = Arc::new("x".into());
        for internal in [true, false] {
            let symbol = ctx.variant_field_ident_internal(&path, &variant, &field, internal);
            assert_eq!(
                render_term(&ctx.source_names(), &format!("({symbol} $ INT {point})")),
                "point.x"
            );
        }
    }

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
