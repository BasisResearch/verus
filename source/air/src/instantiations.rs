//! Instantiation certificates: the `import-instantiations` command cvc5's
//! `export-instantiations` prints, and a later solver reads back.
//!
//! A certificate travels through a file another process wrote, so it is
//! parsed before it reaches a solver. Only a single import command for the
//! expected key, whose rows are all SMT-LIB string literals, is accepted.
//! cvc5 parses each row on its own as instantiation terms and skips one it
//! cannot read, so sending an accepted certificate can add saved instances
//! under its key and do nothing else. Any other text, such as an `assert`
//! or a truncated command, is rejected here and never sent.

use crate::printer::NodeWriter;
use sise::TreeNode as Node;

const IMPORT: &str = "import-instantiations";
const SKOLEMS: &str = ":skolems";

/// A validated `(import-instantiations k [:skolems (s*)] s*)` command with at
/// least one entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportInstantiations {
    key: String,
    /// The `:skolems` table, when the export named any skolems.
    skolems: Option<Vec<String>>,
    /// The instantiation rows, each an SMT-LIB string literal with its quotes.
    entries: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
enum Token<'a> {
    Open,
    Close,
    /// A simple symbol or keyword.
    Symbol(&'a str),
    /// A string literal, quotes included.
    Literal(&'a str),
}

/// SMT-LIB tokens of `text`, skipping whitespace and `;` comments, or `None`
/// at anything else: a quoted `|symbol|`, an unterminated string, or a
/// character no simple symbol contains.
fn tokenize(text: &str) -> Option<Vec<Token<'_>>> {
    let is_symbol_char = |c: char| c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/:".contains(c);
    let mut tokens = Vec::new();
    let mut rest = text;
    while let Some(c) = rest.chars().next() {
        if c.is_whitespace() {
            rest = &rest[c.len_utf8()..];
        } else if c == ';' {
            rest = rest.find('\n').map_or("", |end| &rest[end..]);
        } else if c == '(' || c == ')' {
            tokens.push(if c == '(' { Token::Open } else { Token::Close });
            rest = &rest[1..];
        } else if c == '"' {
            // A literal ends at a quote not followed by another: `""` is an
            // escaped quote inside it.
            let bytes = rest.as_bytes();
            let mut end = 1;
            loop {
                match bytes.get(end) {
                    None => return None,
                    Some(b'"') if bytes.get(end + 1) == Some(&b'"') => end += 2,
                    Some(b'"') => break,
                    Some(_) => end += 1,
                }
            }
            tokens.push(Token::Literal(&rest[..=end]));
            rest = &rest[end + 1..];
        } else if is_symbol_char(c) {
            let end = rest.find(|c: char| !is_symbol_char(c)).unwrap_or(rest.len());
            tokens.push(Token::Symbol(&rest[..end]));
            rest = &rest[end..];
        } else {
            return None;
        }
    }
    Some(tokens)
}

impl ImportInstantiations {
    /// Parse `text` as a certificate for `key`. `None` unless it is exactly one
    /// import command for `key` with at least one entry: a certificate that
    /// names no instance cannot close a query.
    pub fn parse(text: &str, key: &str) -> Option<Self> {
        let tokens = tokenize(text)?;
        let mut tokens = tokens.into_iter();
        let literals = |tokens: &mut std::vec::IntoIter<Token<'_>>| {
            let mut literals = Vec::new();
            loop {
                match tokens.next()? {
                    Token::Literal(literal) => literals.push(literal.to_owned()),
                    Token::Close => return Some(literals),
                    Token::Open | Token::Symbol(_) => return None,
                }
            }
        };
        if tokens.next()? != Token::Open
            || tokens.next()? != Token::Symbol(IMPORT)
            || tokens.next()? != Token::Symbol(key)
        {
            return None;
        }
        let mut skolems = None;
        let mut entries = Vec::new();
        loop {
            match tokens.next()? {
                Token::Symbol(SKOLEMS) if skolems.is_none() && entries.is_empty() => {
                    if tokens.next()? != Token::Open {
                        return None;
                    }
                    skolems = Some(literals(&mut tokens)?);
                }
                Token::Literal(literal) => entries.push(literal.to_owned()),
                Token::Close => break,
                Token::Open | Token::Symbol(_) => return None,
            }
        }
        if tokens.next().is_some() || entries.is_empty() {
            return None;
        }
        Some(ImportInstantiations { key: key.to_owned(), skolems, entries })
    }

    pub fn key(&self) -> &str {
        &self.key
    }

    pub(crate) fn to_node(&self) -> Node {
        let atom = |text: &str| Node::Atom(text.to_owned());
        let mut items = vec![atom(IMPORT), atom(&self.key)];
        if let Some(skolems) = &self.skolems {
            items.push(atom(SKOLEMS));
            items.push(Node::List(skolems.iter().map(|skolem| atom(skolem)).collect()));
        }
        items.extend(self.entries.iter().map(|entry| atom(entry)));
        Node::List(items)
    }

    /// The command as text, which `parse` reads back to an equal certificate.
    pub fn to_text(&self) -> String {
        NodeWriter::new().node_to_string_indent(&String::new(), &self.to_node())
    }
}

#[cfg(test)]
mod tests {
    use super::ImportInstantiations;

    const KEY: &str = "c0123456789abcdef";

    /// What cvc5 `basis-77ab13ff5b` printed for `(export-instantiations k)`
    /// after an unsat check, comment lines included.
    const EXPORT: &str = "; dropped 0\n(import-instantiations c0123456789abcdef\n\"((forall ((y Int)) (! (= (g y) (f y)) :pattern ((g y)))) (a))\"\n\"((forall ((x Int)) (! (>= (f x) 1) :pattern ((f x)))) (a))\")\n";

    #[test]
    fn accepts_an_export_and_round_trips() {
        let certificate = ImportInstantiations::parse(EXPORT, KEY).expect("an export parses");
        assert_eq!(certificate.key(), KEY);
        assert_eq!(certificate.entries.len(), 2);
        assert_eq!(ImportInstantiations::parse(&certificate.to_text(), KEY), Some(certificate));
    }

    #[test]
    fn accepts_skolems_and_escaped_quotes() {
        let text = format!("({} {KEY} :skolems (\"s\" \"t\") \"(a \"\"q\"\")\")", super::IMPORT);
        let certificate = ImportInstantiations::parse(&text, KEY).expect("parses");
        assert_eq!(certificate.skolems, Some(vec!["\"s\"".to_owned(), "\"t\"".to_owned()]));
        assert_eq!(certificate.entries, vec!["\"(a \"\"q\"\")\"".to_owned()]);
        assert_eq!(ImportInstantiations::parse(&certificate.to_text(), KEY), Some(certificate));
    }

    #[test]
    fn rejects_anything_but_one_import_for_the_key() {
        let rejected = [
            // Commands other than an import, alone or after one.
            "(assert false)".to_owned(),
            format!("(import-instantiations {KEY} \"(a)\")\n(assert false)"),
            format!("(assert false)\n(import-instantiations {KEY} \"(a)\")"),
            // Another key, or no entries.
            "(import-instantiations c1 \"(a)\")".to_owned(),
            format!("(import-instantiations {KEY})"),
            format!("(import-instantiations {KEY} :skolems (\"s\"))"),
            // Truncated or garbled.
            format!("(import-instantiations {KEY} \"(abc"),
            format!("(import-instantiations {KEY} \"(a)\""),
            "xyz".to_owned(),
            String::new(),
            // Rows that are not string literals.
            format!("(import-instantiations {KEY} (assert false))"),
            format!("(import-instantiations {KEY} a)"),
            format!("(import-instantiations {KEY} |a b|)"),
            format!("(import-instantiations {KEY} \"(a)\" :skolems (\"s\"))"),
        ];
        for text in rejected {
            assert_eq!(ImportInstantiations::parse(&text, KEY), None, "{text}");
        }
    }
}
