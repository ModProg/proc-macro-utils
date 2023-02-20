#[cfg(doc)]
use proc_macro2::Spacing;
use proc_macro2::{Group, Ident, Literal, Punct, TokenStream, TokenTree};
use smallvec::{smallvec, SmallVec};

use crate::{Delimited, TokenStream2Ext, TokenTree2Ext, TokenTreePunct};

// TODO move implementation in a trait implemented on both
// Peekable<token_stream::IntoIter>s
pub trait Peeker<I: Iterator<Item = TokenTree>> {
    const LENGTH: usize;
    fn peek(self, parser: &mut TokenParser<I>) -> bool;
}

impl<T: FnOnce(&TokenTree) -> bool, I: Iterator<Item = TokenTree>> Peeker<I> for T {
    const LENGTH: usize = 1;

    fn peek(self, parser: &mut TokenParser<I>) -> bool {
        parser.peek().map_or(false, self)
    }
}

macro_rules! impl_peeker {
    ($(($($T:ident $idx:tt),+$(,)?),$len:literal;)*) => {
        $(impl<$($T: FnOnce(&TokenTree) -> bool),+, I: Iterator<Item = TokenTree>> Peeker<I> for ($($T,)+) {
            const LENGTH: usize = $len;
            fn peek(self, parser: &mut TokenParser<I>) -> bool {
                $(parser.peek_n($idx).map_or(false, self.$idx))&&+
            }
        })*
    };
}

impl_peeker![
    (T1 0,),1;
    (T1 0, T2 1),2;
    (T1 0, T2 1, T3 2),3;
];

const MAX_PEEK_LEN: usize = 3;
/// Wrapper for [`TokenStream::into_iter`] allowing not only to iterate on
/// tokens but also to parse simple structures like types or expressions, though
/// it does not make any claims about their correctness.
///
/// ```
/// # use proc_macro2::TokenStream;
/// # use proc_macro_utils::{TokenParser, assert_tokens};
/// # use quote::quote;
/// let mut token_parser = TokenParser::from(quote! {a + b, c});
/// assert_tokens!(token_parser.next_expression().unwrap(), { a + b });
/// ```
#[allow(clippy::module_name_repetitions)]
pub struct TokenParser<T: Iterator<Item = TokenTree>> {
    peek: SmallVec<[TokenTree; MAX_PEEK_LEN]>,
    iter: T,
}

impl<I> TokenParser<I>
where
    I: Iterator<Item = TokenTree>,
{
    /// Creates a new [`TokenParser`] from a [`TokenTree`] iterator.
    pub fn new<T: IntoIterator<Item = TokenTree, IntoIter = I>>(value: T) -> Self {
        Self {
            peek: smallvec![],
            iter: value.into_iter(),
        }
    }
}

impl<T, I> From<T> for TokenParser<I>
where
    T: IntoIterator<Item = TokenTree, IntoIter = I>,
    I: Iterator<Item = TokenTree>,
{
    fn from(value: T) -> Self {
        Self {
            peek: smallvec![],
            iter: value.into_iter(),
        }
    }
}

impl<I: Iterator<Item = TokenTree>> From<TokenParser<I>> for TokenStream {
    fn from(value: TokenParser<I>) -> Self {
        value.iter.collect()
    }
}

impl<T: Iterator<Item = TokenTree>> Iterator for TokenParser<T> {
    type Item = TokenTree;

    fn next(&mut self) -> Option<Self::Item> {
        if self.peek.is_empty() {
            self.iter.next()
        } else {
            Some(self.peek.remove(0))
        }
    }
}

macro_rules! punct {
    ($($punct:literal, [$($tests:ident),*; $last:ident], $name:ident);*$(;)?) => {
        $(#[doc = concat!("Returns the next token if it is a `", $punct ,"`")]
        pub fn $name(&mut self) -> Option<TokenStream> {
            self.next_if_each(($(|t:&TokenTree|t.is_joint() && t.$tests(),)* |t:&TokenTree| t.is_alone() && t.$last()))
        })*
    };
    ([$test:ident $($tests:ident)*]) => {
        matches!(self.peek(), Some(token) if token.$test()) && punct!([$($tests)*])
    }
}

macro_rules! token_tree {
    ($($a:literal, $test:ident, $as:ident, $name:ident, $token:ident);*$(;)?) => {
        $(#[doc = concat!("Returns the next token if it is ", $a, " [`", stringify!($token) ,"`]")]
        pub fn $name(&mut self) -> Option<$token> {
            matches!(self.peek(), Some(token) if token.$test()).then(|| self.next().expect("token should be present").$as().expect(concat!("should be ", stringify!($token))))
        })*
    };
}

macro_rules! delimited {
    ($($test:ident, $name:ident, $doc:literal;)*) => {
        $(#[doc = concat!("Returns the next ", $doc ," group")]
        pub fn $name(&mut self) -> Option<TokenStream> {
            matches!(self.peek(), Some(token) if token.$test())
                .then(|| self.next_group().expect("should be group").stream())
        })*
    };
}

/// Some Iterator utilities
impl<T: Iterator<Item = TokenTree>> TokenParser<T> {
    /// Checks if there are remaining tokens
    pub fn is_empty(&mut self) -> bool {
        self.peek().is_none()
    }

    /// Peeks the next token without advancing the parser
    pub fn peek(&mut self) -> Option<&TokenTree> {
        if self.peek.is_empty() {
            self.peek.push(self.iter.next()?);
        }
        self.peek.first()
    }

    /// Peeks the next token without advancing the parser
    ///
    /// # Panics
    ///
    /// Will panic if `n >= 3`.
    pub fn peek_n(&mut self, n: usize) -> Option<&TokenTree> {
        assert!(
            (0..MAX_PEEK_LEN).contains(&n),
            "{n} over max peek index of {}",
            MAX_PEEK_LEN - 1
        );
        for _ in self.peek.len()..n {
            self.peek.push(self.iter.next()?);
        }
        self.peek.get(n)
    }

    /// Returns the next token if it fulfills the condition otherwise returns
    /// None and doesn't advance the parser
    pub fn next_if(&mut self, test: impl FnOnce(&TokenTree) -> bool) -> Option<TokenTree> {
        test(self.peek()?).then(|| self.next().expect("was peeked"))
    }

    /// Returns the next tokens (up to 3) if they fulfill the conditions
    /// otherwise returns None and doesn't advance the parser
    pub fn next_if_each<P: Peeker<T>>(&mut self, tests: P) -> Option<TokenStream> {
        tests.peek(self).then(|| {
            // Each peeker peeks at least as many elements as its LENGTH therfore they are
            // all in the peek
            self.peek.drain(0..P::LENGTH).collect()
        })
    }

    /// Returns all tokens while `test` evaluates to true.
    ///
    /// Returns `None` if empty or `test(first_token) == false`
    pub fn next_while(&mut self, mut test: impl FnMut(&TokenTree) -> bool) -> Option<TokenStream> {
        if self.peek().is_none() || !test(self.peek().expect("was peeked")) {
            None
        } else {
            let mut token_stream = TokenStream::new();
            token_stream.push(self.next().expect("was peeked"));
            while let Some(token) = self.next_if(&mut test) {
                token_stream.push(token);
            }
            Some(token_stream)
        }
    }

    /// Returns all tokens while `test` evaluates to false.
    ///
    /// Returns `None` if empty or `test(first_token) == true`.
    pub fn next_until(&mut self, mut test: impl FnMut(&TokenTree) -> bool) -> Option<TokenStream> {
        self.next_while(|token| !test(token))
    }
}

impl<T: Iterator<Item = TokenTree>> TokenParser<T> {
    /// Collects remaining tokens back into a [`TokenStream`]
    pub fn into_token_stream(self) -> TokenStream {
        self.into()
    }

    /// Returns the next group of punctuation with [`Punct::spacing`]
    /// [`Spacing::Joint`]
    pub fn next_punctuation_group(&mut self) -> Option<TokenStream> {
        let mut joined = true;
        dbg!(self.next_while(move |token| {
            let ret = joined && dbg!(token.is_punct());
            joined = token.is_joint();
            ret
        }))
    }

    /// "Parses" a type expression
    ///
    /// This just means it collects all the tokens that should belong to the
    /// type, until it reaches either:
    /// - a `;`
    /// - a `,` or `>` and all `<>` pairs are closed
    /// - the end of the token stream
    ///
    /// If the token stream is empty, or starts with `,`, `>` or `;` [`None`] is
    /// returned otherwise, [`Some(TokenStream)`](TokenStream) containing
    /// every token up to but excluding the terminator.
    ///
    /// ```
    /// # use proc_macro_utils::{TokenParser, assert_tokens};
    /// # use proc_macro2::TokenStream;
    /// # use quote::quote;
    ///
    /// let mut tokens = TokenParser::from(quote! {A<Test, B>, remainder});
    /// assert_tokens!(tokens.next_type().unwrap(), { A<Test, B> });
    /// assert!(tokens.next_type().is_none());
    /// assert_tokens!(tokens, { , remainder });
    /// ```
    pub fn next_type(&mut self) -> Option<TokenStream> {
        let Some(first) = self.peek() else { return None; };
        if first.is_comma() || first.is_semi() {
            return None;
        };

        let mut chevron_level: u32 = 0;

        self.next_while(|token| {
            if token.is_less_than() {
                chevron_level += 1;
            } else if token.is_greater_than() {
                if chevron_level == 0 {
                    return false;
                }
                chevron_level -= 1;
            }
            !(chevron_level == 0 && token.is_comma() || token.is_semi())
        })
    }

    /// "Parses" an expression
    ///
    /// This just means it collects all the tokens that should belong to the
    /// expression, until it reaches either:
    /// - a `;`
    /// - a `,` outside a type
    /// - the end of the token stream
    ///
    /// If the token stream is empty, or starts with `,` or `;` [`None`] is
    /// returned otherwise, [`Some(TokenStream)`](TokenStream) containing
    /// every token up to but excluding the terminator.
    ///
    /// ```
    /// # use proc_macro_utils::{TokenParser, assert_tokens};
    /// # use proc_macro2::TokenStream;
    /// # use quote::quote;
    ///
    /// let mut tokens = TokenParser::from(quote! {A + c ::<a, b>::a < b, next_token});
    /// assert_tokens!(tokens.next_expression().unwrap(), { A + c::<a, b>::a < b });
    /// assert!(tokens.next_expression().is_none());
    /// assert_tokens!(tokens, { , next_token });
    /// ```
    pub fn next_expression(&mut self) -> Option<TokenStream> {
        if self.peek().is_none()
            || matches!(self.peek(), Some(token) if token.is_comma() || token.is_semi())
        {
            return None;
        }

        let mut start = true;

        let mut tokens = TokenStream::new();

        // <a> * <a>
        // <a> => <a>
        'outer: while let Some(token) = self.peek() {
            if token.is_semi() || token.is_comma() {
                break;
            }
            if start && token.is_less_than() {
                tokens.push(self.next().expect("token was peeked"));
                loop {
                    if let Some(ty) = self.next_type() {
                        tokens.extend(ty.into_iter());
                    }
                    // next token can only be `,;>` or None
                    let Some(token) = self.peek() else { break 'outer }; // Invalid expression
                    if token.is_semi() {
                        break 'outer;
                    }
                    if token.is_greater_than() {
                        tokens.push(self.next().expect("token was peeked"));
                        break;
                    } else if token.is_comma() {
                        tokens.push(self.next().expect("token was peeked"));
                        continue; // Another type
                    };
                }
            }
            if let Some(token) = self.next() {
                // TODO this might be too simplistic
                start = token.is_punct();
                tokens.push(token);
            }
        }

        Some(tokens)
    }

    /// Returns the next string,
    pub fn next_string(&mut self) -> Option<String> {
        if !self.peek()?.is_literal() {
            return None;
        }
        let lit = self.peek()?.to_string();
        if lit.starts_with('"') {
            Some(resolve_escapes(&lit[1..lit.len() - 1]))
        } else if lit.starts_with('r') {
            let pounds = lit.chars().skip(1).take_while(|&c| c == '#').count();
            Some(lit[2 + pounds..lit.len() - pounds - 1].to_owned())
        } else {
            None
        }
    }
}
// Implemented following https://doc.rust-lang.org/reference/tokens.html#string-literals
#[allow(clippy::needless_continue)]
fn resolve_escapes(mut s: &str) -> String {
    let mut out = String::new();
    while !s.is_empty() {
        if s.starts_with('\\') {
            match s.as_bytes()[1] {
                b'x' => {
                    out.push(
                        char::from_u32(u32::from_str_radix(&s[2..=3], 16).expect("valid escape"))
                            .expect("valid escape"),
                    );
                    s = &s[4..];
                }
                b'u' => {
                    let len = s[3..].find('}').expect("valid escape");
                    out.push(
                        char::from_u32(u32::from_str_radix(&s[3..len], 16).expect("valid escape"))
                            .expect("valid escape"),
                    );
                    s = &s[3 + len..];
                }
                b'n' => {
                    out.push('\n');
                    s = &s[2..];
                }
                b'r' => {
                    out.push('\r');
                    s = &s[2..];
                }
                b't' => {
                    out.push('\t');
                    s = &s[2..];
                }
                b'\\' => {
                    out.push('\\');
                    s = &s[2..];
                }
                b'0' => {
                    out.push('\0');
                    s = &s[2..];
                }
                b'\'' => {
                    out.push('\'');
                    s = &s[2..];
                }
                b'"' => {
                    out.push('"');
                    s = &s[2..];
                }
                b'\n' => {
                    s = &s[..s[2..]
                        .find(|c: char| !c.is_ascii_whitespace())
                        .unwrap_or(s.len())];
                }
                c => unreachable!(
                    "TokenStream string literals should only contain valid escapes, found `\\{c}`"
                ),
            }
        } else {
            let len = s.find('\\').unwrap_or(s.len());
            out.push_str(&s[..len]);
            s = &s[len..];
        }
    }
    out
}

impl<T: Iterator<Item = TokenTree>> TokenParser<T> {
    token_tree!(
        "a", is_group, into_group, next_group, Group;
        "an", is_ident, into_ident, next_ident, Ident;
        "a", is_punct, into_punct, next_punct, Punct;
        "a", is_literal, into_literal, next_literal, Literal;
    );

    delimited!(
        is_parenthesized, next_parenthesized, "parenthesized";
        is_braced, next_braced, "braced";
        is_bracketed, next_bracketed, "bracketed";
    );
}
/// For now the naming of the tokens follow the names used in the
/// [rust reference](https://doc.rust-lang.org/reference/tokens.html#punctuation)
/// even though they diverge from the names used at [`TokenTreePunct`].
///
/// Note that they only match the token with correct [spacing](Spacing), i.e.
/// [`next_plus`](Self::next_plus) will match `+ =` and `+a` but not `+=`.
// TODO figure out what the single token ones should return, TokenStream or
// TokenTree
impl<T: Iterator<Item = TokenTree>> TokenParser<T> {
    punct!(
        "+", [; is_plus], next_plus;
        "-", [; is_minus], next_minus;
        "*", [; is_asterix], next_star;
        "/", [; is_slash], next_slash;
        "%", [; is_percent], next_percent;
        "^", [; is_caret], next_caret;
        "!", [; is_exclamation], next_not;
        "&", [; is_and], next_and;
        "|", [; is_pipe], next_or;
        "&&", [is_and; is_and], next_and_and;
        "||", [is_pipe; is_pipe], next_or_or;
        "<<", [is_less_than; is_less_than], next_shl;
        ">>", [is_greater_than; is_greater_than], next_shr;
        "+=", [is_plus; is_equals], next_plus_eq;
        "-=", [is_minus; is_equals], next_minus_eq;
        "*=", [is_asterix; is_equals], next_star_eq;
        "/=", [is_slash; is_equals], next_slash_eq;
        "%=", [is_percent; is_equals], next_percent_eq;
        "^=", [is_caret; is_equals], next_caret_eq;
        "&=", [is_and; is_equals], next_and_eq;
        "|=", [is_pipe; is_equals], next_or_eq;
        "<<=", [is_less_than, is_less_than; is_equals], next_shl_eq;
        ">>=", [is_greater_than, is_greater_than; is_equals], next_shr_eq;
        "=", [; is_equals], next_eq;
        "==", [is_equals; is_equals], next_eq_eq;
        "!=", [is_equals; is_equals], next_ne;
        ">", [; is_greater_than], next_gt;
        "<", [; is_less_than], next_lt;
        ">=", [is_greater_than; is_equals], next_ge;
        "<=", [is_less_than; is_equals], next_le;
        "@", [; is_at], next_at;
        ".", [; is_dot], next_dot;
        "..", [is_dot; is_dot], next_dot_dot;
        "...", [is_dot, is_dot; is_dot], next_dot_dot_dot;
        "..=", [is_dot, is_dot; is_equals], next_dot_dot_eq;
        ",", [; is_comma], next_comma;
        ";", [; is_semi], next_semi;
        ":", [; is_colon], next_colon;
        "::", [is_colon; is_colon], next_path_sep;
        "->", [is_minus; is_greater_than], next_r_arrow;
        "=>", [is_minus; is_greater_than], next_fat_arrow;
        "#", [; is_pound], next_pound;
        "$", [; is_dollar], next_dollar;
        "?", [; is_question], next_question;
        "~", [; is_tilde], next_tilde;
    );
}

#[cfg(test)]
mod test {
    use quote::quote;

    use super::*;
    use crate::assert_tokens;

    #[test]
    fn ty() {
        let mut at = TokenParser::from(quote! {Name, <Some, Generic, Type>});
        assert_tokens!(at.next_type().unwrap(), { Name });
        at.next();
        assert_tokens!(
            at.next_type().unwrap(),
            { < Some , Generic , Type > }
        );
    }

    #[test]
    fn expr() {
        let mut at = TokenParser::from(
            quote! {a + b, <Some, Generic, Type>::something + <a,b> * a < b, "hi"},
        );
        assert_tokens!(at.next_expression().unwrap(), { a + b });
        at.next();
        assert_tokens!(
            at.next_expression().unwrap(), { <Some, Generic, Type>::something + <a,b> * a < b }
        );
        at.next();
        assert_tokens!(at.next_expression().unwrap(), { "hi" });
    }
}
