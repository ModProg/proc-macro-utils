#[cfg(doc)]
use proc_macro2::Spacing;
use proc_macro2::{token_stream, Group, Ident, Literal, Punct, TokenStream, TokenTree};
use smallvec::{smallvec, SmallVec};

use crate::{Delimited, TokenStream2Ext, TokenTree2Ext, TokenTreePunct};

// TODO move implementation in a trait implemented on both
// Peekable<token_stream::IntoIter>s
/// Trait that allows to peek a constant number of tokens.
pub trait Peeker {
    /// Number of tokens this peeker checks.
    const LENGTH: usize;

    /// Test if the tokens match.
    ///
    /// # Panics
    ///
    /// Implementations can panic if `tokens.len() < Self::LENGTH`.
    #[must_use]
    fn peek(self, tokens: &[TokenTree]) -> bool;
}

impl<T: FnOnce(&TokenTree) -> bool> Peeker for T {
    const LENGTH: usize = 1;

    #[must_use]
    fn peek(self, parser: &[TokenTree]) -> bool {
        self(&parser[0])
    }
}

macro_rules! impl_peeker {
    ($(($($T:ident $idx:tt),+$(,)?),$len:literal;)*) => {
        $(
            impl<$($T: FnOnce(&TokenTree) -> bool),+> Peeker for ($($T,)+) {
                const LENGTH: usize = $len;
                fn peek(self, parser: &[TokenTree]) -> bool {
                    $(self.$idx(&parser[$idx]))&&+
                }
            }
        )*
    };
}

impl_peeker![
    (T1 0,), 1;
    (T1 0, T2 1), 2;
    (T1 0, T2 1, T3 2), 3;
];

/// Wrapper for [`TokenStream::into_iter`] allowing not only to iterate on
/// tokens but also to parse simple structures like types or expressions, though
/// it does not make any claims about their correctness.
///
/// ```
/// # use proc_macro2::TokenStream;
/// # use proc_macro_utils::{TokenParser, assert_tokens};
/// # use quote::quote;
/// let mut token_parser = TokenParser::new(quote! {a + b, c});
/// assert_tokens!(token_parser.next_expression().unwrap(), { a + b });
/// ```
///
/// # Construction
///
/// In most cases use [`new()`](TokenParser::new) to avoid specifying the
/// generics. To change the on-stack size of the peek-buffer use
/// [`new_generic()`](TokenParser::new_generic) or
/// [`From::from`](#impl-From<T>-for-TokenParser<I,+PEEKER_LEN>).
///
/// # Peeking
///
/// The `TokenParser` allows peeking an arbitrary amount of tokens using
/// [`peek_n()`](Self::peek_n) and the token specific variants. This uses a
/// [`SmallVec`] with its capacity specified via `PEEKER_LEN` (default is 6).
/// This means peeking up to `6` tokens ahead happens without heap allocation.
/// Token groups can need up to `3` tokens of additional space e.g.
/// [`peek_n_dot_dot_eq()`](Self::peek_n_dot_dot_eq) can, with the default
/// allocation free be called with up to `3`, and
/// [`peek_n_plus_eq()`](Self::peek_n_plus_eq) up to `4`.
///
/// **Warning**: Setting `PEEKER_LEN = 0` means even
/// [`is_empty()`](Self::is_empty) and [`peek()`](Self::peek) allocate, and a
/// value below `3` will make some of the
/// [`peek_{punctuation}`](#impl-TokenParser<I,+PEEKER_LEN>-3) allocate
/// additionally.
#[allow(clippy::module_name_repetitions)]
#[derive(Clone)]
#[must_use]
pub struct TokenParser<
    I: Iterator<Item = TokenTree> = token_stream::IntoIter,
    const PEEKER_LEN: usize = 6,
> {
    peek: SmallVec<[TokenTree; PEEKER_LEN]>,
    iter: I,
}

impl TokenParser {
    /// Creates a new [`TokenParser`] from a [`TokenTree`] iterator.
    ///
    /// This sets the default length for the peeker buffer. Use
    /// [`new_generic()`](Self::new_generic) to change it.
    pub fn new<T, I>(value: T) -> TokenParser<I, 6>
    where
        T: IntoIterator<Item = TokenTree, IntoIter = I>,
        I: Iterator<Item = TokenTree>,
    {
        TokenParser::new_generic(value)
    }

    /// Creates a new [`TokenParser`] from a [`TokenTree`] iterator, allowing
    /// to specify the size of the peeker buffer.
    ///
    /// See [Peeking](#Peeking) for implications.
    pub fn new_generic<const PEEKER_LEN: usize, T, I>(value: T) -> TokenParser<I, PEEKER_LEN>
    where
        T: IntoIterator<Item = TokenTree, IntoIter = I>,
        I: Iterator<Item = TokenTree>,
    {
        TokenParser {
            peek: smallvec![],
            iter: value.into_iter(),
        }
    }
}

impl<T, I, const PEEKER_LEN: usize> From<T> for TokenParser<I, PEEKER_LEN>
where
    T: IntoIterator<Item = TokenTree, IntoIter = I>,
    I: Iterator<Item = TokenTree>,
{
    fn from(value: T) -> Self {
        TokenParser::new_generic(value)
    }
}

impl<I, const PEEKER_LEN: usize> From<TokenParser<I, PEEKER_LEN>> for TokenStream
where
    I: Iterator<Item = TokenTree>,
{
    #[must_use]
    fn from(value: TokenParser<I, PEEKER_LEN>) -> Self {
        value.iter.collect()
    }
}

impl<I, const PEEKER_LEN: usize> Iterator for TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    type Item = TokenTree;

    #[must_use]
    fn next(&mut self) -> Option<Self::Item> {
        if self.peek.is_empty() {
            self.iter.next()
        } else {
            Some(self.peek.remove(0))
        }
    }
}

#[cfg(feature = "quote")]
impl<I, const PEEKER_LEN: usize> quote::ToTokens for TokenParser<I, PEEKER_LEN>
where
    I: Clone + Iterator<Item = TokenTree>,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(self.clone());
    }

    #[must_use]
    fn to_token_stream(&self) -> TokenStream {
        self.clone().collect()
    }

    #[must_use]
    fn into_token_stream(self) -> TokenStream
    where
        Self: Sized,
    {
        self.collect()
    }
}

macro_rules! punct {
    ($($punct:literal, [$($tests:ident),*; $last:ident], $peek:ident, $peek_n:ident, $name:ident);*$(;)?) => {
        $(#[doc = concat!("Returns the next token if it is a `", $punct ,"`")]
        #[must_use]
        pub fn $name(&mut self) -> Option<TokenStream> {
            self.next_if_each(($(|t:&TokenTree|t.is_joint() && t.$tests(),)* |t:&TokenTree| t.is_alone() && t.$last()))
        })*
        $(#[doc = concat!("Returns the next token if it is a `", $punct ,"` without advancing the parser")]
        #[must_use]
        pub fn $peek(&mut self) -> Option<TokenStream> {
            self.$peek_n(0)
        })*
        $(#[doc = concat!("Returns the `n`th token if it is a `", $punct ,"` without advancing the parser")]
        #[must_use]
        pub fn $peek_n(&mut self, n:usize) -> Option<TokenStream> {
            self.peek_n_if_each(n, ($(|t:&TokenTree|t.is_joint() && t.$tests(),)* |t:&TokenTree| t.is_alone() && t.$last()))
        })*
    };
    ([$test:ident $($tests:ident)*]) => {
        matches!(self.peek(), Some(token) if token.$test()) && punct!([$($tests)*])
    }
}

macro_rules! token_tree {
    ($($a:literal, $test:ident, $peek_as:ident, $as:ident, $peek:ident, $peek_n:ident, $name:ident, $token:ident);*$(;)?) => {
        $(#[doc = concat!("Returns the next token if it is ", $a, " [`", stringify!($token) ,"`].")]
        #[must_use]
        pub fn $name(&mut self) -> Option<$token> {
            self.$peek().is_some().then(|| self.next().expect("token should be present").$as().expect(concat!("should be ", stringify!($token))))
        })*

        $(#[doc = concat!("Returns the next token if it is ", $a, " [`", stringify!($token) ,"`] without advancing the parser.")]
        #[must_use]
        pub fn $peek(&mut self) -> Option<&$token> {
            self.$peek_n(0)
        })*

        $(#[doc = concat!("Returns the `n`th token if it is ", $a, " [`", stringify!($token) ,"`] without advancing the parser.")]
        #[must_use]
        pub fn $peek_n(&mut self, n: usize) -> Option<&$token> {
            self.peek_n(n).and_then(TokenTree::$peek_as)
        })*
    };
}

macro_rules! delimited {
    ($($test:ident, $peek:ident, $peek_n:ident, $name:ident, $doc:literal;)*) => {
        $(#[doc = concat!("Returns the next token if it is a ", $doc ," group.")]
        #[must_use]
        pub fn $name(&mut self) -> Option<TokenStream> {
            self.$peek().map(|stream| {
                self.next().unwrap();
                stream
            })
        })*
        $(#[doc = concat!("Returns the next token if it is a", $doc ," group, without advancing the parser.")]
        #[must_use]
        pub fn $peek(&mut self) -> Option<TokenStream> {
            self.$peek_n(0)
        })*
        $(#[doc = concat!("Returns the `n`th token if it is a ", $doc ," group, without advancing the parser.")]
        #[must_use]
        pub fn $peek_n(&mut self, n: usize) -> Option<TokenStream> {
            self.peek_n(n).and_then(|token|
                token.$test().then(|| token.group().unwrap().stream()))
        })*
    };
}

/// Some Iterator utilities
impl<I, const PEEKER_LEN: usize> TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    /// Checks if there are remaining tokens
    #[must_use]
    pub fn is_empty(&mut self) -> bool {
        self.peek().is_none()
    }

    /// Peeks the next token without advancing the parser
    #[must_use]
    pub fn peek(&mut self) -> Option<&TokenTree> {
        if self.peek.is_empty() {
            self.peek.push(self.iter.next()?);
        }
        self.peek.first()
    }

    /// Peeks the `n`th token without advancing the parser
    #[must_use]
    pub fn peek_n(&mut self, n: usize) -> Option<&TokenTree> {
        for _ in self.peek.len()..=n {
            self.peek.push(self.iter.next()?);
        }
        self.peek.get(n)
    }

    /// Returns the next token if it fulfills the condition otherwise returns
    /// None and doesn't advance the parser
    #[must_use]
    pub fn next_if(&mut self, test: impl FnOnce(&TokenTree) -> bool) -> Option<TokenTree> {
        test(self.peek()?).then(|| self.next().expect("was peeked"))
    }

    /// Returns the next tokens if they fulfill the conditions
    /// otherwise returns None and doesn't advance the parser
    #[must_use]
    pub fn next_if_each<P: Peeker>(&mut self, tests: P) -> Option<TokenStream> {
        // Ensure peek is filled;
        if PEEKER_LEN > 0 {
            self.peek_n(P::LENGTH - 1)?;
        }
        tests
            .peek(&self.peek[..P::LENGTH])
            .then(|| self.peek.drain(0..P::LENGTH).collect())
    }

    /// Returns the next tokens if they fulfill the conditions
    /// otherwise returns None, without advancing the parser
    #[must_use]
    pub fn peek_if_each<P: Peeker>(&mut self, tests: P) -> Option<TokenStream> {
        // Ensure peek is filled;
        self.peek_n_if_each(0, tests)
    }

    /// Returns the next tokens from `n` if they fulfill the
    /// conditions otherwise returns None, without advancing the parser
    #[must_use]
    pub fn peek_n_if_each<P: Peeker>(&mut self, n: usize, tests: P) -> Option<TokenStream> {
        // Ensure peek is filled;
        if PEEKER_LEN > 0 {
            self.peek_n(P::LENGTH + n - 1)?;
        }
        let peeked = &self.peek[n..P::LENGTH + n];
        tests.peek(peeked).then(|| peeked.iter().cloned().collect())
    }

    /// Returns all tokens while `test` evaluates to true.
    ///
    /// Returns `None` if empty or `test(first_token) == false`
    #[must_use]
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
    #[must_use]
    pub fn next_until(&mut self, mut test: impl FnMut(&TokenTree) -> bool) -> Option<TokenStream> {
        self.next_while(|token| !test(token))
    }
}

impl<I, const PEEKER_LEN: usize> TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    /// Collects remaining tokens back into a [`TokenStream`]
    #[must_use]
    pub fn into_token_stream(self) -> TokenStream {
        self.into()
    }

    /// Returns the next group of punctuation with [`Punct::spacing`]
    /// [`Spacing::Joint`]
    #[must_use]
    pub fn next_punctuation_group(&mut self) -> Option<TokenStream> {
        let mut joined = true;
        self.next_while(move |token| {
            let ret = joined && token.is_punct();
            joined = token.is_joint();
            ret
        })
    }

    /// Returns the next ident if it matches the specified keyword without
    /// advancing the parser.
    ///
    /// While this is called `peek_keyword` it is not restricted to rust
    /// keywords, it can be used with any ident.
    /// ```
    /// # use proc_macro_utils::TokenParser;
    /// # use quote::quote;
    /// let mut parser = TokenParser::new(quote!( in out ));
    /// assert_eq!(parser.peek_keyword("in").unwrap().to_string(), "in");
    /// assert_eq!(parser.peek_keyword("in").unwrap().to_string(), "in");
    /// assert!(parser.peek_keyword("out").is_none());
    /// parser.next().unwrap();
    /// assert_eq!(parser.peek_keyword("out").unwrap().to_string(), "out");
    /// ```
    #[must_use]
    pub fn peek_keyword<K: ?Sized>(&mut self, keyword: &K) -> Option<&Ident>
    where
        Ident: PartialEq<K>,
    {
        self.peek_n_keyword(0, keyword)
    }

    /// Returns the nth token if it matches the specified keyword without
    /// advancing the parser.
    ///
    /// While this is called `peek_n_keyword` it is not restricted to rust
    /// keywords, it can be used with any ident.
    /// ```
    /// # use proc_macro_utils::TokenParser;
    /// # use quote::quote;
    /// let mut parser = TokenParser::new(quote!( in out ));
    /// assert_eq!(parser.peek_keyword("in").unwrap().to_string(), "in");
    /// assert_eq!(parser.peek_n_keyword(1, "out").unwrap().to_string(), "out");
    /// assert!(parser.peek_keyword("out").is_none());
    /// ```
    #[must_use]
    pub fn peek_n_keyword<K: ?Sized>(&mut self, n: usize, keyword: &K) -> Option<&Ident>
    where
        Ident: PartialEq<K>,
    {
        self.peek_n_ident(n).filter(|&ident| ident == keyword)
    }

    /// Returns the next ident if it matches the specified keyword.
    ///
    /// While this is called `next_keyword` it is not restricted to rust
    /// keywords, it can be used with any ident.
    /// ```
    /// # use proc_macro_utils::TokenParser;
    /// # use quote::quote;
    /// let mut parser = TokenParser::new(quote!( in out ));
    /// assert_eq!(parser.next_keyword("in").unwrap().to_string(), "in");
    /// assert!(parser.next_keyword("in").is_none());
    /// assert_eq!(parser.next_keyword("out").unwrap().to_string(), "out");
    /// assert!(parser.next_keyword("anything").is_none());
    /// ```
    #[must_use]
    pub fn next_keyword<K: ?Sized>(&mut self, keyword: &K) -> Option<Ident>
    where
        Ident: PartialEq<K>,
    {
        self.next_if(|token| matches!(token.ident(), Some(ident) if ident == keyword))
            .map(|token| token.into_ident().expect("is ident"))
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
    /// let mut tokens = TokenParser::new(quote! {A<Test, B>, remainder});
    /// assert_tokens!(tokens.next_type().unwrap(), { A<Test, B> });
    /// assert!(tokens.next_type().is_none());
    /// assert_tokens!(tokens, { , remainder });
    /// ```
    #[must_use]
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
    /// let mut tokens = TokenParser::new(quote! {A + c ::<a, b>::a < b, next_token});
    /// assert_tokens!(tokens.next_expression().unwrap(), { A + c::<a, b>::a < b });
    /// assert!(tokens.next_expression().is_none());
    /// assert_tokens!(tokens, { , next_token });
    /// ```
    #[must_use]
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

    /// Returns the next string literal
    #[must_use]
    pub fn next_string(&mut self) -> Option<String> {
        if !self.peek()?.is_literal() {
            return None;
        }
        let lit = self.peek()?.to_string();
        if lit.starts_with('"') {
            self.next();
            Some(resolve_escapes(&lit[1..lit.len() - 1]))
        } else if lit.starts_with('r') {
            self.next();
            let pounds = lit.chars().skip(1).take_while(|&c| c == '#').count();
            Some(lit[2 + pounds..lit.len() - pounds - 1].to_owned())
        } else {
            None
        }
    }

    /// Returns the next boolean literal
    #[must_use]
    pub fn next_bool(&mut self) -> Option<bool> {
        self.next_if(|t| {
            t.ident()
                .map_or(false, |ident| ident == "true" || ident == "false")
        })
        .map(|t| matches!(t.ident(), Some(ident) if ident == "true"))
    }
}
// Implemented following https://doc.rust-lang.org/reference/tokens.html#string-literals
// #[allow(clippy::needless_continue)]
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

impl<I, const PEEKER_LEN: usize> TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    token_tree!(
        "a", is_group, group, into_group, peek_group, peek_n_group, next_group, Group;
        "an", is_ident, ident, into_ident, peek_ident, peek_n_ident, next_ident, Ident;
        "a", is_punct, punct, into_punct, peek_punct, peek_n_punct, next_punct, Punct;
        "a", is_literal, literal, into_literal, peek_literal, peek_n_literal, next_literal, Literal;
    );

    delimited!(
        is_parenthesized, peek_parenthesized, peek_n_parenthesized, next_parenthesized, "parenthesized";
        is_braced, peek_braced, peek_n_braced, next_braced, "braced";
        is_bracketed, peek_bracketed, peek_n_bracketed, next_bracketed, "bracketed";
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
impl<I, const PEEKER_LEN: usize> TokenParser<I, PEEKER_LEN>
where
    I: Iterator<Item = TokenTree>,
{
    punct!(
        "+", [; is_plus], peek_plus, peek_n_plus, next_plus;
        "-", [; is_minus], peek_minus, peek_n_minus, next_minus;
        "*", [; is_asterix], peek_star, peek_n_star, next_star;
        "/", [; is_slash], peek_slash, peek_n_slash, next_slash;
        "%", [; is_percent], peek_percent, peek_n_percent, next_percent;
        "^", [; is_caret], peek_caret, peek_n_caret, next_caret;
        "!", [; is_exclamation], peek_not, peek_n_not, next_not;
        "&", [; is_and], peek_and, peek_n_and, next_and;
        "|", [; is_pipe], peek_or, peek_n_or, next_or;
        "&&", [is_and; is_and], peek_and_and, peek_n_and_and, next_and_and;
        "||", [is_pipe; is_pipe], peek_or_or, peek_n_or_or, next_or_or;
        "<<", [is_less_than; is_less_than], peek_shl, peek_n_shl, next_shl;
        ">>", [is_greater_than; is_greater_than], peek_shr, peek_n_shr, next_shr;
        "+=", [is_plus; is_equals], peek_plus_eq, peek_n_plus_eq, next_plus_eq;
        "-=", [is_minus; is_equals], peek_minus_eq, peek_n_minus_eq, next_minus_eq;
        "*=", [is_asterix; is_equals], peek_star_eq, peek_n_star_eq, next_star_eq;
        "/=", [is_slash; is_equals], peek_slash_eq, peek_n_slash_eq, next_slash_eq;
        "%=", [is_percent; is_equals], peek_percent_eq, peek_n_percent_eq, next_percent_eq;
        "^=", [is_caret; is_equals], peek_caret_eq, peek_n_caret_eq, next_caret_eq;
        "&=", [is_and; is_equals], peek_and_eq, peek_n_and_eq, next_and_eq;
        "|=", [is_pipe; is_equals], peek_or_eq, peek_n_or_eq, next_or_eq;
        "<<=", [is_less_than, is_less_than; is_equals], peek_shl_eq, peek_n_shl_eq, next_shl_eq;
        ">>=", [is_greater_than, is_greater_than; is_equals], peek_shr_eq, peek_n_shr_eq, next_shr_eq;
        "=", [; is_equals], peek_eq, peek_n_eq, next_eq;
        "==", [is_equals; is_equals], peek_eq_eq, peek_n_eq_eq, next_eq_eq;
        "!=", [is_equals; is_equals], peek_ne, peek_n_ne, next_ne;
        ">", [; is_greater_than], peek_gt, peek_n_gt, next_gt;
        "<", [; is_less_than], peek_lt, peek_n_lt, next_lt;
        ">=", [is_greater_than; is_equals], peek_ge, peek_n_ge, next_ge;
        "<=", [is_less_than; is_equals], peek_le, peek_n_le, next_le;
        "@", [; is_at], peek_at, peek_n_at, next_at;
        ".", [; is_dot], peek_dot, peek_n_dot, next_dot;
        "..", [is_dot; is_dot], peek_dot_dot, peek_n_dot_dot, next_dot_dot;
        "...", [is_dot, is_dot; is_dot], peek_dot_dot_dot, peek_n_dot_dot_dot, next_dot_dot_dot;
        "..=", [is_dot, is_dot; is_equals], peek_dot_dot_eq, peek_n_dot_dot_eq, next_dot_dot_eq;
        ",", [; is_comma], peek_comma, peek_n_comma, next_comma;
        ";", [; is_semi], peek_semi, peek_n_semi, next_semi;
        ":", [; is_colon], peek_colon, peek_n_colon, next_colon;
        "::", [is_colon; is_colon], peek_path_sep, peek_n_path_sep, next_path_sep;
        "->", [is_minus; is_greater_than], peek_r_arrow, peek_n_r_arrow, next_r_arrow;
        "=>", [is_minus; is_greater_than], peek_fat_arrow, peek_n_fat_arrow, next_fat_arrow;
        "#", [; is_pound], peek_pound, peek_n_pound, next_pound;
        "$", [; is_dollar], peek_dollar, peek_n_dollar, next_dollar;
        "?", [; is_question], peek_question, peek_n_question, next_question;
        "~", [; is_tilde], peek_tilde, peek_n_tilde, next_tilde;
    );
}

#[cfg(test)]
mod test {
    use quote::quote;

    use super::*;
    use crate::assert_tokens;

    #[test]
    fn ty() {
        let mut at = TokenParser::new(quote! {Name, <Some, Generic, Type>});
        assert_tokens!(at.next_type().unwrap(), { Name });
        at.next();
        assert_tokens!(
            at.next_type().unwrap(),
            { < Some , Generic , Type > }
        );
    }

    #[test]
    fn expr() {
        let mut at = TokenParser::new(
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

    #[test]
    fn combined_tokens() {
        let mut parser = TokenParser::new(quote! {
            -> && ..= >=
        });
        assert_tokens!(parser.next_r_arrow().unwrap(), { -> });
        assert_tokens!(parser.next_and_and().unwrap(), { && });
        assert_tokens!(parser.next_dot_dot_eq().unwrap(), { ..= });
        assert_tokens!(parser.next_ge().unwrap(), { >= });
    }

    #[test]
    fn peek() {
        let mut parser = TokenParser::new(quote! {
            0 {} 2 3 += .. =
        });
        assert_eq!(parser.peek().unwrap().to_string(), "0");
        assert_eq!(parser.peek_n(0).unwrap().to_string(), "0");
        assert_eq!(parser.peek_n(1).unwrap().to_string().replace(' ', ""), "{}");
        assert_eq!(parser.peek_n(2).unwrap().to_string(), "2");

        assert_eq!(parser.peek_literal().unwrap().to_string(), "0");
        assert!(parser.peek_group().is_none());
        parser.next().unwrap();
        assert!(parser.peek_group().is_some());
        assert!(parser.peek_n_plus_eq(3).is_some());
        assert!(parser.peek_n_dot_dot(5).is_some());
    }

    #[test]
    fn keyword() {
        let mut parser: TokenParser<_, 4> = TokenParser::from(quote! {
            in out and or
        });
        assert_eq!(parser.next_keyword("in").unwrap().to_string(), "in");
        assert_eq!(parser.next_keyword("out").unwrap().to_string(), "out");
        assert!(parser.next_keyword("or").is_none());
        assert_eq!(parser.next_keyword("and").unwrap().to_string(), "and");
        assert_eq!(parser.next_keyword("or").unwrap().to_string(), "or");
        assert!(parser.next_keyword("or").is_none());
    }
}
