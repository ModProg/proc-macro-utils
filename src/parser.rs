use std::iter::Peekable;

use proc_macro2::*;

use crate::{Delimited, TokenStream2Ext, TokenTree2Ext, TokenTreePunct};

// TODO move implementation in a trait implemented on both
// Peekable<token_stream::IntoIter>s

/// Wrapper for [`TokenStream::into_iter`] allowing not only to iterate on
/// tokens but also to parse simple structures like types or expressions, though
/// it does not make any claims about their correctness.
///
/// ```
/// # use proc_macro2::TokenStream;
/// # use proc_macro_utils::parser::TokenParser;
/// # use proc_macro_utils::assert_tokens;
/// # use quote::quote;
/// let mut token_parser = TokenParser::from(quote! {a + b, c});
/// assert_tokens!(token_parser.next_expression().unwrap(), { a + b });
/// ```
pub struct TokenParser<T: Iterator<Item = TokenTree>>(pub Peekable<T>);

impl<T, I> From<T> for TokenParser<I>
where
    T: IntoIterator<Item = TokenTree, IntoIter = I>,
    I: Iterator<Item = TokenTree>,
{
    fn from(value: T) -> Self {
        Self(value.into_iter().peekable())
    }
}

impl<I: Iterator<Item = TokenTree>> From<TokenParser<I>> for TokenStream {
    fn from(value: TokenParser<I>) -> Self {
        value.0.collect()
    }
}

impl<T: Iterator<Item = TokenTree>> Iterator for TokenParser<T> {
    type Item = TokenTree;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

macro_rules! punct {
    ($($punct:literal, $test:ident, $name:ident);*$(;)?) => {
        $(#[doc = concat!("Returns the next token if it is a `", $punct ,"`")]
        pub fn $name(&mut self) -> Option<Punct> {
            matches!(self.0.peek(), Some(token) if token.$test()).then(|| self.0.next().expect("token should be present").into_punct().expect("should be punctuation"))
        })*
    };
}

macro_rules! token_tree {
    ($($a:literal, $test:ident, $as:ident, $name:ident, $token:ident);*$(;)?) => {
        $(#[doc = concat!("Returns the next token if it is ", $a, " [`", stringify!($token) ,"`]")]
        pub fn $name(&mut self) -> Option<$token> {
            matches!(self.0.peek(), Some(token) if token.$test()).then(|| self.0.next().expect("token should be present").$as().expect(concat!("should be ", stringify!($token))))
        })*
    };
}

macro_rules! delimited {
    ($($test:ident, $name:ident, $doc:literal;)*) => {
        $(#[doc = concat!("Returns the next ", $doc ," group")]
        pub fn $name(&mut self) -> Option<TokenStream> {
            matches!(self.0.peek(), Some(token) if token.$test())
                .then(|| self.next_group().expect("should be group").stream())
        })*
    };
}

impl<T: Iterator<Item = TokenTree>> TokenParser<T> {
    punct!(
        '=', is_equals, next_equals;
        '<', is_less_than, next_less_than;
        '>', is_greater_than, next_greater_than;
        '!', is_exclamation, next_exclamation;
        '~', is_tilde, next_tilde;
        '+', is_plus, next_plus;
        '-', is_minus, next_minus;
        '*', is_asterix, next_asterix;
        '/', is_slash, next_slash;
        '%', is_percent, next_percent;
        '^', is_caret, next_caret;
        '&', is_and, next_and;
        '|', is_pipe, next_pipe;
        '@', is_at, next_at;
        '.', is_dot, next_dot;
        ',', is_comma, next_comma;
        ';', is_semi, next_semi;
        ':', is_colon, next_colon;
        '#', is_pound, next_pound;
        '$', is_dollar, next_dollar;
        '?', is_question, next_question;
        '\'', is_quote, next_quote;
    );

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

    /// Collects remaining tokens back into a [`TokenStream`]
    pub fn into_token_stream(self) -> TokenStream {
        self.into()
    }

    /// Checks if there are remaining tokens
    pub fn is_empty(&mut self) -> bool {
        self.0.peek().is_none()
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

    /// Returns all tokens while `test` evaluates to true.
    ///
    /// Returns `None` if empty or `test(first_token) == false`
    pub fn next_while(&mut self, mut test: impl FnMut(&TokenTree) -> bool) -> Option<TokenStream> {
        if self.0.peek().is_none() || !test(self.0.peek().unwrap()) {
            None
        } else {
            let mut token_stream = TokenStream::new();
            token_stream.push(self.0.next().unwrap());
            while let Some(token) = self.0.next_if(&mut test) {
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

    /// "Parses" a type expression
    ///
    /// This just means it collects all the tokens that should belong to the
    /// type, until it reaches either:
    /// - a `;`
    /// - a `,` or `>` and all `<>` pairs are closed
    /// - the end of the token_stream
    ///
    /// If the token stream is empty, or starts with `,`, `>` or `;` [`None`] is
    /// returned otherwise, [`Some(TokenStream)`](TokenStream) containing
    /// every token up to but excluding the terminator.
    ///
    /// ```
    /// # use proc_macro_utils::parser::TokenParser;
    /// # use proc_macro_utils::assert_tokens;
    /// # use proc_macro2::TokenStream;
    /// # use quote::quote;
    ///
    /// let mut tokens = TokenParser::from(quote! {A<Test, B>, remainder});
    /// assert_tokens!(tokens.next_type().unwrap(), { A<Test, B> });
    /// assert!(tokens.next_type().is_none());
    /// assert_tokens!(tokens.0, { , remainder });
    /// ```
    pub fn next_type(&mut self) -> Option<TokenStream> {
        let Some(first) = self.0.peek() else { return None; };
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
    /// - the end of the token_stream
    ///
    /// If the token stream is empty, or starts with `,` or `;` [`None`] is
    /// returned otherwise, [`Some(TokenStream)`](TokenStream) containing
    /// every token up to but excluding the terminator.
    ///
    /// ```
    /// # use proc_macro_utils::parser::TokenParser;
    /// # use proc_macro_utils::assert_tokens;
    /// # use proc_macro2::TokenStream;
    /// # use quote::quote;
    ///
    /// let mut tokens = TokenParser::from(quote! {A + c ::<a, b>::a < b, next_token});
    /// assert_tokens!(tokens.next_expression().unwrap(), { A + c::<a, b>::a < b });
    /// assert!(tokens.next_expression().is_none());
    /// assert_tokens!(tokens.0, { , next_token });
    /// ```
    pub fn next_expression(&mut self) -> Option<TokenStream> {
        if self.0.peek().is_none()
            || matches!(self.0.peek(), Some(token) if token.is_comma() || token.is_semi())
        {
            return None;
        }

        let mut start = true;

        let mut tokens = TokenStream::new();

        // <a> * <a>
        // <a> => <a>
        'outer: while let Some(token) = self.0.peek() {
            if token.is_semi() || token.is_comma() {
                break;
            }
            if start && token.is_less_than() {
                tokens.push(self.0.next().unwrap());
                loop {
                    if let Some(ty) = self.next_type() {
                        tokens.extend(ty.into_iter());
                    }
                    // next token can only be `,;>` or None
                    let Some(token) = self.0.peek() else { break 'outer }; // Invalid expression
                    if token.is_semi() {
                        break 'outer;
                    }
                    if token.is_greater_than() {
                        tokens.push(self.0.next().unwrap());
                        break;
                    } else if token.is_comma() {
                        tokens.push(self.0.next().unwrap());
                        continue; // Another type
                    };
                }
            }
            if let Some(token) = self.0.next() {
                // TODO this might be too simplistic
                start = token.is_punct();
                tokens.push(token);
            }
        }

        Some(tokens)
    }
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
        at.0.next();
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
        at.0.next();
        assert_tokens!(
            at.next_expression().unwrap(), { <Some, Generic, Type>::something + <a,b> * a < b }
        );
        at.0.next();
        assert_tokens!(at.next_expression().unwrap(), { "hi" });
    }
}
