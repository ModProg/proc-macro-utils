//! Some useful functions on `proc_macro` and `proc_macro2` types
//!
//! E.g. [pushing tokens onto TokenStream](TokenStreamExt::push) and [testing
//! for specific punctuation on TokenTree and Punct](TokenTreePunct)
#![warn(clippy::pedantic)]
#![deny(missing_docs)]

#[cfg(feature = "proc-macro")]
extern crate proc_macro;

// TODO consider splitting up the traits

macro_rules! once {
    (($($tts:tt)*) $($tail:tt)*) => {
        $($tts)*
    };
}

macro_rules! impl_via_trait {
    (
        $(
            $(#$trait_attr:tt)*
            impl $trait:ident for $type:ident {
                $(#$first_attr:tt)*
                $(type $types:ident = $type_assignment:ty; $(#$type_attr:tt)* )*
                $(fn $function:ident($($args:tt)*) $(-> $ret:ty)? { $($stmts:tt)* } $(#$fn_attr:tt)* )*
            }
        )+
    ) => {
        once!($(($(#$trait_attr)* pub trait $trait {
            $(#$first_attr)*
            $(type $types; $(#$type_attr)*)*
            $(fn $function($($args)*) $(-> $ret)?; $(#$fn_attr)*)*
        }))?);
        $(#[cfg(feature = "proc-macro2")]
        const _:() = {
            use proc_macro2::*;
            impl $trait for $type {
                $(type $types = $type_assignment;)*
                $(fn $function($($args)*) $(-> $ret)? {
                    $($stmts)*
                })*
            }
        };
        #[cfg(feature = "proc-macro")]
        const _:() = {
            use proc_macro::*;
            impl $trait for $type {
                $(type $types = $type_assignment;)*
                $(fn $function($($args)*) $(-> $ret)? {
                    $($stmts)*
                })*
            }
        };)+
    };
}

impl_via_trait! {
    /// Generic extensions for
    #[cfg_attr(feature = "proc-macro", doc = "[`proc_macro::TokenStream`]")]
    #[cfg_attr(all(feature = "proc-macro", feature = "proc-macro2"), doc = "and")]
    #[cfg_attr(feature = "proc-macro2", doc = "[`proc_macro2::TokenStream`]")]
    #[cfg_attr(not(any(feature = "proc-macro", feature = "proc-macro2")), doc = "`proc_macro::TokenStream`")]
    impl TokenStreamExt for TokenStream {
        /// TokenTree to support both proc_macro and proc_macro2
        type TokenTree = TokenTree;
        /// Pushes a single [`Self::TokenTree`] onto the token stream
        fn push(&mut self, token: Self::TokenTree) {
            self.extend(std::iter::once(token))
        }
    }
}

macro_rules! token_tree_ext {
    ($($a:literal, $token:literal, $is:ident, $as:ident, $variant:ident);+$(;)?) => {
        impl_via_trait! {
            /// Generic extensions for
            #[cfg_attr(feature = "proc-macro", doc = "[`proc_macro::TokenTree`]")]
            #[cfg_attr(all(feature = "proc-macro", feature = "proc-macro2"), doc = "and")]
            #[cfg_attr(feature = "proc-macro2", doc = "[`proc_macro2::TokenTree`]")]
            #[cfg_attr(not(any(feature = "proc-macro", feature = "proc-macro2")), doc = "`proc_macro::TokenTree`")]
            impl TokenTreeExt for TokenTree {
                $(
                    #[doc = concat!(stringify!($variant), " of this TokenTree, necessary to support both TokenTrees")]
                    type $variant = $variant;
                )*
                $(
                    #[doc = concat!("Tests if the token tree is ", $a, " ", $token, ".")]
                    fn $is(&self) -> bool {
                        matches!(self, Self::$variant(_))
                    }
                    #[doc = concat!("Get the `", stringify!($variant), "` inside this token tree, or [`None`] if it isn't ", $a, " ", $token, ".")]
                    fn $as(self) -> Option<<Self as TokenTreeExt>::$variant> {
                        if let Self::$variant(inner) = self {
                            Some(inner)
                        } else {
                            None
                        }
                    }
                )*
            }
        }
    };
}

token_tree_ext!(
    "a", "group", is_group, group, Group;
    "an", "ident", is_ident, ident, Ident;
    "a", "punctuation", is_punct, punct, Punct;
    "a", "literal", is_literal, literal, Literal;
);

macro_rules! punctuations {
    ($($char:literal as $name:ident),*) => {
        impl_via_trait!{
            /// Trait to test for punctuation
            impl TokenTreePunct for TokenTree {
                $(#[doc = concat!("Tests if the token is `", $char, "`")]
                fn $name(&self) -> bool {
                    matches!(self, TokenTree::Punct(punct) if punct.as_char() == $char)
                })*
            }
            impl TokenTreePunct for Punct {
                $(fn $name(&self) -> bool {
                    self.as_char() == $char
                })*
            }
        }
    };
}

punctuations![
    '=' as is_equals,
    '<' as is_less_than,
    '>' as is_greater_than,
    '!' as is_exclamation,
    '~' as is_tilde,
    '+' as is_plus,
    '-' as is_minus,
    '*' as is_asterix, // TODO naming
    '/' as is_slash,
    '%' as is_percent,
    '^' as is_caret,
    '&' as is_and,
    '|' as is_pipe,
    '@' as is_at,
    '.' as is_dot,
    ',' as is_comma,
    ';' as is_semi,
    ':' as is_colon,
    '#' as is_pound,
    '$' as is_dollar,
    '?' as is_question,
    '\'' as is_quote // TODO naming
];

#[cfg(all(test, feature = "proc-macro2"))]
mod test {
    use proc_macro2::{Punct, Spacing, TokenTree};
    use quote::quote;

    use super::*;

    #[test]
    fn punctuation() {
        let mut tokens = quote! {=<>!$~+-*/%^|@.,;:#$?'a}.into_iter();
        assert!(tokens.next().unwrap().is_equals());
        assert!(tokens.next().unwrap().is_less_than());
        assert!(tokens.next().unwrap().is_greater_than());
        assert!(tokens.next().unwrap().is_exclamation());
        assert!(tokens.next().unwrap().is_dollar());
        assert!(tokens.next().unwrap().is_tilde());
        assert!(tokens.next().unwrap().is_plus());
        assert!(tokens.next().unwrap().is_minus());
        assert!(tokens.next().unwrap().is_asterix());
        assert!(tokens.next().unwrap().is_slash());
        assert!(tokens.next().unwrap().is_percent());
        assert!(tokens.next().unwrap().is_caret());
        assert!(tokens.next().unwrap().is_pipe());
        assert!(tokens.next().unwrap().is_at());
        assert!(tokens.next().unwrap().is_dot());
        assert!(tokens.next().unwrap().is_comma());
        assert!(tokens.next().unwrap().is_semi());
        assert!(tokens.next().unwrap().is_colon());
        assert!(tokens.next().unwrap().is_pound());
        assert!(tokens.next().unwrap().is_dollar());
        assert!(tokens.next().unwrap().is_question());
        assert!(tokens.next().unwrap().is_quote());
    }

    #[test]
    fn token_stream_ext() {
        let mut tokens = quote!(a);
        tokens.push(TokenTree::Punct(Punct::new(',', Spacing::Alone)));
        assert_eq!(tokens.to_string(), "a ,");
    }

    #[test]
    fn token_tree_ext() {
        let mut tokens = quote!({group} ident + "literal").into_iter().peekable();
        assert!(tokens.peek().unwrap().is_group());
        assert_eq!(
            tokens.next().unwrap().group().unwrap().to_string(),
            "{ group }"
        );
        assert!(tokens.peek().unwrap().is_ident());
        assert_eq!(tokens.next().unwrap().ident().unwrap().to_string(), "ident");
        assert!(tokens.peek().unwrap().is_punct());
        assert_eq!(tokens.next().unwrap().punct().unwrap().to_string(), "+");
        assert!(tokens.peek().unwrap().is_literal());
        assert_eq!(
            tokens.next().unwrap().literal().unwrap().to_string(),
            "\"literal\""
        );
    }
}
