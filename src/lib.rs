//! Some useful functions on `proc_macro` and `proc_macro2` types
//!
//! E.g. [pushing tokens onto TokenStream](TokenStreamExt::push) and [testing
//! for specific punctuation on TokenTree and Punct](TokenTreePunct)
#![warn(clippy::pedantic)]
#![deny(missing_docs)]

#[cfg(feature = "proc-macro")]
extern crate proc_macro;

macro_rules! once {
    (($($tts:tt)*) $($tail:tt)*) => {
        $($tts)*
    };
}

macro_rules! attr {
    (($($attr:tt)*), $($item:tt)+) => {
        $(#$attr)* $($item)+
    };
}

macro_rules! trait_def {
    ($item_attr:tt, $trait:ident, $($fn_attr:tt, $fn:ident, $args:tt, $($ret:ty)?),*) => {
        attr!($item_attr,
        pub trait $trait {
            $(attr!($fn_attr, fn $fn $args $(-> $ret)?;);)*
        });
    };
}

macro_rules! trait_impl {
    ($trait:ident, $type:ident, $($fn:ident, $args:tt, $($ret:ty)?, $stmts:tt),*) => {
        impl $trait for $type {
            $(fn $fn $args $(-> $ret)? $stmts)*
        }
    };
}

macro_rules! impl_via_trait {
    ($(
        $(#$trait_attr:tt)*
        impl $trait:ident for $type:ident {
            $($(#$fn_attr:tt)*
            fn $fn:ident $args:tt $(-> $ret:ty)? { $($stmts:tt)* })*
        }
    )+) => {
        once!($((trait_def!(($($trait_attr)*), $trait, $(($($fn_attr)*), $fn, $args, $($ret)?),*);))+);
        #[cfg(feature = "proc-macro")]
        const _: () = {
            use proc_macro::*;
            $(trait_impl!($trait, $type, $($fn, $args, $($ret)?, {$($stmts)*}),*);)+
        };
        #[cfg(feature = "proc-macro2")]
        const _:() = {
            use proc_macro2::*;
            $(trait_impl!($trait, $type, $($fn, $args, $($ret)?, {$($stmts)*}),*);)+
        };
    };
    (
        mod $mod:ident, $mod2:ident {
            $(
                $(#$trait_attr:tt)*
                impl $trait:ident$($doc:literal)?, $trait2:ident$($doc2:literal)?  for $type:ident {
                    $($(#$fn_attr:tt)*
                    fn $fn:ident $args:tt $(-> $ret:ty)? { $($stmts:tt)* })*
                }
            )+
        }
    ) => {
        #[cfg(feature = "proc-macro")]
        once!(($(pub use $mod::$trait;)+));
        #[cfg(feature = "proc-macro")]
        mod $mod {
            use proc_macro::*;
            once!($((trait_def!(($($trait_attr)* $([doc=$doc])?), $trait, $(($($fn_attr)*), $fn, $args, $($ret)?),*);))+);
            $(trait_impl!($trait, $type, $($fn, $args, $($ret)?, {$($stmts)*}),*);)+
        }
        #[cfg(feature = "proc-macro2")]
        once!(($(pub use $mod2::$trait2;)+));
        #[cfg(feature = "proc-macro2")]
        mod $mod2 {
            use proc_macro2::*;
            once!($((trait_def!(($($trait_attr)*$([doc=$doc2])?), $trait2, $(($($fn_attr)*), $fn, $args, $($ret)?),*);))+);
            $(trait_impl!($trait2, $type, $($fn, $args, $($ret)?, {$($stmts)*}),*);)+
        }
    };
}

impl_via_trait! {
    mod token_stream_ext, token_stream2_ext {
        /// Generic extensions for
        impl TokenStreamExt "[`proc_macro::TokenStream`]", TokenStream2Ext "[`proc_macro2::TokenStream`]" for TokenStream {
            /// Pushes a single [`TokenTree`] onto the token stream
            fn push(&mut self, token: TokenTree) {
                self.extend(std::iter::once(token))
            }
        }
    }
}

macro_rules! token_tree_ext {
    ($($a:literal, $token:literal, $is:ident, $as:ident, $variant:ident);+$(;)?) => {
        impl_via_trait! {
            mod token_tree_ext, token_tree2_ext {
                /// Generic extensions for
                impl TokenTreeExt "[`proc_macro::TokenTree`]", TokenTree2Ext "[`proc_macro2::TokenTree`]"  for TokenTree {
                    $(
                        #[doc = concat!("Tests if the token tree is ", $a, " ", $token, ".")]
                        fn $is(&self) -> bool {
                            matches!(self, Self::$variant(_))
                        }
                        #[doc = concat!("Get the [`", stringify!($variant), "`] inside this token tree, or [`None`] if it isn't ", $a, " ", $token, ".")]
                        fn $as(self) -> Option<$variant> {
                            if let Self::$variant(inner) = self {
                                Some(inner)
                            } else {
                                None
                            }
                        }
                    )*
                }
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
        assert!(matches!(
            tokens.next().unwrap().group().unwrap().to_string().as_str(),
            "{ group }" | "{group}"
        ));
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
