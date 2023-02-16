/// Asserts that the `lhs` matches the tokens wrapped in braces on the `rhs`.
///
/// `lhs` needs to be an expression implementing `IntoIterator<Item=TokenTree>`
/// e.g. [`TokenStream`](proc_macro2::TokenStream) or
/// [`TokenParser`](crate::TokenParser).
/// ```
/// # use quote::quote;
/// # use proc_macro_utils::assert_tokens;
/// let some_tokens = quote! { ident, { group } };
///
/// assert_tokens! {some_tokens, { ident, {group} }};
/// ```
#[macro_export]
#[cfg(doc)]
macro_rules! assert_tokens {
    ($lhs:expr, { $($rhs:tt)* }) => {};
}

#[macro_export]
#[cfg(not(doc))]
#[doc(hidden)]
macro_rules! assert_tokens {
    ($lhs:expr, {$($rhs:tt)*}) => {
        let mut lhs = $crate::TokenParser::from($lhs);
        assert_tokens!(@O lhs, "", $($rhs)*);
    };
    (@E $prefix:expr, $expected:tt, $found:tt) => {
        panic!("expected\n    {}\nfound\n    {}\nat\n    {} {}", stringify!$expected, $found, $prefix, $found);
    };
    (@E $prefix:expr, $expected:tt) => {
        panic!("unexpected end, expected\n    {}\nafter\n    {}", stringify!$expected, $prefix);
    };
    (@G $lhs:ident, $fn:ident, $aggr:expr, $sym:literal, $group:tt, {$($inner:tt)*}, $($rhs:tt)*) => {
        if let Some(lhs) = $lhs.$fn() {
            let mut lhs = $crate::TokenParser::from(lhs);
            assert_tokens!(@O lhs, concat!($aggr, ' ', $sym), $($inner)*);
        } else if let Some(lhs) = $lhs.next() {
            assert_tokens!(@E $aggr, ($group), lhs);
        } else {
            assert_tokens!(@E $aggr, ($group));
        }
        assert_tokens!(@O $lhs, assert_tokens!(@C $aggr, $group), $($rhs)*);
    };
    // These don't add a whitespace in front
    (@C $lhs:expr, ,) => {
        concat!($lhs, ',')
    };
    (@C $lhs:expr, :) => {
        concat!($lhs, ':')
    };
    (@C $lhs:expr, ;) => {
        concat!($lhs, ';')
    };
    (@C $lhs:expr, .) => {
        concat!($lhs, '.')
    };
    // All other tokens do
    (@C $lhs:expr, $rhs:tt) => {
        concat!($lhs, ' ', stringify!($rhs))
    };
    (@O $lhs:ident, $aggr:expr,) => { assert!($lhs.is_empty(), "unexpected left over tokens `{}`", $lhs.into_token_stream()); };
    (@O $lhs:ident, $aggr:expr, ( $($inner:tt)* ) $($rhs:tt)*) => {
        assert_tokens!(@G $lhs, next_parenthesized, $aggr, '(', { $($inner)* }, { $($inner)* }, $($rhs)*);
    };
    (@O $lhs:ident, $aggr:expr, { $($inner:tt)* } $($rhs:tt)*) => {
        assert_tokens!(@G $lhs, next_braced, $aggr, '{', { $($inner)* }, { $($inner)* }, $($rhs)*);
    };
    (@O $lhs:ident, $aggr:expr, [ $($inner:tt)* ] $($rhs:tt)*) => {
        assert_tokens!(@G $lhs, next_bracketed, $aggr, '[', [ $($inner)* ], { $($inner)* }, $($rhs)*);
    };
    (@O $lhs:ident, $aggr:expr, $token:tt $($rhs:tt)*) => {
        if let Some(lhs) = $lhs.next_punctuation_group().map(|t|t.to_string()).or_else(|| $lhs.next().map(|t|t.to_string())) {
            if(lhs != stringify!($token)) {
                assert_tokens!(@E $aggr, ($token), lhs);
            }
        } else {
            // TODO
            panic!("expected `{}` but found EOF", stringify!($token));
        }
        assert_tokens!(@O $lhs, assert_tokens!(@C $aggr, $token), $($rhs)*);
    };
}

#[test]
fn test() {
    use quote::quote;
    assert_tokens!(quote!(ident ident, { group/test, vec![a, (a + b)] }, "literal" $), {
        ident ident, { group /test, vec![a,(a+b)] }, "literal" $
    });
    assert_tokens!(quote!(:::), {
        :::
    });
    assert_tokens!(quote!(more:::test::test:: hello :-D $$$ It should just work), {
        more ::: test ::test:: hello :-D $$$ It should just work
    });
}
