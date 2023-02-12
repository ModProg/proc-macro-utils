use proc_macro::{Literal, TokenStream, TokenTree};
use proc_macro_utils::{TokenStreamExt, TokenTreeExt};

#[proc_macro]
pub fn proc_macro(tokens: TokenStream) -> TokenStream {
    let mut tokens = tokens.into_iter();

    assert!(tokens.next().unwrap().is_group());
    assert!(tokens.next().unwrap().is_ident());
    assert!(tokens.next().unwrap().is_punct());
    assert!(tokens.next().unwrap().is_literal());

    let mut tokens = TokenStream::new();
    tokens.push(TokenTree::Literal(Literal::string("It Works!")));
    tokens
}
