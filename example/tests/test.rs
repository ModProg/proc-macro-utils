use example::proc_macro;

#[test]
fn proc_macro() {
    assert_eq!(proc_macro!( { group } ident , "literal"), "It Works!")
}
