pub use minicas_core as core;
pub use minicas_crs as crs;

pub mod prelude {
    pub use crate::core::ast::{AstNode, Node};
    pub use crate::crs::simplify;
}

#[cfg(test)]
#[test]
fn smoke_test() {
    use crate::prelude::*;

    let mut n = Node::try_from("5x -- 2x").unwrap();
    simplify(&mut n, true).unwrap();
    assert_eq!(n, Node::try_from("7x").unwrap());

    let mut n = Node::try_from("5x * 2x").unwrap();
    simplify(&mut n, true).unwrap();
    assert_eq!(n, Node::try_from("10 * pow(x, 2)").unwrap());
    assert_eq!(n.finite_eval(&vec![("x", 3.into())]), Ok(90.into()));
}
