//! A smol Computer Algebra System.
//!
//! Creating an AST is easiest done by parsing it from a string:
//!
//! ```
//! use minicas_core::ast::*;
//! let mut n = Node::try_from("5x * 2x").unwrap();
//! ```
//! Though an AST may be constructed manually (see [minicas_core] tests for examples of this).
//!
//! Once you have an AST, you can typically work with it by calling methods on it, such as [finite_eval()](prelude::AstNode::finite_eval):
//!
//! ```
//! # use minicas_core::ast::*;
//! // EG: Evaluating an expression with variables
//! assert_eq!(
//!     Node::try_from("{x if x > y; otherwise y}")
//!         .unwrap()
//!         .finite_eval(&vec![("x", 42.into()), ("y", 4.into())]),
//!     Ok(42.into()),
//! );
//!
//! // EG: Interval arithmetic
//! assert_eq!(
//!     Node::try_from("x - 2y")
//!         .unwrap()
//!         .eval_interval(&vec![
//!             ("x", (1.into(), 2.into())),
//!             ("y", (5.into(), 6.into()))
//!         ])
//!         .unwrap()
//!         .collect::<Result<Vec<_>, _>>(),
//!     Ok(vec![((-11).into(), (-8).into())]),
//! );
//! ```
//!
//! Theres also a number of algorithm modules in [core::ast]:
//!
//! ```
//! # use minicas::prelude::*;
//! use minicas::algs::*;
//!
//! // EG: Rearrange the equation
//! let mut lhs = NodeInner::new_var("d");
//! make_subject(
//!     &mut lhs,
//!     &Node::try_from("sqrt(pow(x2 - x1, 2) + pow(y2 - y1, 2))").unwrap(),
//!     &Node::try_from("x2").unwrap() // rearrange for x2
//! );
//! assert_eq!(
//!     &lhs,
//!     Node::try_from("0 ± sqrt(pow(d, 2) - pow(y2 - y1, 2)) + x1")
//!         .unwrap()
//!         .as_inner(),
//! );
//!
//! // EG: Constant folding
//! let mut n = Node::try_from("x + (3 * --2)").unwrap();
//! assert_eq!(fold(&mut n), Ok(()),);
//! assert_eq!(n, Node::try_from("x + 6").unwrap());
//! ```
pub use minicas_core as core;
pub use minicas_crs as crs;

pub mod prelude {
    pub use crate::core::ast::{AstNode, Node, NodeInner};
    pub use crate::crs::simplify;
}

/// Re-exports of common algorithms.
pub mod algs {
    pub use crate::core::ast::{fold, make_subject};
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
