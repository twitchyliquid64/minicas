//! Internals of minicas, a small Computer Algebra System.
//!
//! In this crate, you will generally work on implementations of [ast::AstNode]. These are:
//!
//!  * The enum [ast::NodeInner], which concretely implements the different variants of the AST
//!  * The wrapper [ast::Node], which wraps a [ast::NodeInner]
//!  * The heap-allocated wrapper [ast::HN], which is a node on the heap.
//!
//! Creating an AST is easiest done by parsing it from a string:
//!
//! ```
//! use minicas_core::ast::*;
//! let mut n = Node::try_from("5x * 2x").unwrap();
//! ```
//! Though an AST may be constructed manually (see tests for examples of this).
//!
//! Once you have an AST, you can typically work with it by calling methods on it, such as [ast::AstNode::finite_eval]:
//!
//! ```
//! # use minicas_core::ast::*;
//! // EG: Evaluating an expression with variables
//! assert_eq!(
//! 	Node::try_from("{x if x > y; otherwise y}")
//! 		.unwrap()
//! 		.finite_eval(&vec![("x", 42.into()), ("y", 4.into())]),
//! 	Ok(42.into()),
//! );
//!
//! // EG: Interval arithmetic
//! assert_eq!(
//! 	Node::try_from("x - 2y")
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
//! Theres also a number of algorithm modules in [ast]:
//!
//! ```
//! use minicas_core::ast::*;
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

pub mod ast;
mod ty;
pub use ty::{Ty, TyValue};

pub mod pred;

pub mod rules;

mod path;
pub use path::Path;
