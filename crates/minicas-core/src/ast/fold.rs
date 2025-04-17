//! Implements constant folding/propagation of an AST.
use crate::ast::{AstNode, Binary, EvalError, NodeInner, Unary};

/// Performs constant folding on an AST.
///
/// ```
/// # use minicas_core::ast::{Node, Piecewise};
/// # use minicas_core::ast::fold;
/// let mut n = Node::try_from("2 + 3").unwrap();
/// assert_eq!(fold(&mut n), Ok(()),);
/// assert_eq!(n, Node::try_from("5").unwrap());
/// ```
pub fn fold<N: AstNode>(n: &mut N) -> Result<(), EvalError> {
    let mut err = Ok(());
    n.walk_mut(true, &mut |n| {
        let is_const_expr = match n {
            NodeInner::Unary(Unary { val, .. }) => {
                if val.as_const().is_some() {
                    true
                } else {
                    false
                }
            }
            NodeInner::Binary(Binary { lhs, rhs, .. }) => {
                if lhs.as_const().is_some() && rhs.as_const().is_some() {
                    true
                } else {
                    false
                }
            }
            NodeInner::Piecewise(p) => {
                p.iter_branches()
                    .map(|e| e.0.as_const().is_some() && e.1.as_const().is_some())
                    .all(|b| b)
                    && p.else_branch().as_const().is_some()
            }

            NodeInner::Const(_) | NodeInner::Var(_) => false,
        };

        if is_const_expr {
            match n.finite_eval(&()) {
                Ok(v) => {
                    *n = NodeInner::new_const(v);
                }
                // Ignore multiple, just means we cant simplify in this case
                Err(EvalError::Multiple) => {}
                Err(e) => {
                    err = Err(e);
                }
            }
        }
        true
    });

    err
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Node, Piecewise};

    #[test]
    fn unary() {
        let mut n = Node::try_from("--(5)").unwrap();
        assert_eq!(fold(&mut n), Ok(()),);
        assert_eq!(n, Node::try_from("5").unwrap());
    }

    #[test]
    fn binary() {
        let mut n = Node::try_from("2 + 3").unwrap();
        assert_eq!(fold(&mut n), Ok(()),);
        assert_eq!(n, Node::try_from("5").unwrap());
    }

    #[test]
    fn binary_multiple_solutions() {
        let mut n = Node::try_from("2 ± 1").unwrap();
        assert_eq!(fold(&mut n), Ok(()),);
        assert_eq!(n, Node::try_from("2 ± 1").unwrap());
    }

    #[test]
    fn binary_bool() {
        let mut n = Node::try_from("true == false").unwrap();
        assert_eq!(fold(&mut n), Ok(()),);
        assert_eq!(n, Node::try_from("false").unwrap());
    }

    #[test]
    fn chained() {
        let mut n = Node::try_from("2 + (3 * --2)").unwrap();
        assert_eq!(fold(&mut n), Ok(()),);
        assert_eq!(n, Node::try_from("8").unwrap());
    }

    #[test]
    fn non_const() {
        let mut n = Node::try_from("2 + (3x / 2)").unwrap();
        assert_eq!(fold(&mut n), Ok(()),);
        assert_eq!(n, Node::try_from("2 + (3x / 2)").unwrap());
    }

    #[test]
    fn piecewise() {
        let mut n: Node = NodeInner::from(Piecewise::new(
            vec![(
                Node::try_from("x == 5").unwrap().into(),
                Node::try_from("x == y").unwrap().into(),
            )],
            Node::try_from("5").unwrap().into(),
        ))
        .into();
        assert_eq!(fold(&mut n), Ok(()),);

        let mut n: Node = NodeInner::from(Piecewise::new(
            vec![(
                Node::try_from("5").unwrap().into(),
                Node::try_from("true").unwrap().into(),
            )],
            Node::try_from("1").unwrap().into(),
        ))
        .into();
        assert_eq!(fold(&mut n), Ok(()),);
        assert_eq!(n, Node::try_from("5").unwrap());
    }
}
