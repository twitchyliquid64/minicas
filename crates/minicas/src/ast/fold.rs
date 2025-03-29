use crate::ast::{AstNode, Binary, EvalError, NodeInner, Unary};

/// Performs constant folding on an AST.
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

            NodeInner::Const(_) | NodeInner::Var(_) => false,
        };

        if is_const_expr {
            match n.finite_eval(&()) {
                Ok(v) => {
                    *n = NodeInner::new_const(v);
                }
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
    use crate::ast::Node;

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
}
