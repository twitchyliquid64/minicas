use crate::ast::{AstNode, Binary, BinaryOp, NodeInner, Unary, UnaryOp};
use crate::Ty;

/// Describes issues with an AST due to invalid type + operation combinations.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeError {
    UnaryIncompatible(UnaryOp, Ty),
    BinaryIncompatible(BinaryOp, Ty, Ty),
}

/// Checks an AST for type errors.
pub fn typecheck<N: AstNode>(n: &N) -> Result<(), TypeError> {
    let mut err = Ok(());
    n.walk(false, &mut |n| match n {
        NodeInner::Const(_) => true,

        NodeInner::Unary(Unary { op, val }) => {
            if !op.descendant_compatible(val.returns()) {
                err = Err(TypeError::UnaryIncompatible(op.clone(), val.returns()));
                false
            } else {
                true
            }
        }

        NodeInner::Binary(Binary { op, lhs, rhs }) => {
            if !op.descendant_compatible(lhs.returns(), rhs.returns()) {
                err = Err(TypeError::BinaryIncompatible(
                    op.clone(),
                    lhs.returns(),
                    rhs.returns(),
                ));
                false
            } else {
                true
            }
        }
    });

    err
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Node;

    #[test]
    fn basic() {
        assert_eq!(typecheck(&Node::try_from("5").unwrap()), Ok(()),);
        assert_eq!(typecheck(&Node::try_from("true").unwrap()), Ok(()),);
        assert_eq!(typecheck(&Node::try_from("-5").unwrap()), Ok(()),);
        assert_eq!(typecheck(&Node::try_from("3 + 5 * 11").unwrap()), Ok(()),);

        assert_eq!(
            typecheck(&Node::try_from("true + 1").unwrap()),
            Err(TypeError::BinaryIncompatible(
                BinaryOp::Add,
                Ty::Bool,
                Ty::Rational
            )),
        );
        assert_eq!(
            typecheck(&Node::try_from("2 * 3 + false").unwrap()),
            Err(TypeError::BinaryIncompatible(
                BinaryOp::Add,
                Ty::Rational,
                Ty::Bool,
            )),
        );
    }
}
