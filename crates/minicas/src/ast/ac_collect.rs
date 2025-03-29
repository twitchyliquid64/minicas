use crate::ast::{BinaryOp, NodeInner, Path};

/// Describes issues with collecting terms.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AcError {
    BadVariant,
    NotAssociativeCommutative,
    Internal,
}

fn ac_collect_recursive(
    n: &NodeInner,
    op: BinaryOp,
    path: Path,
    terms: &mut Vec<Path>,
) -> Result<(), ()> {
    match n {
        NodeInner::Binary(b) => {
            if b.op() == op {
                let (mut lp, mut rp) = (path.clone(), path.clone());
                lp.push(0);
                ac_collect_recursive(b.lhs(), op, lp, terms)?;
                rp.push(1);
                ac_collect_recursive(b.rhs(), op, rp, terms)?;
            } else {
                let self_path = path.clone();
                terms.push(self_path);
            }
        }

        // nothing contained to walk
        NodeInner::Const(_) | NodeInner::Var(_) | NodeInner::Unary(_) => {
            let self_path = path.clone();
            terms.push(self_path);
        }
    }

    Ok(())
}

/// Collects paths to all terms below this node which share the same
/// associative + commutative operator.
pub fn ac_collect(n: &NodeInner, terms: &mut Vec<Path>) -> Result<(), AcError> {
    if let Some(b) = n.as_binary() {
        let op = b.op();
        if !op.associative() || !op.commutative() {
            return Err(AcError::NotAssociativeCommutative);
        }

        ac_collect_recursive(n, op, Path::default(), terms).map_err(|_| AcError::Internal)
    } else {
        Err(AcError::BadVariant)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Node;

    #[test]
    fn simple() {
        let n = Node::try_from("5 + 3").unwrap();
        let mut output = Vec::new();
        assert_eq!(ac_collect(&n, &mut output), Ok(()));
        assert_eq!(
            output
                .into_iter()
                .map(|p| p.into())
                .collect::<Vec<Vec<usize>>>(),
            vec![vec![0], vec![1]]
        );
    }

    #[test]
    fn tri() {
        let n = Node::try_from("5 + 3 + 2x").unwrap();
        let mut output = Vec::new();
        assert_eq!(ac_collect(&n, &mut output), Ok(()));
        assert_eq!(
            output
                .into_iter()
                .map(|p| p.into())
                .collect::<Vec<Vec<usize>>>(),
            vec![vec![0, 0], vec![0, 1], vec![1]]
        );
    }

    #[test]
    fn mul() {
        let n = Node::try_from("(2 + 1) * (5 * 3)").unwrap();
        let mut output = Vec::new();
        assert_eq!(ac_collect(&n, &mut output), Ok(()));
        assert_eq!(
            output
                .into_iter()
                .map(|p| format!("{}", n.get(&mut p.iter()).unwrap()))
                .collect::<Vec<_>>(),
            vec!["2 + 1", "5", "3",],
        );
    }
}
