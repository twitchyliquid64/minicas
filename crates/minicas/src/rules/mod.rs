use crate::ast::{AstNode, Node, NodeInner};
use crate::pred::Predicate;
use serde::{Deserialize, Deserializer};

mod pred_spec;
pub use pred_spec::PredSpec;

/// Describes a rule test, which consists of the expected AST
/// before and after applying a rule.
#[derive(Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TestSpec {
    pub from: String,
    pub to: String,
}

impl TryFrom<TestSpec> for (Node, Node) {
    type Error = String;

    fn try_from(s: TestSpec) -> Result<Self, Self::Error> {
        Ok((s.from.as_str().try_into()?, s.to.as_str().try_into()?))
    }
}

fn deserialize_ast_str<'de, D>(deserializer: D) -> Result<Node, D::Error>
where
    D: Deserializer<'de>,
{
    let buf = String::deserialize(deserializer)?;

    Node::try_from(buf.as_str()).map_err(serde::de::Error::custom)
}

/// Describes the action to perform when a rule matches.
#[derive(Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields, untagged)]
pub enum RuleActionSpec {
    /// Overwrite a part of the AST with a node elsewhere in the AST.
    Replace {
        /// The indexing sequence to fetch the node to be written.
        ///
        /// See [AstNode::get] for more details on indexing.
        from: Vec<usize>,
        /// The indexing sequence the node should be written to.
        ///
        /// See [AstNode::get] for more details on indexing.
        to: Vec<usize>,
    },
    /// Swaps two nodes in the AST.
    Swap { swap: (Vec<usize>, Vec<usize>) },
    /// Constructs a replacement node by starting from some base
    /// and performing actions against it from the original node.
    Rewrite {
        #[serde(deserialize_with = "deserialize_ast_str")]
        base: Node,
        replace: Vec<(Vec<usize>, Vec<usize>)>,
    },
    /// Perform multiple actions in order.
    Multi(Vec<Self>),
}

impl RuleActionSpec {
    /// Applies the action to the given node.
    // TODO: Real error type.
    pub fn apply<N: AstNode + From<Node>>(&self, n: &mut N) -> Result<(), ()> {
        match self {
            Self::Replace { from, to } => {
                let from = n.get(from.iter().map(|i| *i)).ok_or(())?.clone();
                let to = n.get_mut(to.iter().map(|i| *i)).ok_or(())?;
                *to = from;
            }
            Self::Swap { swap: (a, b) } => {
                let mut tmp = NodeInner::new_const(false);
                let a_mut = n.get_mut(a.iter().map(|i| *i)).ok_or(())?;
                std::mem::swap(&mut tmp, a_mut);

                let b_mut = n.get_mut(b.iter().map(|i| *i)).ok_or(())?;
                std::mem::swap(&mut tmp, b_mut);

                let a_mut = n.get_mut(a.iter().map(|i| *i)).ok_or(())?;
                std::mem::swap(&mut tmp, a_mut);
            }
            Self::Rewrite { base, replace } => {
                let mut out: N = N::from(base.clone());

                for (from, to) in replace {
                    let from = n.get(from.iter().map(|i| *i)).ok_or(())?.clone();
                    let to = out.get_mut(to.iter().map(|i| *i)).ok_or(())?;
                    *to = from;
                }
                *n = out;
            }
            Self::Multi(v) => {
                for r in v.iter() {
                    r.apply(n)?;
                }
            }
        }
        Ok(())
    }
}

/// Describes how a rule is specified in a rule file.
#[derive(Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RuleSpec {
    #[serde(alias = "match")]
    pub predicate: PredSpec,

    #[serde(
        alias = "replace",
        alias = "actions",
        alias = "swap",
        alias = "rewrite"
    )]
    pub action: RuleActionSpec,

    #[serde(default)]
    pub tests: Vec<TestSpec>,
}

/// Describes the schema for a rule file.
#[derive(Deserialize, Debug, Clone, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RuleFileSpec {
    pub rules: Vec<RuleSpec>,
}

/// An AST update rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    pred: Predicate,
    action: RuleActionSpec,
    tests: Vec<(Node, Node)>,
}

impl Rule {
    /// Applies the rule to the specified node. True is returned if
    /// the rule matched & an action was taken.
    pub fn eval<N: AstNode + From<Node>>(&self, n: &mut N) -> Result<bool, ()> {
        if self.pred.matches(n) {
            self.action.apply(n)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Run the self tests.
    pub fn self_test(&self) -> Result<(), usize> {
        for (i, (from, to)) in self.tests.iter().enumerate() {
            let mut n = from.clone();
            match self.eval(&mut n) {
                Ok(true) => {}
                Ok(false) => return Err(i),
                Err(()) => return Err(i),
            }
            if &n != to {
                return Err(i);
            }
        }
        Ok(())
    }
}

impl TryFrom<RuleSpec> for Rule {
    type Error = String;

    fn try_from(s: RuleSpec) -> Result<Self, Self::Error> {
        Ok(Self {
            pred: s.predicate.try_into()?,
            action: s.action,
            tests: s
                .tests
                .into_iter()
                .map(|s| <TestSpec as TryInto<(Node, Node)>>::try_into(s))
                .collect::<Result<Vec<(Node, Node)>, String>>()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::BinaryOp;
    use crate::pred::PredicateOp;
    use crate::TyValue;
    use toml::de;

    #[test]
    fn parse_spec() {
        assert_eq!(
            de::from_str::<RuleSpec>(
                r#"
            match.op = '/'
			match.rhs = {const = '1'}

			replace.from = [0] # using the numerator (first lhs)
			replace.to = []    # overwrite self

			tests = [
			    {from = '12 / 1', to = '12'},
			]
            "#
            ),
            Ok(RuleSpec {
                predicate: PredSpec {
                    op: Some("/".to_string()),
                    rhs: Some(Box::new(PredSpec {
                        const_val: Some("1".to_string()),
                        ..PredSpec::default()
                    })),
                    ..PredSpec::default()
                },
                action: RuleActionSpec::Replace {
                    from: vec![0],
                    to: vec![],
                },
                tests: vec![TestSpec {
                    from: "12 / 1".to_string(),
                    to: "12".to_string(),
                }],
            })
        );
    }

    #[test]
    fn convert_spec() {
        assert_eq!(
            de::from_str::<RuleSpec>(
                r#"
            match.op = '/'
			match.rhs = {const = '1'}

			replace.from = [0] # using the numerator (first lhs)
			replace.to = []    # overwrite self

			tests = [
			    {from = '12 / 1', to = '12'},
			]
            "#
            )
            .unwrap()
            .try_into(),
            Ok(Rule {
                pred: Predicate {
                    op: Some(PredicateOp::Binary(BinaryOp::Div)),
                    children: vec![
                        None,
                        Some(Predicate {
                            const_value: Some(TyValue::from(1)),
                            ..Predicate::op(PredicateOp::Const)
                        })
                    ],
                    ..Predicate::default()
                },
                action: RuleActionSpec::Replace {
                    from: vec![0],
                    to: vec![],
                },
                tests: vec![(
                    Node::try_from("12 / 1").unwrap(),
                    Node::try_from("12").unwrap()
                ),],
            })
        );
    }

    #[test]
    fn apply_replace() {
        let rule: Rule = de::from_str::<RuleSpec>(
            r#"
            match.op = '/'
			match.rhs = {const = '1'}

			replace.from = [0] # using the numerator (first lhs)
			replace.to = []    # overwrite self
            "#,
        )
        .unwrap()
        .try_into()
        .unwrap();

        let mut ast = Node::try_from("12 / 1").unwrap();
        assert_eq!(rule.eval(&mut ast), Ok(true));
        assert_eq!(ast, Node::try_from("12").unwrap());
    }

    #[test]
    fn apply_swap() {
        let rule: Rule = de::from_str::<RuleSpec>(
            r#"
            match.op = '*'
            match.lhs = {not_op = 'const'}
            match.rhs = {op = 'const'}

            action.swap = [[0], [1]]
            "#,
        )
        .unwrap()
        .try_into()
        .unwrap();

        let mut ast = Node::try_from("x * 2").unwrap();
        assert_eq!(rule.eval(&mut ast), Ok(true));
        assert_eq!(ast, Node::try_from("2x").unwrap());
    }

    #[test]
    fn apply_rewrite() {
        let rule: Rule = de::from_str::<RuleSpec>(
            r#"
            match.op = '-'
            match.lhs = {op = 'neg'}
            match.rhs = {not_op = 'neg'}

            [rewrite]
            base = "-(1 + 1)"
            replace = [
                [[0, 0], [0, 0]],
                [[1], [0, 1]],
            ]
            "#,
        )
        .unwrap()
        .try_into()
        .unwrap();

        let mut ast = Node::try_from("-12 - 2").unwrap();
        assert_eq!(rule.eval(&mut ast), Ok(true));
        assert_eq!(ast, Node::try_from("-(12 + 2)").unwrap());
    }

    #[test]
    fn selftest() {
        let mut rule: Rule = de::from_str::<RuleSpec>(
            r#"
            match.op = '/'
			match.rhs = {const = '1'}

			actions = [
                {from = [0], to = []},
            ]

			tests = [
			    {from = '12 / 1', to = '12'},
			]
            "#,
        )
        .unwrap()
        .try_into()
        .unwrap();

        assert_eq!(rule.self_test(), Ok(()));

        // mess up the test result
        rule.tests[0].1 = Node::try_from("4x").unwrap();
        assert_eq!(rule.self_test(), Err(0));
    }
}
