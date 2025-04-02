use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, digit0, digit1, multispace0, multispace1},
    combinator::{fail, map_res},
    multi::many0,
    sequence::{delimited, preceded, separated_pair},
    IResult,
};
use nom_language::precedence::precedence;
use nom_language::precedence::{binary_op, unary_op, Assoc, Operation};

#[derive(Clone, Debug, PartialEq)]
pub enum ParseNode<'a> {
    Int(i64),
    Float(f64),
    Bool(bool),
    Ident(String),
    IdentWithCoefficient(u64, String),
    Unary {
        op: &'a str,
        operand: Box<ParseNode<'a>>,
    },
    Abs(Box<ParseNode<'a>>),
    Binary {
        op: &'a str,
        lhs: Box<ParseNode<'a>>,
        rhs: Box<ParseNode<'a>>,
    },
    Piecewise {
        arms: Vec<(Box<ParseNode<'a>>, Box<ParseNode<'a>>)>,
        otherwise: Box<ParseNode<'a>>,
    },
}

pub fn parse(i: &str) -> IResult<&str, ParseNode> {
    parser(i)
}

fn parser(i: &str) -> IResult<&str, ParseNode> {
    precedence(
        unary_op(1, preceded(multispace0, tag("-"))),
        fail(),
        preceded(
            multispace0,
            alt((
                binary_op(2, Assoc::Left, tag("*")),
                binary_op(2, Assoc::Left, tag("/")),
                binary_op(3, Assoc::Left, tag("+")),
                binary_op(3, Assoc::Left, tag("-")),
                binary_op(4, Assoc::Left, tag("==")),
                binary_op(4, Assoc::Left, tag(">")),
                binary_op(4, Assoc::Left, tag(">=")),
                binary_op(4, Assoc::Left, tag("<")),
                binary_op(4, Assoc::Left, tag("<=")),
            )),
        ),
        alt((
            map_res(
                preceded(multispace0, (digit1, tag("."), digit1)),
                |(major, _dot, minor): (&str, &str, &str)| {
                    let mut s = String::from(major);
                    s.push_str(".");
                    s.push_str(minor);

                    if let Ok(f) = s.parse::<f64>() {
                        return Ok(ParseNode::Float(f));
                    }
                    Err(())
                },
            ),
            map_res(
                preceded(multispace0, (digit1, alpha1, digit0)),
                |(co_eff, ident, trailing_num): (&str, &str, &str)| {
                    if let Ok(co_eff) = co_eff.parse::<u64>() {
                        let ident = String::from(ident) + trailing_num;
                        return Ok(ParseNode::IdentWithCoefficient(co_eff, ident));
                    }
                    Err(())
                },
            ),
            map_res(
                preceded(multispace0, delimited(tag("|"), parser, tag("|"))),
                |n| Ok::<ParseNode<'_>, ()>(ParseNode::Abs(Box::new(n))),
            ),
            map_res(
                preceded(multispace0, delimited(tag("abs("), parser, tag(")"))),
                |n| Ok::<ParseNode<'_>, ()>(ParseNode::Abs(Box::new(n))),
            ),
            map_res(preceded(multispace0, digit1), |s: &str| {
                if let Ok(i) = s.parse::<i64>() {
                    return Ok(ParseNode::Int(i));
                }
                Err(())
            }),
            map_res(preceded(multispace0, tag("true")), |_| {
                Ok::<ParseNode<'_>, ()>(ParseNode::Bool(true))
            }),
            map_res(preceded(multispace0, tag("false")), |_| {
                Ok::<ParseNode<'_>, ()>(ParseNode::Bool(false))
            }),
            map_res(
                preceded(multispace0, (alpha1, digit0)),
                |(s, t): (&str, &str)| {
                    let ident = String::from(s) + t;
                    Ok::<ParseNode<'_>, ()>(ParseNode::Ident(ident))
                },
            ),
            preceded(multispace0, delimited(tag("("), parser, tag(")"))),
            map_res(
                preceded(
                    multispace0,
                    delimited(
                        tag("{"),
                        separated_pair(
                            many0(delimited(
                                multispace0,
                                separated_pair(
                                    parser,
                                    (multispace1, tag("if"), multispace1),
                                    parser,
                                ),
                                (multispace0, tag(";")),
                            )),
                            (multispace0, tag("otherwise"), multispace1),
                            parser,
                        ),
                        (multispace0, tag("}")),
                    ),
                ),
                |(arms, otherwise): (Vec<(ParseNode, ParseNode)>, ParseNode)| {
                    Ok::<ParseNode<'_>, ()>(ParseNode::Piecewise {
                        arms: arms
                            .into_iter()
                            .map(|(e, c)| (Box::new(e), Box::new(c)))
                            .collect(),
                        otherwise: Box::new(otherwise),
                    })
                },
            ),
        )),
        |op: Operation<&str, (), &str, ParseNode>| {
            use nom_language::precedence::Operation::*;
            match op {
                Prefix("-", o) => Ok(ParseNode::Unary {
                    op: "-",
                    operand: Box::new(o),
                }),
                Binary(lhs, op, rhs) => Ok(ParseNode::Binary {
                    op: op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }),
                _ => Err("Invalid combination"),
            }
        },
    )(i)
}

#[test]
fn literals() {
    assert_eq!(parser("3"), Ok(("", ParseNode::Int(3))));
    assert_eq!(parser("2.5"), Ok(("", ParseNode::Float(2.5))));
    assert_eq!(parser("true"), Ok(("", ParseNode::Bool(true))));
    assert_eq!(parser("false "), Ok((" ", ParseNode::Bool(false))));
}

#[test]
fn vars() {
    assert_eq!(parser("x"), Ok(("", ParseNode::Ident("x".into()))));
    assert_eq!(parser("ab"), Ok(("", ParseNode::Ident("ab".into()))));
    assert_eq!(
        parser("2x"),
        Ok(("", ParseNode::IdentWithCoefficient(2, "x".into())))
    );
    assert_eq!(parser("a1"), Ok(("", ParseNode::Ident("a1".into()))));
    assert_eq!(
        parser("2x11"),
        Ok(("", ParseNode::IdentWithCoefficient(2, "x11".into())))
    );
}

#[test]
fn abs() {
    assert_eq!(
        parser("|3|"),
        Ok(("", ParseNode::Abs(Box::new(ParseNode::Int(3)))))
    );
    assert_eq!(
        parser("abs(2)"),
        Ok(("", ParseNode::Abs(Box::new(ParseNode::Int(2)))))
    );
}

#[test]
fn parenthesis() {
    assert_eq!(parser("(3)"), Ok(("", ParseNode::Int(3))));
    assert_eq!(
        parser("(-3)"),
        Ok((
            "",
            ParseNode::Unary {
                op: &"-",
                operand: Box::new(ParseNode::Int(3)),
            }
        ))
    );

    assert_eq!(
        parser("-(3)"),
        Ok((
            "",
            ParseNode::Unary {
                op: &"-",
                operand: Box::new(ParseNode::Int(3)),
            }
        ))
    );
    assert_eq!(
        parser("-((4 - 3) + 2)"),
        Ok((
            "",
            ParseNode::Unary {
                op: &"-",
                operand: Box::new(ParseNode::Binary {
                    op: &"+",
                    lhs: Box::new(ParseNode::Binary {
                        op: &"-",
                        lhs: Box::new(ParseNode::Int(4)),
                        rhs: Box::new(ParseNode::Int(3)),
                    }),
                    rhs: Box::new(ParseNode::Int(2)),
                }),
            }
        ))
    );
    assert_eq!(
        parser("3 + (2 + 3)"),
        Ok((
            "",
            ParseNode::Binary {
                op: &"+",
                lhs: Box::new(ParseNode::Int(3)),
                rhs: Box::new(ParseNode::Binary {
                    op: &"+",
                    lhs: Box::new(ParseNode::Int(2)),
                    rhs: Box::new(ParseNode::Int(3)),
                }),
            }
        ))
    );
}

#[test]
fn op_precedence() {
    assert_eq!(
        parser("2 - 3 * 2"),
        Ok((
            "",
            ParseNode::Binary {
                op: &"-",
                lhs: Box::new(ParseNode::Int(2)),
                rhs: Box::new(ParseNode::Binary {
                    op: &"*",
                    lhs: Box::new(ParseNode::Int(3)),
                    rhs: Box::new(ParseNode::Int(2)),
                }),
            }
        ))
    );
}

#[test]
fn basic() {
    assert_eq!(
        parser("-3"),
        Ok((
            "",
            ParseNode::Unary {
                op: &"-",
                operand: Box::new(ParseNode::Int(3)),
            }
        ))
    );

    assert_eq!(
        parser("4-3"),
        Ok((
            "",
            ParseNode::Binary {
                op: &"-",
                lhs: Box::new(ParseNode::Int(4)),
                rhs: Box::new(ParseNode::Int(3)),
            }
        ))
    );
    assert_eq!(
        parser("4 - 3"),
        Ok((
            "",
            ParseNode::Binary {
                op: &"-",
                lhs: Box::new(ParseNode::Int(4)),
                rhs: Box::new(ParseNode::Int(3)),
            }
        ))
    );
    assert_eq!(
        parser("4 - 3 * 4"),
        Ok((
            "",
            ParseNode::Binary {
                op: &"-",
                lhs: Box::new(ParseNode::Int(4)),
                rhs: Box::new(ParseNode::Binary {
                    op: &"*",
                    lhs: Box::new(ParseNode::Int(3)),
                    rhs: Box::new(ParseNode::Int(4)),
                }),
            }
        ))
    );
    assert_eq!(
        parser("(4 - 3) * 4  "),
        Ok((
            "  ",
            ParseNode::Binary {
                op: &"*",
                lhs: Box::new(ParseNode::Binary {
                    op: &"-",
                    lhs: Box::new(ParseNode::Int(4)),
                    rhs: Box::new(ParseNode::Int(3)),
                }),
                rhs: Box::new(ParseNode::Int(4)),
            }
        ))
    );

    assert_eq!(
        parser("4==3"),
        Ok((
            "",
            ParseNode::Binary {
                op: &"==",
                lhs: Box::new(ParseNode::Int(4)),
                rhs: Box::new(ParseNode::Int(3)),
            }
        ))
    );
}

#[test]
fn piecewise() {
    assert_eq!(
        parser("{-1 if x < 0; 1 if x > 0; otherwise 0}"),
        Ok((
            "",
            ParseNode::Piecewise {
                arms: vec![
                    (
                        Box::new(ParseNode::Unary {
                            op: &"-",
                            operand: Box::new(ParseNode::Int(1)),
                        }),
                        Box::new(ParseNode::Binary {
                            op: &"<",
                            lhs: Box::new(ParseNode::Ident("x".into())),
                            rhs: Box::new(ParseNode::Int(0)),
                        }),
                    ),
                    (
                        Box::new(ParseNode::Int(1)),
                        Box::new(ParseNode::Binary {
                            op: &">",
                            lhs: Box::new(ParseNode::Ident("x".into())),
                            rhs: Box::new(ParseNode::Int(0)),
                        }),
                    ),
                ],
                otherwise: Box::new(ParseNode::Int(0)),
            }
        ))
    );
}
