use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{digit1, multispace0},
    combinator::{fail, map_res},
    sequence::{delimited, preceded},
    IResult,
};
use nom_language::precedence::precedence;
use nom_language::precedence::{binary_op, unary_op, Assoc, Operation};

#[derive(Clone, Debug, PartialEq)]
pub enum ParseNode<'a> {
    Int(i64),
    Float(f64),
    Bool(bool),
    Unary {
        op: &'a str,
        operand: Box<ParseNode<'a>>,
    },
    Binary {
        op: &'a str,
        lhs: Box<ParseNode<'a>>,
        rhs: Box<ParseNode<'a>>,
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
            delimited(tag("("), parser, tag(")")),
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
}
