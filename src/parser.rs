use chumsky::{
    input::{Stream, ValueInput},
    prelude::*,
};
use logos::Logos;

use crate::lexer::Token::{self, *};

// TODO include spans for better error reporting
pub type Ast = Vec<SchemaDecl>;

#[derive(Clone, Debug, PartialEq)]
pub struct SchemaDecl {
    id: String,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Logical {
    True,
    False,
    Unknown,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    Binary(usize),
    Logical(Logical),
    // TODO differentiate between float and integers?
    Real(f64),
    // TODO differentiate between encoded and simple string?
    String(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `NOT`
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    /* Mul-like */
    /// `*`
    Mul,
    /// `/`
    RealDiv,
    /// `DIV`
    IntegerDiv,
    /// `MOD`
    Mod,
    /// `AND`
    And,
    /// `||`, Complex entity instance construction operator (12.10)
    ComplexEntityInstanceConstruction,

    /* Add-like */
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `OR`
    Or,
    /// `XOR`
    Xor,

    /// `**`
    Pow,
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinaryOperation {
    op: BinOp,
    lhs: Box<Expr>,
    rhs: Box<Expr>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct UnaryOperation {
    op: UnaryOp,
    rhs: Box<Expr>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Literal(Literal),
    BinaryOperation(BinaryOperation),
    UnaryOperation(UnaryOperation),
}

// pub struct QualifiableFactor {}

pub fn literal_parser<'src, I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>>(
) -> impl Parser<'src, I, Literal, extra::Err<Rich<'src, Token<'src>>>> + Clone {
    select! {
        BINARY_LITERAL(num) => Literal::Binary(num),
        INTEGER_LITERAL(num) => Literal::Real(num),
        FLOAT_LITERAL(num) => Literal::Real(num),
        SIMPLE_STRING_LITERAL(str) => Literal::String(str.into()),
        TRUE => Literal::Logical(Logical::True),
        FALSE => Literal::Logical(Logical::False),
        UNKNOWN => Literal::Logical(Logical::Unknown),
    }
    .or(select! {ENCODED_STRING_LITERAL(s) => s}.validate(|s, span, emitter| {
        let encoded_bytes = (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()) // can be unwrapped, as the lexer already checks if the char is in range
            .collect();
        Literal::String(String::from_utf8(encoded_bytes).unwrap_or_else(|_| {
            // TODO span could be more precise by checking inside the string
            emitter.emit(Rich::custom(span, "invalid unicode character"));
            String::from('\u{FFFD}') // unicode replacement character
        }))
    }))
}

pub fn expr_parser<'src, I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>>(
) -> impl Parser<'src, I, Expr, extra::Err<Rich<'src, Token<'src>>>> + Clone {
    recursive(|expr| {
        let primary = literal_parser().map(Expr::Literal); // TODO QualifiableFactor

        let paren_expr = expr.delimited_by(just(OPEN_PAREN), just(CLOSE_PAREN));

        let unary_op = select! {
            PLUS => UnaryOp::Plus,
            MINUS => UnaryOp::Minus,
            NOT => UnaryOp::Not,
        }
        .then(primary.clone().or(paren_expr.clone()))
        .map(|(op, arg)| Expr::UnaryOperation(UnaryOperation { op, rhs: Box::new(arg) })); // TODO expression

        let atom = unary_op.or(primary).or(paren_expr); // TODO aggregate_initializer | entity_constructor | enumeration_reference | interval | query_expression

        let exp = atom.clone().then_ignore(just(DOUBLE_STAR)).repeated().foldr(atom.clone(), |lhs, rhs| {
            Expr::BinaryOperation(BinaryOperation { op: BinOp::Pow, lhs: lhs.into(), rhs: rhs.into() })
        });
        exp.or(atom)
    })
}

pub fn parser<'src, I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>>(
) -> impl Parser<'src, I, Ast, extra::Err<Rich<'src, Token<'src>>>> {
    just(SCHEMA)
        .ignore_then(select! { SIMPLE_ID(id) => SchemaDecl { id: id.into() } })
        .then_ignore(just(SEMICOLON))
        .then_ignore(just(END_SCHEMA))
        .repeated()
        .at_least(1)
        .collect::<Vec<_>>()
}

pub fn parse(src: &str) -> Ast {
    let token_iter = Token::lexer(src).spanned().map(|(tok, span)| (tok, span.into()));
    let token_stream = Stream::from_iter(token_iter)
        // Tell chumsky to split the (Token, SimpleSpan) stream into its parts so that it can handle the spans for us
        // This involves giving chumsky an 'end of input' span: we just use a zero-width span at the end of the string
        .spanned((src.len()..src.len()).into());

    // Parse the token stream with our chumsky parser
    parser().parse(token_stream).into_result().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! parse {
        ($parser:expr, $src:expr) => {{
            let token_iter = Token::lexer($src)
                .spanned()
                .map(|(tok, span)| (tok, span.into()));
            let token_stream = Stream::from_iter(token_iter)
                // Tell chumsky to split the (Token, SimpleSpan) stream into its parts so that it can handle the spans for us
                // This involves giving chumsky an 'end of input' span: we just use a zero-width span at the end of the string
                .spanned(($src.len()..$src.len()).into());

            // Parse the token stream with our chumsky parser
            $parser().parse(token_stream).into_result().unwrap()
        }};
    }

    macro_rules! parse_eq {
        ($parser:expr, $src:expr, $eq:expr) => {
            assert_eq!(parse!($parser, $src), $eq)
        };
    }

    #[test]
    fn parses_simple_schema() {
        parse_eq!(parser, "SCHEMA simple; END_SCHEMA", vec![SchemaDecl { id: "simple".to_owned() }]);
    }

    #[test]
    fn parses_literals() {
        parse_eq!(literal_parser, "12.9", Literal::Real(12.9));
        parse_eq!(literal_parser, "12", Literal::Real(12.0));
        parse_eq!(literal_parser, "true", Literal::Logical(Logical::True));
        parse_eq!(literal_parser, "UNKNOWN", Literal::Logical(Logical::Unknown));
        parse_eq!(literal_parser, "'hello world'", Literal::String("hello world".into()));
        parse_eq!(literal_parser, "\"F09F9881\"", Literal::String("😁".into()));
    }

    #[test]
    fn parses_literal_expressions() {
        parse_eq!(expr_parser, "12.9", Expr::Literal(Literal::Real(12.9)));
    }

    #[test]
    fn parses_unary_operations() {
        parse_eq!(
            expr_parser,
            "-12.9",
            Expr::UnaryOperation(UnaryOperation {
                op: UnaryOp::Minus,
                rhs: Box::new(Expr::Literal(Literal::Real(12.9)))
            })
        );
        parse_eq!(
            expr_parser,
            "not True",
            Expr::UnaryOperation(UnaryOperation {
                op: UnaryOp::Not,
                rhs: Box::new(Expr::Literal(Literal::Logical(Logical::True)))
            })
        );
    }

    #[test]
    fn parses_exp_binary_operation() {
        parse_eq!(
            expr_parser,
            "42**2**3",
            Expr::BinaryOperation(BinaryOperation {
                op: BinOp::Pow,
                lhs: Box::new(Expr::Literal(Literal::Real(42.0))),
                rhs: Box::new(Expr::BinaryOperation(BinaryOperation {
                    op: BinOp::Pow,
                    lhs: Box::new(Expr::Literal(Literal::Real(2.0))),
                    rhs: Box::new(Expr::Literal(Literal::Real(3.0)))
                }))
            })
        );
    }
}
