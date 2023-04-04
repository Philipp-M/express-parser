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
pub enum LogicalLiteral {
    TRUE,
    FALSE,
    UNKNOWN,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    Binary(usize),
    Logical(LogicalLiteral),
    // TODO differentiate between float and integers?
    Real(f64),
    // TODO differentiate between encoded and simple string?
    String(String),
}

pub fn literal_parser<'src, I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>>(
) -> impl Parser<'src, I, Literal, extra::Err<Rich<'src, Token<'src>>>> {
    select! {
        BINARY_LITERAL(num) => Literal::Binary(num),
        INTEGER_LITERAL(num) => Literal::Real(num),
        FLOAT_LITERAL(num) => Literal::Real(num),
        SIMPLE_STRING_LITERAL(str) => Literal::String(str.into()),
        TRUE => Literal::Logical(LogicalLiteral::TRUE),
        FALSE => Literal::Logical(LogicalLiteral::FALSE),
        UNKNOWN => Literal::Logical(LogicalLiteral::UNKNOWN),
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
        parse_eq!(literal_parser, "true", Literal::Logical(LogicalLiteral::TRUE));
        parse_eq!(literal_parser, "UNKNOWN", Literal::Logical(LogicalLiteral::UNKNOWN));
        parse_eq!(literal_parser, "'hello world'", Literal::String("hello world".into()));
        parse_eq!(literal_parser, "\"F09F9881\"", Literal::String("😁".into()));
    }
}
