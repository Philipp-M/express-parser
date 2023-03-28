use chumsky::{
    input::{Stream, ValueInput},
    prelude::*,
};
use logos::Logos;

use crate::lexer::Token::{self, *};

#[derive(Clone, Debug, PartialEq)]
pub struct Ast {
    pub schemas: Vec<SchemaDecl>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SchemaDecl {
    id: String,
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
        .map(|schemas| Ast { schemas })
}

pub fn parse(src: &str) -> Ast {
    let token_iter = Token::lexer(src)
        .spanned()
        .map(|(tok, span)| (tok, span.into()));
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

    #[test]
    fn parses_simple_schema() {
        assert_eq!(
            parse("SCHEMA simple; END_SCHEMA"),
            Ast {
                schemas: vec![SchemaDecl {
                    id: "simple".to_owned()
                }]
            }
        );
    }
}
