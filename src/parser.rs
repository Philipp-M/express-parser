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

    /* relational operators */
    /// `=`
    Equal,
    /// `<>`
    NotEqual,
    /// `<`
    Less,
    /// `>`
    Greater,
    /// `<=`
    LessEqual,
    /// `>=`
    GreaterEqual,
    /// `:=:`
    InstanceEqual,
    /// `:<>:`
    InstanceNotEqual,

    /* extended relational operators */
    /// `IN`
    In,
    /// `LIKE`
    Like,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BuiltInConstant {
    /// `CONST_E`, Napier's constant `e = 2.71828 …`
    Napier,
    /// The ratio of a circle's circumference to its diameter, `π = 3.14159 …`
    Pi,
    /// `SELF` is not a constant, but behaves as one in every context in which it can appear.
    Self_,
    /// The indeterminate symbol `?` stands for an ambiguous value.
    /// It is compatible with all data types.
    Indeterminate,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FunctionCallName {
    BuiltInFunction(BuiltInFunction),
    Reference(String),
}

#[allow(non_camel_case_types, clippy::upper_case_acronyms)] // to use original identifiers
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BuiltInFunction {
    ABS,
    ACOS,
    ASIN,
    ATAN,
    BLENGTH,
    COS,
    EXISTS,
    EXP,
    FORMAT,
    HIBOUND,
    HIINDEX,
    LENGTH,
    LOBOUND,
    LOINDEX,
    LOG,
    LOG2,
    LOG10,
    NVL,
    ODD,
    ROLESOF,
    SIN,
    SIZEOF,
    SQRT,
    TAN,
    TYPEOF,
    USEDIN,
    VALUE,
    VALUE_IN,
    VALUE_UNIQUE,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionCall {
    name: FunctionCallName,
    args: Vec<Expr>,
}

/// Output of [qualifier]
#[derive(Debug, Clone, PartialEq)]
pub enum Qualifier {
    /// Like `.x`
    Attribute(String),
    /// Like `\point`
    Group(String),
    /// Like `[1]`
    Index(Expr),
    /// Like `[1:3]`
    Range { begin: Expr, end: Expr },
}

#[derive(Debug, Clone, PartialEq)]
pub enum QualifiableFactor {
    /// [attribute_ref], [general_ref], [population], or [constant_ref]
    Reference(String),
    /// [built_in_constant]
    BuiltInConstant(BuiltInConstant),
    /// [function_call]
    FunctionCall(FunctionCall),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Qualifiable {
    qualifiable_factor: QualifiableFactor,
    qualifiers: Vec<Qualifier>,
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
    Qualifiable(Qualifiable),
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

macro_rules! qualifier {
    ($name:ident) => {
        
    };
}

// TODO add param to only allow simple_expr
// TODO unfortunately chumsky doesn't allow mutual recursion (simple_expr <-> expr)
// I'm not sure anyway if in e.g. a numeric expression the normal (relational) expression is allowed to be called,
// in case only simple_expr is allowed, this could be solved with an extra parameter for this function that disables relational operators
pub fn expr_parser<'src, I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>>(
) -> impl Parser<'src, I, Expr, extra::Err<Rich<'src, Token<'src>>>> + Clone {
    recursive(|expr| {
        macro_rules! function_call_name {
            (builtins: $($builtin_name:ident),+) => {
                select! {
                    $($builtin_name => FunctionCallName::BuiltInFunction(BuiltInFunction::$builtin_name)),+,
                    SIMPLE_ID(fn_name) => FunctionCallName::Reference(fn_name.into()),
                }
            };
        }
        let function_call_name = function_call_name!(builtins: ABS, ACOS, ASIN, ATAN, BLENGTH, COS, EXISTS, EXP,
                                                     FORMAT, HIBOUND, HIINDEX, LENGTH, LOBOUND, LOINDEX,
                                                     LOG, LOG2, LOG10, NVL, ODD, ROLESOF, SIN, SIZEOF, SQRT,
                                                     TAN, TYPEOF, USEDIN, VALUE, VALUE_IN, VALUE_UNIQUE);

        let qualifier = just(DOT).ignore_then(select! { SIMPLE_ID(id) => Qualifier::Attribute(id.into()) }).repeated().collect();
        let actual_parameter_list =
            expr.clone().separated_by(just(COMMA)).collect().delimited_by(just(OPEN_PAREN), just(CLOSE_PAREN));
        // TODO parameter list seems to be optional, this would makes parsing a little bit ambiguous (without parameters, it's just a Reference)
        let function_call = function_call_name
            .then(actual_parameter_list)
            .map(|(name, args)| QualifiableFactor::FunctionCall(FunctionCall { name, args }));
        // let qualifier = qualifier!();
        let qualifiable_factor = function_call
            .or(select! {
                SIMPLE_ID(id) => QualifiableFactor::Reference(id.into()),
                CONST_E => QualifiableFactor::BuiltInConstant(BuiltInConstant::Napier),
                PI => QualifiableFactor::BuiltInConstant(BuiltInConstant::Pi),
                SELF => QualifiableFactor::BuiltInConstant(BuiltInConstant::Self_),
                WILD_CARD => QualifiableFactor::BuiltInConstant(BuiltInConstant::Indeterminate),
            }).then(qualifier)
            // TODO qualifiers
            .map(|(qf, q)| Expr::Qualifiable(Qualifiable { qualifiable_factor: qf, qualifiers: q }));
        let primary = literal_parser().map(Expr::Literal).or(qualifiable_factor);

        let paren_expr = expr.delimited_by(just(OPEN_PAREN), just(CLOSE_PAREN));

        let unary_op = select! {
            PLUS => UnaryOp::Plus,
            MINUS => UnaryOp::Minus,
            NOT => UnaryOp::Not,
        }
        .then(primary.clone().or(paren_expr.clone()))
        .map(|(op, arg)| Expr::UnaryOperation(UnaryOperation { op, rhs: Box::new(arg) }));

        // simple_factor in bnf
        let atom = unary_op.or(primary).or(paren_expr); // TODO aggregate_initializer | entity_constructor | enumeration_reference | interval | query_expression

        // factor in bnf
        let pow = atom.clone().then_ignore(just(DOUBLE_STAR)).repeated().foldr(atom.clone(), |lhs, rhs| {
            Expr::BinaryOperation(BinaryOperation { op: BinOp::Pow, lhs: lhs.into(), rhs: rhs.into() })
        });

        let term = pow.clone().foldl(
            select! {
                STAR => BinOp::Mul,
                SLASH => BinOp::RealDiv,
                DIV => BinOp::IntegerDiv,
                MOD => BinOp::Mod,
                AND => BinOp::And,
                DOUBLE_PIPE => BinOp::Or,
            }
            .then(pow)
            .repeated(),
            |lhs, (op, rhs)| Expr::BinaryOperation(BinaryOperation { op, lhs: lhs.into(), rhs: rhs.into() }),
        );

        let simple_expr = term.clone().foldl(
            select! {
                PLUS => BinOp::Add,
                MINUS => BinOp::Sub,
                OR => BinOp::Or,
                XOR => BinOp::Xor,
            }
            .then(term)
            .repeated(),
            |lhs, (op, rhs)| Expr::BinaryOperation(BinaryOperation { op, lhs: lhs.into(), rhs: rhs.into() }),
        );

        let rel_expr = simple_expr
            .clone()
            .then(select! {
                LESS => BinOp::Less,
                GREATER => BinOp::Greater,
                LESS_EQUAL => BinOp::LessEqual,
                GREATER_EQUAL => BinOp::GreaterEqual,
                NOT_EQUAL => BinOp::NotEqual,
                EQUAL => BinOp::Equal,
                INSTANCE_NOT_EQUAL => BinOp::InstanceNotEqual,
                INSTANCE_EQUAL => BinOp::InstanceEqual,
                IN => BinOp::In,
                LIKE => BinOp::Like,
            })
            .then(simple_expr.clone())
            .map(|((lhs, op), rhs)| Expr::BinaryOperation(BinaryOperation { op, lhs: lhs.into(), rhs: rhs.into() }));
        rel_expr.or(simple_expr)
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
            $parser.parse(token_stream).into_result().unwrap()
        }};
    }

    macro_rules! parse_eq {
        ($parser:expr, $src:expr, $eq:expr) => {
            assert_eq!(parse!($parser, $src), $eq)
        };
    }

    macro_rules! unary_op {
        (+) => { UnaryOp::Plus };
        (-) => { UnaryOp::Minus };
        (!) => { UnaryOp::Not };
    }

    macro_rules! unary_expr {
        ($op:tt $rhs:tt) => {
            Expr::UnaryOperation(UnaryOperation { op: unary_op!($op), rhs: Box::new(expr!{$rhs}) })
        };
    }

    macro_rules! binary_op {
        (+) => { BinOp::Add };
        (-) => { BinOp::Sub };
        (or) => { BinOp::Or };
        (xor) => { BinOp::Xor };
        (*) => { BinOp::Mul };
        ((**)) => { BinOp::Pow };
        (/) => { BinOp::RealDiv };
        (div) => { BinOp::IntegerDiv };
        (%) => { BinOp::Mod };
        (and) => { BinOp::And };
        ((||)) => { BinOp::ComplexEntityInstanceConstruction };
        (=) => { BinOp::Equal };
        (=) => { BinOp::Equal };
        ((<>)) => { BinOp::NotEqual };
        (<) => { BinOp::Less };
        (>) => { BinOp::Greater };
        ((<=)) => { BinOp::LessEqual };
        ((>=)) => { BinOp::GreaterEqual };
        ((:=:)) => { BinOp::InstanceEqual };
        ((:<>:)) => { BinOp::InstanceNotEqual };
        (in) => { BinOp::In };
        (like) => { BinOp::Like };
    }

    macro_rules! binary_expr {
        ($lhs:tt $op:tt $rhs:tt) => {
            Expr::BinaryOperation(BinaryOperation { op: binary_op!($op), lhs: Box::new(expr!{$lhs}), rhs: Box::new(expr!{$rhs}) })
        };
    }

    macro_rules! expr {
        // literals
        {(r $lit:literal)} => { Expr::Literal(Literal::Real($lit)) };
        {(l $lit:ident)} => { Expr::Literal(Literal::Logical(Logical::$lit)) };
        {(b $lit:literal)} => { Expr::Literal(Literal::Binary($lit)) };
        // unary expr
        {($op:tt $rhs:tt)} => { unary_expr!($op $rhs) };
        // binary expr
        {($lhs:tt $op:tt $rhs:tt)} => { binary_expr!($lhs $op $rhs) };
    }

    #[test]
    fn parses_simple_schema() {
        parse_eq!(parser(), "SCHEMA simple; END_SCHEMA", vec![SchemaDecl { id: "simple".to_owned() }]);
    }

    #[test]
    fn parses_literals() {
        parse_eq!(literal_parser(), "12.9", Literal::Real(12.9));
        parse_eq!(literal_parser(), "12", Literal::Real(12.0));
        parse_eq!(literal_parser(), "true", Literal::Logical(Logical::True));
        parse_eq!(literal_parser(), "UNKNOWN", Literal::Logical(Logical::Unknown));
        parse_eq!(literal_parser(), "'hello world'", Literal::String("hello world".into()));
        parse_eq!(literal_parser(), "\"F09F9881\"", Literal::String("😁".into()));
        parse_eq!(literal_parser(), "\"F09F9881F09F9881\"", Literal::String("😁😁".into()));
    }

    #[test]
    fn parses_literal_expressions() {
        parse_eq!(expr_parser(), "12.9", expr! {(r 12.9)});
    }

    #[test]
    fn parses_unary_operations() {
        parse_eq!(expr_parser(), "-12.9", expr! {(-(r 12.9))});
        parse_eq!(expr_parser(), "not True", expr! {(!(l True))});
    }

    #[test]
    fn parses_binary_operations() {
        parse_eq!(expr_parser(), "42**2**3", expr! {((r 42.0)(**)((r 2.0)(**)(r 3.0)))});
        parse_eq!(
            expr_parser(),
            "12 - 42 * 42 ** 2 + 3",
            expr! {(((r 12.0) - ((r 42.0) * ((r 42.0)(**)(r 2.0)))) + (r 3.0))}
        );
        parse_eq!(
            expr_parser(),
            "12 or (42 * 42 ** 2 + 3)",
            expr! {((r 12.0) or (((r 42.0) * ((r 42.0)(**)(r 2.0))) + (r 3.0)))}
        );
        parse_eq!(
            expr_parser(),
            "12 in 42 * 42 ** 2 + 3",
            expr! {((r 12.0) in (((r 42.0) * ((r 42.0)(**)(r 2.0))) + (r 3.0)))}
        );
    }
}
