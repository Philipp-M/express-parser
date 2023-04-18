use std::fmt::Display;

use chumsky::{
    input::{Stream, ValueInput},
    prelude::*,
};
use logos::Logos;

use crate::lexer::Token::{self, *};

// TODO include spans for better error reporting
pub struct Ast(Vec<SchemaDecl>);

#[derive(Clone, Debug, PartialEq)]
pub struct SchemaDecl {
    id: String,
}

impl Display for SchemaDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SCHEMA {}; END_SCHEMA", self.id)
    }
}

impl Display for Ast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.iter().try_for_each(|s| write!(f, "{s}\n"))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Logical {
    True,
    False,
    Unknown,
}

impl Display for Logical {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            Self::True => "TRUE",
            Self::False => "FALSE",
            Self::Unknown => "UNKNOWN",
        })
    }
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

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Binary(binary) => write!(f, "%{binary:b}"),
            Literal::Logical(logical) => write!(f, "{logical}"),
            Literal::Real(real) => write!(f, "{real}"),
            Literal::String(s) => write!(f, "'{s}'"), // TODO encoded_string_literal?, this could produce incorrect code
        }
    }
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
impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            UnaryOp::Plus => "+",
            UnaryOp::Minus => "-",
            UnaryOp::Not => "NOT",
        })
    }
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

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            BinOp::Mul => "*",
            BinOp::RealDiv => "/",
            BinOp::IntegerDiv => "DIV",
            BinOp::Mod => "MOD",
            BinOp::And => "AND",
            BinOp::ComplexEntityInstanceConstruction => "||",
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Or => "OR",
            BinOp::Xor => "XOR",
            BinOp::Pow => "**",
            BinOp::Equal => "=",
            BinOp::NotEqual => "<>",
            BinOp::Less => "<",
            BinOp::Greater => ">",
            BinOp::LessEqual => "<=",
            BinOp::GreaterEqual => ">=",
            BinOp::InstanceEqual => ":=:",
            BinOp::InstanceNotEqual => ":<>:",
            BinOp::In => "IN",
            BinOp::Like => "LIKE",
        })
    }
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

impl Display for BuiltInConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            BuiltInConstant::Napier => "CONST_E",
            BuiltInConstant::Pi => "PI",
            BuiltInConstant::Self_ => "SELF",
            BuiltInConstant::Indeterminate => "?",
        })
    }
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

impl Display for BuiltInFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            BuiltInFunction::ABS => "ABS",
            BuiltInFunction::ACOS => "ACOS",
            BuiltInFunction::ASIN => "ASIN",
            BuiltInFunction::ATAN => "ATAN",
            BuiltInFunction::BLENGTH => "BLENGTH",
            BuiltInFunction::COS => "COS",
            BuiltInFunction::EXISTS => "EXISTS",
            BuiltInFunction::EXP => "EXP",
            BuiltInFunction::FORMAT => "FORMAT",
            BuiltInFunction::HIBOUND => "HIBOUND",
            BuiltInFunction::HIINDEX => "HIINDEX",
            BuiltInFunction::LENGTH => "LENGTH",
            BuiltInFunction::LOBOUND => "LOBOUND",
            BuiltInFunction::LOINDEX => "LOINDEX",
            BuiltInFunction::LOG => "LOG",
            BuiltInFunction::LOG2 => "LOG2",
            BuiltInFunction::LOG10 => "LOG10",
            BuiltInFunction::NVL => "NVL",
            BuiltInFunction::ODD => "ODD",
            BuiltInFunction::ROLESOF => "ROLESOF",
            BuiltInFunction::SIN => "SIN",
            BuiltInFunction::SIZEOF => "SIZEOF",
            BuiltInFunction::SQRT => "SQRT",
            BuiltInFunction::TAN => "TAN",
            BuiltInFunction::TYPEOF => "TYPEOF",
            BuiltInFunction::USEDIN => "USEDIN",
            BuiltInFunction::VALUE => "VALUE",
            BuiltInFunction::VALUE_IN => "VALUE_IN",
            BuiltInFunction::VALUE_UNIQUE => "VALUE_UNIQUE",
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum FunctionCallName {
    BuiltInFunction(BuiltInFunction),
    Reference(String),
}

impl Display for FunctionCallName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionCallName::BuiltInFunction(builtin) => write!(f, "{}", builtin),
            FunctionCallName::Reference(r) => write!(f, "{}", r),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionCall {
    name: FunctionCallName,
    args: Vec<Expr>,
}

impl Display for FunctionCall {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if !self.args.is_empty() {
            write!(f, "(")?;
        }
        let len = self.args.len();
        for (i, arg) in self.args.iter().enumerate() {
            if i == len - 1 {
                write!(f, "{})", arg)?;
            } else {
                write!(f, "{}, ", arg)?;
            }
        }
        Ok(())
    }
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

impl Display for Qualifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Qualifier::Attribute(id) => write!(f, ".{id}"),
            Qualifier::Group(id) => write!(f, "\\{id}"),
            Qualifier::Index(expr) => write!(f, "[{expr}]"),
            Qualifier::Range { begin, end } => write!(f, "[{begin}:{end}]"),
        }
    }
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

impl Display for QualifiableFactor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QualifiableFactor::Reference(r) => write!(f, "{r}"),
            QualifiableFactor::BuiltInConstant(c) => write!(f, "{c}"),
            QualifiableFactor::FunctionCall(fc) => write!(f, "{fc}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Qualifiable {
    qualifiable_factor: QualifiableFactor,
    qualifiers: Vec<Qualifier>,
}

impl Display for Qualifiable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.qualifiable_factor)?;
        self.qualifiers.iter().try_for_each(|q| write!(f, "{q}"))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct BinaryOperation {
    op: BinOp,
    lhs: Box<Expr>,
    rhs: Box<Expr>,
}

impl Display for BinaryOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO maybe don't always use parenthised expressions
        write!(f, "({} {} {})", self.lhs, self.op, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct UnaryOperation {
    op: UnaryOp,
    rhs: Box<Expr>,
}

impl Display for UnaryOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // TODO parenthises necessary anywhere?
        write!(f, "{} {}", self.op, self.rhs)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct AggregateInitializer {
    elements: Vec<Element>,
}

impl Display for AggregateInitializer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let len = self.elements.len();
        for (i, arg) in self.elements.iter().enumerate() {
            if i == len - 1 {
                write!(f, "{}", arg)?;
            } else {
                write!(f, "{}, ", arg)?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}

// TODO see below, likely ambiguous parsing with function_call
// TODO combine Display trait code with function_call
#[derive(Debug, Clone, PartialEq)]
pub struct EntityConstructor {
    entity_ref: String,
    args: Vec<Expr>,
}

impl Display for EntityConstructor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}(", self.entity_ref)?;
        let len = self.args.len();
        for (i, arg) in self.args.iter().enumerate() {
            if i == len - 1 {
                write!(f, "{}", arg)?;
            } else {
                write!(f, "{}, ", arg)?;
            }
        }
        write!(f, ")")
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Literal(Literal),
    Qualifiable(Qualifiable),
    BinaryOperation(BinaryOperation),
    UnaryOperation(UnaryOperation),
    AggregateInitializer(AggregateInitializer),
    EntityConstructor(EntityConstructor),
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Literal(l) => write!(f, "{l}"),
            Expr::Qualifiable(q) => write!(f, "{q}"),
            Expr::BinaryOperation(b) => write!(f, "{b}"),
            Expr::UnaryOperation(u) => write!(f, "{u}"),
            Expr::AggregateInitializer(a) => write!(f, "{a}"),
            Expr::EntityConstructor(e) => write!(f, "{e}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Element {
    pub expr: Expr,
    pub repetition: Option<Expr>,
}

impl Display for Element {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.repetition {
            Some(rep) => write!(f, "{}:{}", self.expr, rep),
            None => write!(f, "{}", self.expr),
        }
    }
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

// TODO add param to only allow simple_expr
// TODO unfortunately chumsky doesn't allow mutual recursion (simple_expr <-> expr)
// I'm not sure anyway if in e.g. a numeric expression the normal (relational) expression is allowed to be called (although the BNF defines it),
// in case only simple_expr is allowed, this could be solved with an extra parameter for this function that disables relational operators
// This could and likely will also be solved by validation either directly in the parser (.validate(..)) or in a later step
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

        let attribute_qualifier = just(DOT).ignore_then(select! { SIMPLE_ID(id) => Qualifier::Attribute(id.into()) });
        let group_qualifier = just(BACKSLASH).ignore_then(select! { SIMPLE_ID(id) => Qualifier::Group(id.into()) });
        let index_qualifier = expr
            .clone()
            .then_ignore(just(COLON))
            .then(expr.clone())
            .map(|(begin, end)| Qualifier::Range { begin, end }) // [<expr>:<expr>]
            .or(expr.clone().map(Qualifier::Index)) // [<expr>]
            .delimited_by(just(OPEN_BRACKET), just(CLOSE_BRACKET));
        let qualifiers = attribute_qualifier.or(group_qualifier).or(index_qualifier).repeated().collect().boxed();

        let actual_parameter_list =
            expr.clone().separated_by(just(COMMA)).collect().delimited_by(just(OPEN_PAREN), just(CLOSE_PAREN));
        // TODO parameter list seems to be optional, this would make parsing a little bit ambiguous (without parameters, it's just a Reference)
        let function_call = function_call_name
            .then(actual_parameter_list)
            .map(|(name, args)| QualifiableFactor::FunctionCall(FunctionCall { name, args }));

        let qualifiable_factor = function_call
            .or(select! {
                SIMPLE_ID(id) => QualifiableFactor::Reference(id.into()),
                CONST_E => QualifiableFactor::BuiltInConstant(BuiltInConstant::Napier),
                PI => QualifiableFactor::BuiltInConstant(BuiltInConstant::Pi),
                SELF => QualifiableFactor::BuiltInConstant(BuiltInConstant::Self_),
                WILD_CARD => QualifiableFactor::BuiltInConstant(BuiltInConstant::Indeterminate),
            })
            .then(qualifiers)
            .map(|(qualifiable_factor, qualifiers)| Expr::Qualifiable(Qualifiable { qualifiable_factor, qualifiers }));

        let element = expr
            .clone()
            .then(just(COLON).ignore_then(expr.clone()).or_not())
            .map(|(expr, repetition)| Element { expr, repetition });

        let primary = literal_parser().map(Expr::Literal).or(qualifiable_factor).boxed();

        let paren_expr = expr.clone().delimited_by(just(OPEN_PAREN), just(CLOSE_PAREN));

        let unary_op = select! {
            PLUS => UnaryOp::Plus,
            MINUS => UnaryOp::Minus,
            NOT => UnaryOp::Not,
        }
        .then(primary.clone().or(paren_expr.clone()))
        .map(|(op, arg)| Expr::UnaryOperation(UnaryOperation { op, rhs: Box::new(arg) }));

        let actual_parameter_list =
            expr.clone().separated_by(just(COMMA)).collect().delimited_by(just(OPEN_PAREN), just(CLOSE_PAREN));
        // TODO parameter list seems to be optional, this would make parsing a little bit ambiguous (without parameters, it's just a Reference)
        let entity_constructor = select! { SIMPLE_ID(id) => id.to_string()}
            .then(actual_parameter_list)
            .map(|(entity_ref, args)| Expr::EntityConstructor(EntityConstructor { entity_ref, args }));

        let aggregate_initializer = element
            .separated_by(just(COMMA))
            .collect()
            .delimited_by(just(OPEN_BRACKET), just(CLOSE_BRACKET))
            .map(|elements| Expr::AggregateInitializer(AggregateInitializer { elements }));

        // simple_factor in BNF
        // TODO BNF ambiguous? entity_constructor probably/likely clashes with function_call, does a semantic check later decide whether it's a function_call or an entity_constructor?
        // If that's the case, the function call should probably grouped together with the entity_constructor as something like a "callable reference"
        let atom = aggregate_initializer.or(entity_constructor).or(unary_op).or(paren_expr).or(primary); // TODO enumeration_reference | interval | query_expression

        // factor in BNF
        let pow = atom.clone().then_ignore(just(DOUBLE_STAR)).repeated().foldr(atom.clone(), |lhs, rhs| {
            Expr::BinaryOperation(BinaryOperation { op: BinOp::Pow, lhs: lhs.into(), rhs: rhs.into() })
        });

        let term = pow
            .clone()
            .foldl(
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
            )
            .boxed();

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
        .map(Ast)
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
            let token_iter = Token::lexer($src).spanned().map(|(tok, span)| (tok, span.into()));
            let token_stream = Stream::from_iter(token_iter).spanned(($src.len()..$src.len()).into());
            $parser.parse(token_stream).into_result().expect("Failed parsing")
        }};
    }

    macro_rules! parse_eq {
        ($parser:expr, $src:expr, $eq:expr) => {
            assert_eq!(parse!($parser, $src), $eq)
        };
    }

    macro_rules! parses {
        ($parser:expr, $src:expr, $eq:expr) => {
            assert_eq!(format!("{}", parse!($parser, $src)), $eq)
        };
        ($parser:expr, $src:expr) => {
            assert_eq!(format!("{}", parse!($parser, $src)), $src)
        };
    }

    #[test]
    fn parses_simple_schema() {
        parses!(parser(), "SCHEMA simple; END_SCHEMA\n");
    }

    #[test]
    fn parses_literals() {
        parses!(literal_parser(), "12.9");
        parses!(literal_parser(), "12");
        parses!(literal_parser(), "true", "TRUE");
        parses!(literal_parser(), "UNKNOWN");
        parses!(literal_parser(), "'hello world'");
        // TODO This should be encoded back into an encoded string literal instead of an UTF8 string
        parses!(literal_parser(), "\"F09F9881\"", "'😁'");
        parses!(literal_parser(), "\"F09F9881F09F9881\"", "'😁😁'");
    }

    #[test]
    fn parses_literal_expressions() {
        parses!(expr_parser(), "12.9");
    }

    #[test]
    fn parses_unary_operations() {
        parses!(expr_parser(), "- 12.9");
        parses!(expr_parser(), "not True", "NOT TRUE");
    }

    #[test]
    fn parses_binary_operations() {
        parses!(expr_parser(), "42**2**3", "(42 ** (2 ** 3))");
        parses!(expr_parser(), "12 - 42 * 42 ** 2 + 3", "((12 - (42 * (42 ** 2))) + 3)");
        parses!(expr_parser(), "12 or (42 * 42 ** 2 + 3)", "(12 OR ((42 * (42 ** 2)) + 3))");
        parses!(expr_parser(), "12 in 42 * 42 ** 2 + 3", "(12 IN ((42 * (42 ** 2)) + 3))");
    }

    #[test]
    fn parses_aggregate_initializer() {
        parses!(expr_parser(), "[12.9]");
        parses!(expr_parser(), "[12.9:1]");
        // parses!(expr_parser(), "[12.9:1,]"); // TODO allow this, not in BNF though?
        parses!(expr_parser(), "[12.9:1, 12]");
        parses!(expr_parser(), "[12.9:1, 122.9:1]");
    }

    #[test]
    fn parses_entity_constructor() {
        parses!(expr_parser(), "MyEntity()");
        parse_eq!(expr_parser(), "MyEntity()", Expr::EntityConstructor(EntityConstructor { entity_ref: "MyEntity".to_string(), args: vec![] }));

        parses!(expr_parser(), "IfcVectorDifference(V, XVec).Orientation");
    }

    #[test]
    fn parses_qualifiers() {
        parses!(expr_parser(), "arr[12.9:?]");
        parses!(expr_parser(), "arr[12.9:?].idx");
    }
}
