use logos::Logos;

#[allow(non_camel_case_types)]
#[derive(Logos, Clone, Debug, PartialEq)]
pub enum Token<'src> {
    // KEYWORDS
    #[regex(r"(?i)ABS")]
    ABS,
    #[regex(r"(?i)ABSTRACT")]
    ABSTRACT,
    #[regex(r"(?i)ACOS")]
    ACOS,
    #[regex(r"(?i)AGGREGATE")]
    AGGREGATE,
    #[regex(r"(?i)ALIAS")]
    ALIAS,
    #[regex(r"(?i)AND")]
    AND,
    #[regex(r"(?i)ANDOR")]
    ANDOR,
    #[regex(r"(?i)ARRAY")]
    ARRAY,
    #[regex(r"(?i)AS")]
    AS,
    #[regex(r"(?i)ASIN")]
    ASIN,
    #[regex(r"(?i)ATAN")]
    ATAN,
    #[regex(r"(?i)BAG")]
    BAG,
    #[regex(r"(?i)BASED_ON")]
    BASED_ON,
    #[regex(r"(?i)BEGIN")]
    BEGIN,
    #[regex(r"(?i)BINARY")]
    BINARY,
    #[regex(r"(?i)BLENGTH")]
    BLENGTH,
    #[regex(r"(?i)BOOLEAN")]
    BOOLEAN,
    #[regex(r"(?i)BY")]
    BY,
    #[regex(r"(?i)CASE")]
    CASE,
    #[regex(r"(?i)CONSTANT")]
    CONSTANT,
    #[regex(r"(?i)CONST_E")]
    CONST_E,
    #[regex(r"(?i)COS")]
    COS,
    #[regex(r"(?i)DERIVE")]
    DERIVE,
    #[regex(r"(?i)DIV")]
    DIV,
    #[regex(r"(?i)ELSE")]
    ELSE,
    #[regex(r"(?i)END")]
    END,
    #[regex(r"(?i)END_ALIAS")]
    END_ALIAS,
    #[regex(r"(?i)END_CASE")]
    END_CASE,
    #[regex(r"(?i)END_CONSTANT")]
    END_CONSTANT,
    #[regex(r"(?i)END_ENTITY")]
    END_ENTITY,
    #[regex(r"(?i)END_FUNCTION")]
    END_FUNCTION,
    #[regex(r"(?i)END_IF")]
    END_IF,
    #[regex(r"(?i)END_LOCAL")]
    END_LOCAL,
    #[regex(r"(?i)END_PROCEDURE")]
    END_PROCEDURE,
    #[regex(r"(?i)END_REPEAT")]
    END_REPEAT,
    #[regex(r"(?i)END_RULE")]
    END_RULE,
    #[regex(r"(?i)END_SCHEMA")]
    END_SCHEMA,
    #[regex(r"(?i)END_SUBTYPE_CONSTRAINT")]
    END_SUBTYPE_CONSTRAINT,
    #[regex(r"(?i)END_TYPE")]
    END_TYPE,
    #[regex(r"(?i)ENTITY")]
    ENTITY,
    #[regex(r"(?i)ENUMERATION")]
    ENUMERATION,
    #[regex(r"(?i)ESCAPE")]
    ESCAPE,
    #[regex(r"(?i)EXISTS")]
    EXISTS,
    #[regex(r"(?i)EXTENSIBLE")]
    EXTENSIBLE,
    #[regex(r"(?i)EXP")]
    EXP,
    #[regex(r"(?i)FALSE")]
    FALSE,
    #[regex(r"(?i)FIXED")]
    FIXED,
    #[regex(r"(?i)FOR")]
    FOR,
    #[regex(r"(?i)FORMAT")]
    FORMAT,
    #[regex(r"(?i)FROM")]
    FROM,
    #[regex(r"(?i)FUNCTION")]
    FUNCTION,
    #[regex(r"(?i)GENERIC")]
    GENERIC,
    #[regex(r"(?i)GENERIC_ENTITY")]
    GENERIC_ENTITY,
    #[regex(r"(?i)HIBOUND")]
    HIBOUND,
    #[regex(r"(?i)HIINDEX")]
    HIINDEX,
    #[regex(r"(?i)IF")]
    IF,
    #[regex(r"(?i)IN")]
    IN,
    #[regex(r"(?i)INSERT")]
    INSERT,
    #[regex(r"(?i)INTEGER")]
    INTEGER,
    #[regex(r"(?i)INVERSE")]
    INVERSE,
    #[regex(r"(?i)LENGTH")]
    LENGTH,
    #[regex(r"(?i)LIKE")]
    LIKE,
    #[regex(r"(?i)LIST")]
    LIST,
    #[regex(r"(?i)LOBOUND")]
    LOBOUND,
    #[regex(r"(?i)LOCAL")]
    LOCAL,
    #[regex(r"(?i)LOG")]
    LOG,
    #[regex(r"(?i)LOG10")]
    LOG10,
    #[regex(r"(?i)LOG2")]
    LOG2,
    #[regex(r"(?i)LOGICAL")]
    LOGICAL,
    #[regex(r"(?i)LOINDEX")]
    LOINDEX,
    #[regex(r"(?i)MOD")]
    MOD,
    #[regex(r"(?i)NOT")]
    NOT,
    #[regex(r"(?i)NUMBER")]
    NUMBER,
    #[regex(r"(?i)NVL")]
    NVL,
    #[regex(r"(?i)ODD")]
    ODD,
    #[regex(r"(?i)OF")]
    OF,
    #[regex(r"(?i)ONEOF")]
    ONEOF,
    #[regex(r"(?i)OPTIONAL")]
    OPTIONAL,
    #[regex(r"(?i)OR")]
    OR,
    #[regex(r"(?i)OTHERWISE")]
    OTHERWISE,
    #[regex(r"(?i)PI")]
    PI,
    #[regex(r"(?i)PROCEDURE")]
    PROCEDURE,
    #[regex(r"(?i)QUERY")]
    QUERY,
    #[regex(r"(?i)REAL")]
    REAL,
    #[regex(r"(?i)REFERENCE")]
    REFERENCE,
    #[regex(r"(?i)REMOVE")]
    REMOVE,
    #[regex(r"(?i)RENAMED")]
    RENAMED,
    #[regex(r"(?i)REPEAT")]
    REPEAT,
    #[regex(r"(?i)RETURN")]
    RETURN,
    #[regex(r"(?i)ROLESOF")]
    ROLESOF,
    #[regex(r"(?i)RULE")]
    RULE,
    #[regex(r"(?i)SCHEMA")]
    SCHEMA,
    #[regex(r"(?i)SELECT")]
    SELECT,
    #[regex(r"(?i)SELF")]
    SELF,
    #[regex(r"(?i)SET")]
    SET,
    #[regex(r"(?i)SIN")]
    SIN,
    #[regex(r"(?i)SIZEOF")]
    SIZEOF,
    #[regex(r"(?i)SKIP")]
    SKIP,
    #[regex(r"(?i)SQRT")]
    SQRT,
    #[regex(r"(?i)STRING")]
    STRING,
    #[regex(r"(?i)SUBTYPE")]
    SUBTYPE,
    #[regex(r"(?i)SUBTYPE_CONSTRAINT")]
    SUBTYPE_CONSTRAINT,
    #[regex(r"(?i)SUPERTYPE")]
    SUPERTYPE,
    #[regex(r"(?i)TAN")]
    TAN,
    #[regex(r"(?i)THEN")]
    THEN,
    #[regex(r"(?i)TO")]
    TO,
    #[regex(r"(?i)TOTAL_OVER")]
    TOTAL_OVER,
    #[regex(r"(?i)TRUE")]
    TRUE,
    #[regex(r"(?i)TYPE")]
    TYPE,
    #[regex(r"(?i)TYPEOF")]
    TYPEOF,
    #[regex(r"(?i)UNIQUE")]
    UNIQUE,
    #[regex(r"(?i)UNKNOWN")]
    UNKNOWN,
    #[regex(r"(?i)UNTIL")]
    UNTIL,
    #[regex(r"(?i)USE")]
    USE,
    #[regex(r"(?i)USEDIN")]
    USEDIN,
    #[regex(r"(?i)VALUE")]
    VALUE,
    #[regex(r"(?i)VALUE_IN")]
    VALUE_IN,
    #[regex(r"(?i)VALUE_UNIQUE")]
    VALUE_UNIQUE,
    #[regex(r"(?i)VAR")]
    VAR,
    #[regex(r"(?i)WHERE")]
    WHERE,
    #[regex(r"(?i)WHILE")]
    WHILE,
    #[regex(r"(?i)WITH")]
    WITH,
    #[regex(r"(?i)XOR")]
    XOR,

    // LITERALS

    // TODO think about directly assigning the value

    // unfortunately something like "[0-9abcdef]{8}" is not supported (yet)
    #[regex(r"%[0-1]+")]
    BINARY_LITERAL(&'src str),
    #[regex(r"[0-9]+")]
    INTEGER_LITERAL(&'src str),
    #[regex(r"[0-9]+\.[0-9]*([eE][+-]?[0-9]+)?")]
    FLOAT_LITERAL(&'src str),
    // TODO test this thoroughly, it isn't exactly what the BNF says, but stepcode does the same...
    // probably adjust this at some point to represent the real BNF
    #[regex(r"'([^'\n]|'')*'")]
    SIMPLE_STRING_LITERAL,
    // unfortunately something like "[0-9abcdef]{8}" is not supported (yet)
    #[regex(r#""[0-9abcdef][0-9abcdef][0-9abcdef][0-9abcdef][0-9abcdef][0-9abcdef][0-9abcdef][0-9abcdef]""#)]
    ENCODED_STRING_LITERAL,

    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*")]
    SIMPLE_ID(&'src str),

    #[token("(*")]
    EMBEDDED_REMARK_START,
    #[token("*)")]
    EMBEDDED_REMARK_END,

    // PUNCTUATION
    #[token(",")]
    COMMA,
    #[token(".")]
    DOT,
    #[token(";")]
    SEMICOLON,
    #[token(":")]
    COLON,

    // PARENTHESES/BRACKETS/BRACES
    #[token("(")]
    OPEN_PAREN,
    #[token(")")]
    CLOSE_PAREN,
    #[token("[")]
    OPEN_BRACKET,
    #[token("]")]
    CLOSE_BRACKET,
    #[token("{")]
    OPEN_BRACE,
    #[token("}")]
    CLOSE_BRACE,

    // OPERATORS
    #[token(":=")]
    ASSIGNMENT,
    #[token("<")]
    LESS,
    #[token(">")]
    GREATER,
    #[token("<=")]
    LESS_EQUAL,
    #[token(">=")]
    GREATER_EQUAL,
    #[token("<>")]
    NOT_EQUAL,
    #[token("=")]
    EQUAL,
    #[token(":=:")]
    INSTANCE_EQUAL,
    #[token(":<>:")]
    INSTANCE_NOT_EQUAL,
    #[token("+")]
    PLUS,
    #[token("-")]
    MINUS,
    #[token("||")]
    DOUBLE_PIPE,
    #[token("*")]
    STAR,
    #[token("/")]
    SLASH,

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    ERROR,
}

pub fn lex(input: &str) -> Vec<Token> {
    Token::lexer(input).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use Token::*;

    #[test]
    fn parses_case_insensitive_keywords() {
        assert_eq!(lex("SCHEMA"), vec![SCHEMA]);
        assert_eq!(lex("use"), vec![USE]);
        assert_eq!(lex("wHilE"), vec![WHILE]);
    }

    #[test]
    fn parses_number_literals() {
        assert_eq!(lex("12"), vec![INTEGER_LITERAL("12")]);
        assert_eq!(lex("12."), vec![FLOAT_LITERAL("12.")]);
        assert_eq!(lex("12.E8"), vec![FLOAT_LITERAL("12.E8")]);
        assert_eq!(lex("34.E-8"), vec![FLOAT_LITERAL("34.E-8")]);
        assert_eq!(lex("56.7"), vec![FLOAT_LITERAL("56.7")]);
        assert_eq!(lex("89.1e+0"), vec![FLOAT_LITERAL("89.1e+0")]);
    }

    #[test]
    fn parses_string_literals() {
        assert_eq!(lex("''"), vec![SIMPLE_STRING_LITERAL]);
        assert_eq!(lex("''''"), vec![SIMPLE_STRING_LITERAL]);
        assert_eq!(lex("'''''"), vec![ERROR]);
        assert_eq!(lex("'\n'"), vec![ERROR, ERROR]);
        assert!(lex("\"12\"").contains(&ERROR));
        assert_eq!(lex("\"12fa2a8f\""), vec![ENCODED_STRING_LITERAL]);
    }

    #[test]
    fn parses_binary_literals() {
        assert_eq!(lex("%1"), vec![BINARY_LITERAL("%1")]);
        assert_eq!(lex("%0"), vec![BINARY_LITERAL("%0")]);
        assert_eq!(lex("%1111"), vec![BINARY_LITERAL("%1111")]);
        assert_eq!(lex("%1101"), vec![BINARY_LITERAL("%1101")]);
        assert!(lex("%210").contains(&ERROR));
    }

    #[test]
    fn parses_simple_id() {
        assert_eq!(lex("i"), vec![SIMPLE_ID("i")]);
        assert_eq!(lex("hello123"), vec![SIMPLE_ID("hello123")]);
        assert_eq!(lex("hello_world12"), vec![SIMPLE_ID("hello_world12")]);
    }

    #[test]
    fn parses_operators() {
        assert_eq!(lex(":="), vec![ASSIGNMENT]);
        assert_eq!(lex("<"), vec![LESS]);
        assert_eq!(lex(">"), vec![GREATER]);
        assert_eq!(lex("<="), vec![LESS_EQUAL]);
        assert_eq!(lex(">="), vec![GREATER_EQUAL]);
        assert_eq!(lex("<>"), vec![NOT_EQUAL]);
        assert_eq!(lex("="), vec![EQUAL]);
        assert_eq!(lex(":=:"), vec![INSTANCE_EQUAL]);
        assert_eq!(lex(":<>:"), vec![INSTANCE_NOT_EQUAL]);
        assert_eq!(lex("+"), vec![PLUS]);
        assert_eq!(lex("-"), vec![MINUS]);
        assert_eq!(lex("||"), vec![DOUBLE_PIPE]);
        assert_eq!(lex("*"), vec![STAR]);
        assert_eq!(lex("/"), vec![SLASH]);
    }
}
