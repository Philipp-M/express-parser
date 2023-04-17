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
    #[regex(r"%[0-1]+", |lex| usize::from_str_radix(&lex.slice()[1..], 2).ok())]
    BINARY_LITERAL(usize),
    #[regex(r"[0-9]+", |lex| lex.slice().parse().ok())]
    INTEGER_LITERAL(f64),
    #[regex(r"[0-9]+\.[0-9]*([eE][+-]?[0-9]+)?", |lex| lex.slice().parse().ok())]
    FLOAT_LITERAL(f64),
    // TODO test this thoroughly, it isn't exactly what the BNF says, but stepcode does the same...
    // probably adjust this at some point to represent the real BNF
    #[regex(r"'([^'\n]|'')*'", |lex| Some(&lex.slice()[1..(lex.slice().len()-1)]))]
    SIMPLE_STRING_LITERAL(&'src str),
    // unfortunately something like "[0-9abcdef]{8}" is not supported (yet)
    #[regex(r#""([0-9abcdefABCDEF][0-9abcdefABCDEF][0-9abcdefABCDEF][0-9abcdefABCDEF][0-9abcdefABCDEF][0-9abcdefABCDEF][0-9abcdefABCDEF][0-9abcdefABCDEF])+""#, |lex| Some(&lex.slice()[1..(lex.slice().len()-1)]))]
    ENCODED_STRING_LITERAL(&'src str),

    #[regex(r"[a-zA-Z][a-zA-Z0-9_]*")]
    SIMPLE_ID(&'src str),

    #[regex(r"\(\*", parse_embedded_remark)]
    EMBEDDED_REMARK(Remark<'src>),
    #[regex("--", parse_tail_remark)]
    TAIL_REMARK(Remark<'src>),

    // PUNCTUATION
    #[token(",")]
    COMMA,
    #[token(".")]
    DOT,
    #[token(";")]
    SEMICOLON,
    #[token(":")]
    COLON,
    #[token("?")]
    WILD_CARD,
    #[token("\\")]
    BACKSLASH,

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
    #[token("<*")]
    AGGREGATION,
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
    #[token("|")]
    PIPE,
    #[token("*")]
    STAR,
    #[token("**")]
    DOUBLE_STAR,
    #[token("/")]
    SLASH,

    #[error]
    #[regex(r"[ \t\r\n\f]+", logos::skip)]
    ERROR,
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct Remark<'a> {
    tag: Option<&'a str>,
    remark: &'a str,
}

fn parse_remark_tag<'a>(lexer: &mut logos::Lexer<'a, Token<'a>>) -> Option<&'a str> {
    if lexer.remainder().starts_with('"') {
        let remaining = lexer.remainder();
        let mut in_simple_id = false;
        let mut requires_simple_id = false;
        for (i, c) in remaining[1..].chars().enumerate() {
            match c {
                '_' | 'a'..='z' | 'A'..='Z' | '0'..='9' if in_simple_id => continue,
                'a'..='z' | 'A'..='Z' => {
                    in_simple_id = true;
                }
                '.' => {
                    requires_simple_id = true;
                }
                '"' => {
                    if requires_simple_id || i == 0 {
                        return None;
                    } else {
                        lexer.bump(i + 2); // includes quotes at the beginning
                        return Some(&remaining[1..=i]);
                    }
                }
                _ => return None,
            }
        }
    }
    None
}

// TODO are whitespaces allowed between the (* and the tag?
fn parse_embedded_remark<'a>(lexer: &mut logos::Lexer<'a, Token<'a>>) -> Option<Remark<'a>> {
    let mut embedded_remarks = 1;
    let tag = parse_remark_tag(lexer);
    let remainder = lexer.remainder();
    let mut remark_length = 0;
    loop {
        match lexer.remainder().as_bytes() {
            [b'*', b')', ..] => {
                lexer.bump(2);
                embedded_remarks -= 1;
                if embedded_remarks == 0 {
                    return Some(Remark { tag, remark: &remainder[..remark_length] });
                }
                remark_length += 2;
            }
            [b'(', b'*', ..] => {
                lexer.bump(2);
                embedded_remarks += 1;
                remark_length += 2;
            }
            [] => return None,
            _ => {
                lexer.bump(1);
                remark_length += 1;
            }
        }
    }
}

// TODO are whitespaces allowed between the -- and the tag?
fn parse_tail_remark<'a>(lexer: &mut logos::Lexer<'a, Token<'a>>) -> Option<Remark<'a>> {
    let tag = parse_remark_tag(lexer);
    let mut char_count = 0;
    let remainder = lexer.remainder();
    for c in remainder.chars() {
        if matches!(c, '\n' | '\r') {
            break;
        }
        char_count += 1;
    }
    lexer.bump(char_count);
    Some(Remark { tag, remark: &remainder[..char_count] })
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
        assert_eq!(lex("12"), vec![INTEGER_LITERAL(12.0)]);
        assert_eq!(lex("12."), vec![FLOAT_LITERAL(12.0)]);
        assert_eq!(lex("12.E8"), vec![FLOAT_LITERAL(12.0e8)]);
        assert_eq!(lex("34.E-8"), vec![FLOAT_LITERAL(34.0E-8)]);
        assert_eq!(lex("56.7"), vec![FLOAT_LITERAL(56.7)]);
        assert_eq!(lex("89.1e+0"), vec![FLOAT_LITERAL(89.1e+0)]);
    }

    #[test]
    fn parses_string_literals() {
        assert_eq!(lex("''"), vec![SIMPLE_STRING_LITERAL("")]);
        // TODO should this be ' instead of ''?
        assert_eq!(lex("''''"), vec![SIMPLE_STRING_LITERAL("''")]);
        assert_eq!(lex("'Hello World'"), vec![SIMPLE_STRING_LITERAL("Hello World")]);
        assert_eq!(lex("'''''"), vec![ERROR]);
        assert_eq!(lex("'\n'"), vec![ERROR, ERROR]);
        assert!(lex("\"12\"").contains(&ERROR));
        assert_eq!(lex("\"F09F9881\""), vec![ENCODED_STRING_LITERAL("F09F9881")]);
        assert_eq!(lex("\"F09e9881\""), vec![ENCODED_STRING_LITERAL("F09e9881")]);
    }

    #[test]
    fn parses_binary_literals() {
        assert_eq!(lex("%1"), vec![BINARY_LITERAL(1)]);
        assert_eq!(lex("%0"), vec![BINARY_LITERAL(0)]);
        assert_eq!(lex("%1111"), vec![BINARY_LITERAL(15)]);
        assert_eq!(lex("%1101"), vec![BINARY_LITERAL(13)]);
        assert!(lex("%210").contains(&ERROR));
    }

    #[test]
    fn parses_simple_id() {
        assert_eq!(lex("i"), vec![SIMPLE_ID("i")]);
        assert_eq!(lex("hello123"), vec![SIMPLE_ID("hello123")]);
        assert_eq!(lex("hello_world12"), vec![SIMPLE_ID("hello_world12")]);
        assert_eq!(lex("TrueNorth"), vec![SIMPLE_ID("TrueNorth")]);
    }

    #[test]
    fn parses_embedded_remarks() {
        assert_eq!(lex("(**)"), vec![EMBEDDED_REMARK(Default::default())]);
        assert_eq!(lex("(**) UNKNOWN"), vec![EMBEDDED_REMARK(Default::default()), UNKNOWN]);
        assert_eq!(lex("(* remark *)"), vec![EMBEDDED_REMARK(Remark { tag: None, remark: " remark " })]);
        assert_eq!(lex("(* remark *) TRUE"), vec![EMBEDDED_REMARK(Remark { tag: None, remark: " remark " }), TRUE]);
        assert_eq!(
            lex("(* embedded (* remark *) *)"),
            vec![EMBEDDED_REMARK(Remark { tag: None, remark: " embedded (* remark *) " })]
        );
        assert_eq!(
            lex("(* embedded (* remark *) another (* remark that embeds (* another remark *) *) *)"),
            vec![EMBEDDED_REMARK(Remark {
                tag: None,
                remark: " embedded (* remark *) another (* remark that embeds (* another remark *) *) "
            })]
        );
        assert_eq!(
            lex(r#"(*"tag"*) UNKNOWN"#),
            vec![EMBEDDED_REMARK(Remark { tag: Some("tag"), remark: "" }), UNKNOWN]
        );
    }

    #[test]
    fn parses_tail_remarks() {
        assert_eq!(lex("-- remark"), vec![TAIL_REMARK(Remark { tag: None, remark: " remark" })]);
        assert_eq!(
            lex("--\"remark\" hello\n\r TRUE"),
            vec![TAIL_REMARK(Remark { tag: Some("remark"), remark: " hello" }), TRUE]
        );
        assert_eq!(
            lex("--\"remark\" hello\r\n TRUE"),
            vec![TAIL_REMARK(Remark { tag: Some("remark"), remark: " hello" }), TRUE]
        );
        assert_eq!(
            lex("--\"remark\" hello\n\n\n\r TRUE"),
            vec![TAIL_REMARK(Remark { tag: Some("remark"), remark: " hello" }), TRUE]
        );
        assert_eq!(
            lex("--\"remark\" hello\r\r\r\n\n TRUE"),
            vec![TAIL_REMARK(Remark { tag: Some("remark"), remark: " hello" }), TRUE]
        );
        assert_eq!(lex("--"), vec![TAIL_REMARK(Remark { tag: None, remark: "" })]);
        assert_eq!(lex("--\n\r"), vec![TAIL_REMARK(Remark { tag: None, remark: "" })]);
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
        assert_eq!(lex("**"), vec![DOUBLE_STAR]);
        assert_eq!(lex("/"), vec![SLASH]);
    }

    #[test]
    fn parses_ifc_schema_without_errors() -> std::io::Result<()> {
        let input = std::fs::read_to_string("./IFC.exp")?;
        // eprintln!("{:#?}", Token::lexer(&input).collect::<Vec<_>>());
        assert!(!Token::lexer(&input).any(|t| t == ERROR));
        Ok(())
    }
}
