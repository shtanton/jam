use lazy_static::lazy_static;
use regex::Regex;

#[derive(Debug, PartialEq)]
pub enum Token {
    Let,
    Fn,
    Import,
    Struct,
    Type,
    Identifier(String),
    IntegerLiteral(i64),
    StringLiteral(String),
    OpenBracket,
    CloseBracket,
    OpenSquare,
    CloseSquare,
}

impl Token {
    fn get_next_token(input: &str) -> Result<(Option<Token>, usize), String> {
        lazy_static! {
            static ref LET_PATTERN: Regex = Regex::new(r"^let($|[\s\)\]])").unwrap();
            static ref FN_PATTERN: Regex = Regex::new(r"^fn($|[\s\)\]])").unwrap();
            static ref IMPORT_PATTERN: Regex = Regex::new(r"^import($|[\s\)\]])").unwrap();
            static ref STRUCT_PATTERN: Regex = Regex::new(r"^struct($|[\s\)\]])").unwrap();
            static ref TYPE_PATTERN: Regex = Regex::new(r"^type($[\s\)\]])").unwrap();
            static ref IDENTIFIER_PATTERN: Regex =
                Regex::new(r"^([A-Za-z_+-/*='][A-Za-z0-9_+-/*=']*)").unwrap();
            static ref INTEGER_LITERAL_PATTERN: Regex =
                Regex::new(r"^(-?\d+)($|[\s\)\]])").unwrap();
            static ref STRING_LITERAL_PATTERN: Regex =
                Regex::new(r#"^"([^"]*)"($|[\s\)\]])"#).unwrap();
            static ref OPEN_BRACKET_PATTERN: Regex = Regex::new(r"^\(").unwrap();
            static ref CLOSE_BRACKET_PATTERN: Regex = Regex::new(r"^\)($|[\s\)\]])").unwrap();
            static ref OPEN_SQUARE_PATTERN: Regex = Regex::new(r"^\[").unwrap();
            static ref CLOSE_SQUARE_PATTERN: Regex = Regex::new(r"^\]($|[\s\)\]])").unwrap();
            static ref WHITESPACE_PATTERN: Regex = Regex::new(r"^\s+").unwrap();
        }
        if LET_PATTERN.is_match(input) {
            Ok((Some(Token::Let), 3))
        } else if FN_PATTERN.is_match(input) {
            Ok((Some(Token::Fn), 2))
        } else if IMPORT_PATTERN.is_match(input) {
            Ok((Some(Token::Import), 6))
        } else if STRUCT_PATTERN.is_match(input) {
            Ok((Some(Token::Struct), 6))
        } else if TYPE_PATTERN.is_match(input) {
            Ok((Some(Token::Type), 4))
        } else if let Some(captures) = INTEGER_LITERAL_PATTERN.captures(input) {
            let value: i64 = captures.get(1).unwrap().as_str().parse().unwrap();
            let range = captures.get(1).unwrap();
            Ok((
                Some(Token::IntegerLiteral(value)),
                range.end() - range.start(),
            ))
        } else if let Some(captures) = STRING_LITERAL_PATTERN.captures(input) {
            let value = captures.get(1).unwrap().as_str().to_string();
            let range = captures.get(1).unwrap();
            Ok((
                Some(Token::StringLiteral(value)),
                range.end() - range.start() + 2,
            ))
        } else if let Some(captures) = IDENTIFIER_PATTERN.captures(input) {
            let name = captures.get(1).unwrap().as_str().to_string();
            let range = captures.get(0).unwrap();
            Ok((Some(Token::Identifier(name)), range.end() - range.start()))
        } else if OPEN_BRACKET_PATTERN.is_match(input) {
            Ok((Some(Token::OpenBracket), 1))
        } else if CLOSE_BRACKET_PATTERN.is_match(input) {
            Ok((Some(Token::CloseBracket), 1))
        } else if OPEN_SQUARE_PATTERN.is_match(input) {
            Ok((Some(Token::OpenSquare), 1))
        } else if CLOSE_SQUARE_PATTERN.is_match(input) {
            Ok((Some(Token::CloseSquare), 1))
        } else if let Some(range) = WHITESPACE_PATTERN.find(input) {
            Ok((None, range.end() - range.start()))
        } else {
            Err(format!("Unrecognized token: {}", input))
        }
    }
}

pub fn lex(input: String) -> impl Iterator<Item = Result<Token, String>> {
    let mut progress_index = 0;

    std::iter::from_fn(move || loop {
        let remaining_input = input.as_str().split_at(progress_index).1;
        if remaining_input.len() == 0 {
            return None;
        }
        let (maybe_token, length) = match Token::get_next_token(remaining_input) {
            Ok(ok) => ok,
            Err(error) => return Some(Err(error)),
        };
        progress_index += length;
        if let Some(token) = maybe_token {
            return Some(Ok(token));
        }
    })
}
