use regex::Regex;
use lazy_static::lazy_static;


#[derive(Debug)]
pub enum Token {
    IntegerLiteral(i64),
    OpenBracket,
    CloseBracket,
}

impl Token {
    fn get_next_token(input: &str) -> Result<(Option<Token>, usize), String> {
        lazy_static! {
            static ref INTEGER_LITERAL_PATTERN: Regex = Regex::new(r"^(-?\d+)").unwrap();
            static ref OPEN_BRACKET_PATTERN: Regex = Regex::new(r"^\(").unwrap();
            static ref CLOSE_BRACKET_PATTERN: Regex = Regex::new(r"^\)").unwrap();
            static ref WHITESPACE_PATTERN: Regex = Regex::new(r"^\s+").unwrap();
        }
        if let Some(captures) = INTEGER_LITERAL_PATTERN.captures(input) {
            let value: i64 = captures.get(1).unwrap().as_str().parse().unwrap();
            let range = captures.get(0).unwrap();
            Ok((Some(Token::IntegerLiteral(value)), range.end() - range.start()))
        } else if let Some(range) = OPEN_BRACKET_PATTERN.find(input) {
            Ok((Some(Token::OpenBracket), range.end() - range.start()))
        } else if let Some(range) = CLOSE_BRACKET_PATTERN.find(input) {
            Ok((Some(Token::CloseBracket), range.end() - range.start()))
        } else if let Some(range) = WHITESPACE_PATTERN.find(input) {
            Ok((None, range.end() - range.start()))
        } else {
            println!("Token:{}.", input);
            Err("Unrecognized token".to_string())
        }
    }
}

pub fn lex(input: String) -> impl Iterator<Item = Result<Token, String>> {
    let mut progress_index = 0;

    std::iter::from_fn(move || {
        loop {
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
        }
    })
}
