#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntheticError {
    UnexpectedEndOfInput,
    InvalidToken,
    UnterminatedString,
    ExpectedCharacter {
        expected: char,
        found: Option<char>
    }
}