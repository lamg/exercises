// Signature file for parser generated by fsyacc
module Parser
type token = 
  | EOF
  | RIGHT_PAREN
  | LEFT_PAREN
  | NOT
  | DIFFERS
  | EQUIVALES
  | FOLLOWS
  | IMPLIES
  | OR
  | AND
  | VAR of (string)
  | FALSE
  | TRUE
type tokenId = 
    | TOKEN_EOF
    | TOKEN_RIGHT_PAREN
    | TOKEN_LEFT_PAREN
    | TOKEN_NOT
    | TOKEN_DIFFERS
    | TOKEN_EQUIVALES
    | TOKEN_FOLLOWS
    | TOKEN_IMPLIES
    | TOKEN_OR
    | TOKEN_AND
    | TOKEN_VAR
    | TOKEN_FALSE
    | TOKEN_TRUE
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_prog
    | NONTERM_expr
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (Predicate option) 