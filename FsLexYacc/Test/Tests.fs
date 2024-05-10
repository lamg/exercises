module Tests

open Xunit
open FSharp.Text.Lexing
open Lib

let parse source =
  let lexbuf = LexBuffer<char>.FromString source
  let res = Parser.start Lexer.read lexbuf

  match res with
  | Some ast -> ast
  | None -> failwith "failed to parse"

[<Fact>]
let ``My test`` () = 
  let source = "true false true false false"
  let ast = parse source
  Assert.Equal (True, ast)
