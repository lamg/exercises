#r "nuget: FParsec, 2.0.0-beta2"

open FParsec.Primitives
open FParsec.CharParsers

type Statement =
    | CreateTable
    | InsertInto

let keyword (s: string) = spaces >>. skipString s .>> spaces

let createTable =
    parse {
        do! keyword "CREATE"
        do! keyword "TABLE"
        return CreateTable
    }

let insertInto =
    parse {
        do! keyword "INSERT"
        do! keyword "INTO"
        return InsertInto
    }

let statement = attempt createTable <|> insertInto

let cases =
    [ "CREATE TABLE", CreateTable
      "INSERT INTO", InsertInto
      " INSERT INTO", InsertInto ]

cases
|> List.iter (fun (input, expected) ->
    let result = runParserOnString statement () "test" input

    match result with
    | Success(actual, _, _) when actual = expected -> printfn "Success"
    | Success(actual, _, _) -> printfn $"Failure: expected {expected}, got {actual}"
    | Failure(msg, _, _) -> printfn $"Failure: {msg}")
