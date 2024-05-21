// Implementation file for parser generated by fsyacc
module Parser
#nowarn "64";; // turn off warnings that type variables used in production annotations are instantiated to concrete type
open FSharp.Text.Lexing
open FSharp.Text.Parsing.ParseHelpers
# 1 "Parser.fsy"

    open Lib

# 10 "Parser.fs"
// This type is the type of tokens accepted by the parser
type token = 
  | EOF
  | NOT
  | DIFFERS
  | EQUIVALES
  | FOLLOWS
  | IMPLIES
  | OR
  | AND
  | FALSE
  | TRUE
// This type is used to give symbolic names to token indexes, useful for error messages
type tokenId = 
    | TOKEN_EOF
    | TOKEN_NOT
    | TOKEN_DIFFERS
    | TOKEN_EQUIVALES
    | TOKEN_FOLLOWS
    | TOKEN_IMPLIES
    | TOKEN_OR
    | TOKEN_AND
    | TOKEN_FALSE
    | TOKEN_TRUE
    | TOKEN_end_of_input
    | TOKEN_error
// This type is used to give symbolic names to token indexes, useful for error messages
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_prog
    | NONTERM_expr

// This function maps tokens to integer indexes
let tagOfToken (t:token) = 
  match t with
  | EOF  -> 0 
  | NOT  -> 1 
  | DIFFERS  -> 2 
  | EQUIVALES  -> 3 
  | FOLLOWS  -> 4 
  | IMPLIES  -> 5 
  | OR  -> 6 
  | AND  -> 7 
  | FALSE  -> 8 
  | TRUE  -> 9 

// This function maps integer indexes to symbolic token ids
let tokenTagToTokenId (tokenIdx:int) = 
  match tokenIdx with
  | 0 -> TOKEN_EOF 
  | 1 -> TOKEN_NOT 
  | 2 -> TOKEN_DIFFERS 
  | 3 -> TOKEN_EQUIVALES 
  | 4 -> TOKEN_FOLLOWS 
  | 5 -> TOKEN_IMPLIES 
  | 6 -> TOKEN_OR 
  | 7 -> TOKEN_AND 
  | 8 -> TOKEN_FALSE 
  | 9 -> TOKEN_TRUE 
  | 12 -> TOKEN_end_of_input
  | 10 -> TOKEN_error
  | _ -> failwith "tokenTagToTokenId: bad token"

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
let prodIdxToNonTerminal (prodIdx:int) = 
  match prodIdx with
    | 0 -> NONTERM__startstart 
    | 1 -> NONTERM_start 
    | 2 -> NONTERM_prog 
    | 3 -> NONTERM_prog 
    | 4 -> NONTERM_expr 
    | 5 -> NONTERM_expr 
    | _ -> failwith "prodIdxToNonTerminal: bad production index"

let _fsyacc_endOfInputTag = 12 
let _fsyacc_tagOfErrorTerminal = 10

// This function gets the name of a token as a string
let token_to_string (t:token) = 
  match t with 
  | EOF  -> "EOF" 
  | NOT  -> "NOT" 
  | DIFFERS  -> "DIFFERS" 
  | EQUIVALES  -> "EQUIVALES" 
  | FOLLOWS  -> "FOLLOWS" 
  | IMPLIES  -> "IMPLIES" 
  | OR  -> "OR" 
  | AND  -> "AND" 
  | FALSE  -> "FALSE" 
  | TRUE  -> "TRUE" 

// This function gets the data carried by a token as an object
let _fsyacc_dataOfToken (t:token) = 
  match t with 
  | EOF  -> (null : System.Object) 
  | NOT  -> (null : System.Object) 
  | DIFFERS  -> (null : System.Object) 
  | EQUIVALES  -> (null : System.Object) 
  | FOLLOWS  -> (null : System.Object) 
  | IMPLIES  -> (null : System.Object) 
  | OR  -> (null : System.Object) 
  | AND  -> (null : System.Object) 
  | FALSE  -> (null : System.Object) 
  | TRUE  -> (null : System.Object) 
let _fsyacc_gotos = [| 0us;65535us;1us;65535us;0us;1us;1us;65535us;0us;2us;1us;65535us;0us;4us;|]
let _fsyacc_sparseGotoTableRowOffsets = [|0us;1us;3us;5us;|]
let _fsyacc_stateToProdIdxsTableElements = [| 1us;0us;1us;0us;1us;1us;1us;2us;1us;3us;1us;4us;1us;5us;|]
let _fsyacc_stateToProdIdxsTableRowOffsets = [|0us;2us;4us;6us;8us;10us;12us;|]
let _fsyacc_action_rows = 7
let _fsyacc_actionTableElements = [|3us;32768us;0us;3us;8us;6us;9us;5us;0us;49152us;0us;16385us;0us;16386us;0us;16387us;0us;16388us;0us;16389us;|]
let _fsyacc_actionTableRowOffsets = [|0us;4us;5us;6us;7us;8us;9us;|]
let _fsyacc_reductionSymbolCounts = [|1us;1us;1us;1us;1us;1us;|]
let _fsyacc_productionToNonTerminalTable = [|0us;1us;2us;2us;3us;3us;|]
let _fsyacc_immediateActions = [|65535us;49152us;16385us;16386us;16387us;16388us;16389us;|]
let _fsyacc_reductions = lazy [|
# 127 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> Boolean option in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : 'gentype__startstart));
# 136 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_prog in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 24 "Parser.fsy"
                                   _1 
                   )
# 24 "Parser.fsy"
                 : Boolean option));
# 147 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 27 "Parser.fsy"
                                 None 
                   )
# 27 "Parser.fsy"
                 : 'gentype_prog));
# 157 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 28 "Parser.fsy"
                                  Some _1 
                   )
# 28 "Parser.fsy"
                 : 'gentype_prog));
# 168 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 31 "Parser.fsy"
                                  True 
                   )
# 31 "Parser.fsy"
                 : 'gentype_expr));
# 178 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 32 "Parser.fsy"
                                   False 
                   )
# 32 "Parser.fsy"
                 : 'gentype_expr));
|]
# 189 "Parser.fs"
let tables : FSharp.Text.Parsing.Tables<_> = 
  { reductions = _fsyacc_reductions.Value;
    endOfInputTag = _fsyacc_endOfInputTag;
    tagOfToken = tagOfToken;
    dataOfToken = _fsyacc_dataOfToken; 
    actionTableElements = _fsyacc_actionTableElements;
    actionTableRowOffsets = _fsyacc_actionTableRowOffsets;
    stateToProdIdxsTableElements = _fsyacc_stateToProdIdxsTableElements;
    stateToProdIdxsTableRowOffsets = _fsyacc_stateToProdIdxsTableRowOffsets;
    reductionSymbolCounts = _fsyacc_reductionSymbolCounts;
    immediateActions = _fsyacc_immediateActions;
    gotos = _fsyacc_gotos;
    sparseGotoTableRowOffsets = _fsyacc_sparseGotoTableRowOffsets;
    tagOfErrorTerminal = _fsyacc_tagOfErrorTerminal;
    parseError = (fun (ctxt:FSharp.Text.Parsing.ParseErrorContext<_>) -> 
                              match parse_error_rich with 
                              | Some f -> f ctxt
                              | None -> parse_error ctxt.Message);
    numTerminals = 13;
    productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable  }
let engine lexer lexbuf startState = tables.Interpret(lexer, lexbuf, startState)
let start lexer lexbuf : Boolean option =
    engine lexer lexbuf 0 :?> _
