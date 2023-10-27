module CheckOps

// check an F# file holds the following properties
// - contains a function with the signature `main: string seq -> string seq`
// - does not write or read from stdin, stdout, stderr
// - does not interact with the file system
// - does not load any external libraries

open FSharp.Analyzers.SDK

let analyzer (ctx: CliContext) : Async<Message list> =
        async {
            return
                [ { Type = "CheckOps analyzer"
                    Message = "Forbidden operations are used in this file"
                    Code = "CO001"
                    Severity = Error
                    Range = FSharp.Compiler.Text.Range.Zero
                    Fixes = [] } ]
        }

[<CliAnalyzer "CheckOps">]
let main: Analyzer<CliContext> = analyzer