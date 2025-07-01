type Adjective =
  | Beautiful
  | Large
  | Small

type Noun =
  | House
  | River
  | Description of Noun * Adjective list

let f (x: Adjective) (noun: Noun) =
  match noun with
  | Description(n, adjectives) -> Description(n, x :: adjectives)
  | _ -> Description(noun, [ x ])

open System
open System.Runtime.CompilerServices

type Assert =
  static member failAtCaller(message: string, [<CallerFilePath>] ?filePath: string, [<CallerLineNumber>] ?lineNumber) =
    let fullMessage =
      sprintf "Assertion failed at %s:%d\nMessage: %s" (defaultArg filePath "") (defaultArg lineNumber 0) message

    printfn "%s" fullMessage

  static member inline equal(expected: 'a, actual: 'a, [<CallerFilePath>] ?filePath, [<CallerLineNumber>] ?lineNumber) =
    if expected <> actual then
      let msg = sprintf "Expected: %A\nActual: %A" expected actual
      let filePath, lineNumber = defaultArg filePath "", defaultArg lineNumber 0
      Assert.failAtCaller (msg, filePath, lineNumber)
    else
      ()


let ``beautiful house`` = f Beautiful House

let ``casa bonita`` = House |> f Beautiful

Assert.equal (``beautiful house``, ``casa bonita``)

let ``casa bonita grande`` = House |> f Beautiful |> f Large

let ``large beautiful house`` = f Large (f Beautiful House)

Assert.equal (``large beautiful house``, ``casa bonita``)
