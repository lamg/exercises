#r "nuget: FSharp.Control.AsyncSeq, 3.2.1"
#r "nuget: FsHttp, 14.5.0"
#r "nuget: LamgEnv, 0.0.2"
#r "nuget: dotenv.net, 3.1.3"

// NOTE: this script requires a you to have an Anthropic API Key.
// Its value should be in an environment variable called "anthropic_key"

open FSharp.Control
open System
open FsHttp

type EventLine =
  | Event of string
  | Data of string
  | Id of int
  | Retry of int

let trimPrefix (prefix: string) (line: string) =
  match line.Split(prefix, StringSplitOptions.TrimEntries) with
  | [| _; x |] -> Some x
  | _ -> None

let parseInt (s: string) =
  let mutable n = 0
  if Int32.TryParse(s, ref n) then Some n else None

let parseEvent = trimPrefix "event:" >> Option.map Event
let parseData = trimPrefix "data:" >> Option.map Data
let parseId = trimPrefix "id:" >> Option.bind parseInt >> Option.map Id
let parseRetry = trimPrefix "retry:" >> Option.bind parseInt >> Option.map Retry

let parseEventLine (line: string) =
  [ parseEvent; parseData; parseId; parseRetry ]
  |> Seq.map (fun x -> x line)
  |> Seq.tryFind _.IsSome
  |> Option.defaultValue None

let readEvents (sr: IO.Stream) =
  let rd = new IO.StreamReader(sr)

  asyncSeq {
    while not rd.EndOfStream do
      let! line = rd.ReadLineAsync() |> Async.AwaitTask

      match parseEventLine line with
      | Some e -> yield e
      | None -> ()
  }


dotenv.net.DotEnv.Load()
let key = LamgEnv.getEnv "anthropic_key" |> _.Value

type Delta =
  { ``type``: string option
    text: string option }

type Message =
  { ``type``: string
    message: obj option
    content_block: obj option
    delta: Delta option
    index: int option }

let deserializeActive (json: string) =
  try
    System.Text.Json.JsonSerializer.Deserialize<Message> json |> Some
  with _ ->
    None

let eventToMsg (line: EventLine) =
  match line with
  | Data d ->
    match deserializeActive d with
    | Some { ``type`` = "message_start" } -> None
    | Some { ``type`` = "ping" } -> None
    | Some { ``type`` = "content_block_delta"
             delta = Some { text = Some t } } -> Some t
    | _ -> None
  | _ -> None

let ask (key: string) (model: string) (question: string) =
  http {
    POST "https://api.anthropic.com/v1/messages"
    header "x-api-key" key
    header "anthropic-version" "2023-06-01"
    body

    jsonSerialize
      {| model = model
         max_tokens = 1024
         stream = true
         messages = [ {| role = "user"; content = question |} ] |}
  }
  |> Request.send
  |> Response.toStream
  |> readEvents
  |> AsyncSeq.choose eventToMsg
  |> AsyncSeq.iter (fun token -> printf $"{token}")
  |> Async.RunSynchronously

ask key "claude-3-5-sonnet-20240620" "what is your favorite functional algorithm. Implement it in F# please."
