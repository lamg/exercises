open System
open System.Threading

type Message =
  | Question of string
  | AnswerSegment of AsyncReplyChannel<string>
  | Stop

let answer = [| "here"; "is"; "your"; "answer" |]

let questionAnswer (inbox: MailboxProcessor<Message>) =
  let rec loop count =
    async {
      // Receive a message
      let! msg = inbox.Receive()
      do! Async.Sleep 500

      return!
        match msg with
        | Question q -> loop 0
        | AnswerSegment channel when count < answer.Length ->
          channel.Reply answer[count]
          loop (count + 1)
        | Stop
        | AnswerSegment _ -> async { () }
    }

  loop 0


let agent = MailboxProcessor.Start questionAnswer

Question "Hello world" |> agent.Post

for i in { 0 .. answer.Length + 1 } do

  async {
    if i >= answer.Length then
      agent.Post Stop
    else
      let! segment = agent.PostAndTryAsyncReply(AnswerSegment, timeout = 10000)
      printfn $"segment = {segment}"
  }
  |> Async.RunSynchronously
