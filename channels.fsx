open System
open System.Threading
open System.Threading.Channels

let c = Channel.CreateUnbounded<string>()

// push 10 string values into a channel with one second delay
// between each other
List.init 10 (fun n -> $"{n}")
|> List.map (fun x ->
    async {
        let v = c.Writer.WriteAsync x
        do! Async.Sleep 1000
        return! v.AsTask() |> Async.AwaitTask
    })
|> Async.Sequential
|> Async.Ignore
|> Async.Start

// read the values from another thread and stop after 2 seconds
// waiting for a value

let mutable next = true

while next do
    let tks = new CancellationTokenSource(TimeSpan.FromSeconds 2)
    let v = c.Reader.ReadAsync tks.Token
    printf "waiting … "

    try
        let r = v.AsTask() |> Async.AwaitTask |> Async.RunSynchronously
        printfn $"got {r}"
    with :? Tasks.TaskCanceledException ->
        next <- false

printfn "finished"
