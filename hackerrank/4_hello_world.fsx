let times = stdin.ReadLine() |> int

{1..times} |> Seq.iter (fun _ -> printfn "Hello World")
