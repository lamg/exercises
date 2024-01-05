let readUntil42 () =
    let x = stdin.ReadLine()

    match x with
    | "42" -> None
    | _ -> Some(printfn "%s" x, ())

Seq.unfold readUntil42 () |> Seq.iter ignore
