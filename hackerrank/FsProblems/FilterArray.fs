module Problems.FilterArray

let readInt () =
  stdin.ReadLine() |> Option.ofObj |> Option.map int

let read () =
  let delimiter = stdin.ReadLine() |> intlet mutable x = readInt ()

  while x.IsSome do
    if x.Value < delimiter then
      printfn "%d" x.Value

    x <- readInt ()
