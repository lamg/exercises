module Problems.Fs

let repeat_s_x (s: int) (x: string) =
    { 1..s } |> Seq.iter (fun _ -> printfn "%s" x)

let s = stdin.ReadLine() |> int



let xs = ResizeArray<string>()
let mutable x = stdin.ReadLine() |> Option.ofObj

while x.IsSome do
    x.Value |> xs.Add
    x <- stdin.ReadLine() |> Option.ofObj

xs |> Seq.iter (repeat_s_x s)
