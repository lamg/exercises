module Problems.FsProblems

//let times = stdin.ReadLine() |> int

//{ 1..times } |> Seq.iter (fun _ -> printfn "Hello World")

let xss = [ [ 1; 2; 3 ]; [ 4; 5; 6 ]; [ 7; 8; 9 ] ]

let incSeq = [ 0 .. xss.Length - 1 ]
let getDiagonal = List.map (fun (x, y) -> xss[x][y])
let firstDiagonal = List.zip incSeq incSeq |> getDiagonal
let secondDiagonal = List.zip incSeq (List.rev incSeq) |> getDiagonal
