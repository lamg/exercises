open System.Collections.Generic

let calculatePrimes (primeList: List<bool>) (stop: int) =
    for i in primeList.Count .. stop do
        primeList.Add true

    for i in primeList.Count .. (int (sqrt (float stop))) do
        if primeList.[i] then
            for j in i * i .. i .. stop do
                primeList.[j] <- false

let primes (primeList: List<bool>) start stop =
    seq {
        for i in start..stop do
            if i >= primeList.Count then
                calculatePrimes primeList stop

            if primeList.[i] then
                yield i
    }

let readInts () =
    stdin.ReadLine().Split([| ' ' |], 2)
    |> Array.map int
    |> function
        | [| m; n |] -> (m, n)
        | _ -> failwith "invalid input"

let printInts = Seq.iter (printfn "%d")

let mutable primeList = List<bool>()
primeList.Add false
primeList.Add false

let cases = stdin.ReadLine() |> int

{ 1..cases }
|> Seq.iter (fun _ ->
    readInts () ||> primes primeList |> printInts
    printfn "")
