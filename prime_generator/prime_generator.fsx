let calculatePrimes (cp: ResizeArray<bool>) (stop: int) =
    for i in cp.Count .. stop do
        cp.Add true

    for i in cp.Count .. (int (sqrt (float stop))) do
        if cp.[i] then
            for j in i * i .. i .. stop do
                cp.[j] <- false

let primes (cp: ResizeArray<bool>) start stop =
    seq {
        for i in start..stop do
            if i >= cp.Count then
                calculatePrimes cp stop

            if cp.[i] then
                yield i
    }

let readInts () =
    stdin.ReadLine().Split([| ' ' |], 2)
    |> Array.map int
    |> function
        | [| m; n |] -> (m, n)
        | _ -> failwith "invalid input"

let printInts = Seq.iter (printfn "%d")
let mutable cp = ResizeArray<bool> ()

// cp holds a list of calculated values
// Seq.forall (fun i -> cp[i] = isPrime i) {0..cp.Count-1}
cp.Add false // 0 is not prime
cp.Add false // 1 is not prime

let cases = stdin.ReadLine() |> int

{ 1..cases }
|> Seq.iter (fun _ ->
    readInts () ||> primes cp |> printInts
    printfn "")
