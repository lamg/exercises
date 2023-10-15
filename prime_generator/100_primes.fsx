
let sqrt (n: int) = n |> float |> sqrt |> System.Math.Ceiling |> int

// a number cannot have two prime factors greater than its square root
// if none has found before its square root then is not possible there are prime factors beyond it

let calculatePrimes (cp: ResizeArray<bool>) (stop: int) =
    let start = cp.Count
    for i in cp.Count .. stop do
        cp.Add true

    for i in 2 .. sqrt stop do
        if cp[i] then
            for j in start .. i .. stop do
                cp[j] <- false

let cp = ResizeArray<bool> ()

// cp holds a list of calculated values
// invariant: Seq.forall (fun i -> cp[i] = isPrime i) {0..cp.Count-1}
cp.Add false // 0 is not prime
cp.Add false // 1 is not prime

calculatePrimes cp 98
printfn "Primes up to 100:"
cp |> Seq.mapi (fun i p -> (p,i)) |> Seq.filter fst |>  Seq.iteri (fun n (_,p) -> printfn $"{n}: {p}")
