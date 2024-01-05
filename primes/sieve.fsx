let ns = Seq.initInfinite id |> Seq.skip 2

let isPrime n =
    Seq.forall (fun x -> n % x <> 0) { 2 .. n - 1 }

let primes = ns |> Seq.filter isPrime
let firstNPrimes n = primes |> Seq.take n |> Seq.toList

printfn "the first 10 primes = %A" (firstNPrimes 10)
