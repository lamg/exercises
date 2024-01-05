// if searching for prime factors we don't find any before its square root
// then is not possible that its prime factors are greater than its square root
// because at least it needs two and the multiplication of two numbers greater than its square root
// is greater than the number itself
let sqrt (n: int) =
    n |> float |> sqrt |> System.Math.Ceiling |> int

// cv holds a list of calculated values
// Seq.forall (fun i -> cv[i] = isPrime i) {0..cv.Count-1}
// 0 is not prime
// 1 is not prime

let mutable cv = Array.init 2 (fun _ -> false)

let foreachPrime f start stop =
    let rec loop i =
        if i <= stop then
            if cv[i] then
                f i

            loop (i + 1)

    loop (max 2 start)

let iter start step stop f =
    let rec loop i =
        if i <= stop then
            f i
            loop (i + step)

    loop start

let calculatePrimes (stop: int) =
    let cv' = (Array.init (stop - cv.Length + 1) (fun _ -> true))
    cv <- Array.append cv cv'

    let markMultiples p =
        iter (p * p) p stop (fun i -> cv[i] <- false)

    foreachPrime markMultiples 2 (sqrt stop)

let primes start stop =
    if stop > cv.Length then
        calculatePrimes stop

    foreachPrime (printfn "%d") start stop

let readInts () =
    stdin.ReadLine().Split([| ' ' |], 2)
    |> Array.map int
    |> function
        | [| m; n |] -> (m, n)
        | _ -> failwith "invalid input"


let cases = stdin.ReadLine() |> int

{ 1..cases }
|> Seq.iter (fun _ ->
    readInts () ||> primes
    printfn "")

// primes 2 100
