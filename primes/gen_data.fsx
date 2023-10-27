let cases = 10
printfn "%d" cases
let rnd = System.Random()

for i in 1..cases do
    let m = rnd.Next()
    let n = m + rnd.Next 100000
    printfn "%d %d" m n
