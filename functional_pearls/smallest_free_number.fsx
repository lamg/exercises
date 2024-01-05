// minfree finds the smallest number not appearing in a list of numbers
// for example, minFree [0..10] = 11, minFree [0;1;3] = 2

let minFree (xs: int seq) =
    let naturalNumbers = Seq.initInfinite id
    let notInXs n = not (Seq.contains n xs)
    let gaps = Seq.filter notInXs naturalNumbers
    Seq.head gaps

// minFree works by finding the difference between a sequence that
// has all natural numbers and one that can contain gaps between natural numbers.
// In case there's no gap between numbers, that sequence is just finite,
// therefore we will find a natural number that is not there,
// i.e. the gap is in the end.

// Since the sequence of natural numbers is ordered then the first gap we find
// is the minimum free number.

// However, in the worst case we have the sequence of the first n naturals xs = [0..n-1].
// For each i in [0..n-1] we make i+1 comparisons before moving to the next i.
// So the total number of comparisons is sum [1..n] = n*(n+1)/2.

printfn "minFree [0..10] = %d" (minFree [ 0..10 ])
