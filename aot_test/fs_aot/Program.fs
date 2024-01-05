let factorial (n: uint64) =
  let rec loop (acc: uint64) (n: uint64) =
    if n = 0UL then acc else loop (acc * n) (n - 1UL)

  loop 1UL n

printfn $"factorial 10 = {factorial 10UL}"
