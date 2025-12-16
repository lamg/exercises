type Nat =
  | Zero
  | Succ of Nat

  member this.toInt() =
    match this with
    | Zero -> 0
    | Succ n -> 1 + n.toInt ()

  override this.ToString() = this.toInt().ToString()

  static member ofInt =
    function
    | 0 -> Zero
    | n when n > 0 -> Succ(Nat.ofInt (n - 1))
    | n -> failwith $"{n} is not a natural number"

#nowarn "86"

let rec (<=) (x: Nat) (y: Nat) =
  match x, y with
  | Zero, _ -> true
  | Succ n, Succ m -> n <= m
  | _ -> false

let (<) (x: Nat) (y: Nat) = x <> y && x <= y
let (>=) (x: Nat) (y: Nat) = y <= x
let (>) (x: Nat) (y: Nat) = x <> y && x >= y

let rec (+) (x: Nat) (y: Nat) =
  match x with
  | Zero -> y
  | Succ n -> Succ(n + y)

let rec (-) (x: Nat) (y: Nat) =
  match x, y with
  | Zero, _ -> Zero
  | _, Zero -> x
  | Succ n, Succ m -> n - m

let rec (*) (x: Nat) (y: Nat) =
  match x with
  | Zero -> Zero
  | Succ Zero -> y
  | Succ n -> y + n * y

let rec (/) (x: Nat) (y: Nat) =
  // (m, k) such:
  // x = m * y + k  &&  (y != 0 && k < y  ||  y = 0 && k = x)
  match x - y with
  | _ when y = Zero -> Zero, x // TODO find definitions that make some algebraic sense for division by 0
  | _ when x = Zero -> Zero, Zero
  | _ when x = y -> Succ Zero, Zero
  | Zero -> Zero, x
  | r ->
    let m, k = r / y
    Succ m, k

let tests () =
  let test (x: int, op: Nat -> Nat -> (string * Nat), y: int) (r: int) =
    let str_op, actual = op (Nat.ofInt x) (Nat.ofInt y)

    let status =
      if actual = Nat.ofInt r then
        $"{actual} OK"
      else
        $"{actual} WRONG, expected {r}"

    $"{x} {str_op} {y} = {status}"

  let plus x y = "+", x + y
  let minus x y = "-", x - y
  let times x y = "*", x * y

  [ 2, plus, 2, 4; 3, minus, 3, 0; 2, times, 2, 4; 4, times, 4, 16 ]
  |> List.iter (fun (x, op, y, r) ->
    let r = test (x, op, y) r
    printfn $"{r}")

  [ 3, 2, (1, 1)
    2, 2, (1, 0)
    4, 2, (2, 0)
    16, 4, (4, 0)
    10, 7, (1, 3)
    10, 0, (0, 10) ]
  |> List.iter (fun (x, y, (m, k)) ->
    let x, y, m, k = Nat.ofInt x, Nat.ofInt y, Nat.ofInt m, Nat.ofInt k
    let dividend = y * m + k

    if dividend <> x then
      failwith $"{y} * {m} + {k} = {dividend}, expected {x}"

    let actual = x / y

    let status =
      if actual = (m, k) then
        $"{actual} OK"
      else
        $"{actual} WRONG, expected {(m, k)}"

    printfn $"{x} / {y} = {status}")
