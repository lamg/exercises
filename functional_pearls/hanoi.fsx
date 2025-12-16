[<RequireQualifiedAccess>]
type Tower =
  | A
  | B
  | C

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

let rec (<) (x: Nat) (y: Nat) =
  match x, y with
  | Zero, Succ _ -> true
  | Succ n, Succ m -> n < m
  | _ -> false

type Hanoi = { src: Tower; dest: Tower; n: Nat }

let aux =
  function
  | Tower.A, Tower.C -> Tower.B
  | Tower.A, Tower.B -> Tower.C
  | Tower.B, Tower.C -> Tower.A
  | Tower.B, Tower.A -> Tower.C
  | Tower.C, Tower.A -> Tower.B
  | Tower.C, Tower.B -> Tower.A
  | x, y -> failwith $"invalid configuration {x} -> {y}"

let rec solve (conf: Hanoi) =
  match conf.n with
  | Zero -> []
  | Succ n' ->
    let x = aux (conf.src, conf.dest)

    solve { conf with dest = x; n = n' }
    @ [ conf.src, conf.dest ]
    @ solve { conf with src = x; n = n' }

let hanoi (n: int) =
  { src = Tower.A
    dest = Tower.C
    n = Nat.ofInt n }

let hanoi3 = hanoi 3

let s3 = solve hanoi3
printfn $"conf {hanoi3.src} {hanoi3.dest} {hanoi3.n}"
s3 |> List.iter (fun (x, y) -> printfn $"{x} -> {y}")
printfn "-----------------------------------------"

let check (conf: Hanoi) (xs: list<Tower * Tower>) =
  let N = conf.n.toInt ()
  let towers = List.init N Nat.ofInt, [], []

  let ok (x: Nat list, y: Nat list) =
    match x, y with
    | n :: ns, [] -> true
    | n :: ns, m :: _ when n < m -> true
    | _ -> false

  let res =
    xs
    |> List.fold
      (fun (a, b, c) (x, y) ->
        match x, y with
        | Tower.A, Tower.C when ok (a, c) -> a.Tail, b, a.Head :: c
        | Tower.A, Tower.B when ok (a, b) -> a.Tail, a.Head :: b, c
        | Tower.B, Tower.C when ok (b, c) -> a, b.Tail, b.Head :: c
        | Tower.B, Tower.A when ok (b, a) -> b.Head :: a, b.Tail, c
        | Tower.C, Tower.A when ok (c, a) -> c.Head :: a, b, c.Tail
        | Tower.C, Tower.B when ok (c, b) -> a, c.Head :: b, c.Tail
        | _ -> failwith $"invalid movement {x} -> {y}")
      towers

  match res with
  | [], [], c when Nat.ofInt c.Length = conf.n -> true
  | _ -> false

printfn "conf N | ok "

hanoi
|> Seq.init 5
|> Seq.iter (fun conf ->
  let xs = solve conf
  let ok = check conf xs
  printfn $"conf {conf.n} | {ok}")
