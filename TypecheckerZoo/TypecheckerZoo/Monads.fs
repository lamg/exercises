module Monads

type State<'a, 's> = State of ('s -> 'a * 's)

type StateBuilder() =
  member _.Return x = State(fun s -> x, s)
  member _.ReturnFrom x = x

  member _.Bind(State m, f) =
    State(fun s ->
      let a, s' = m s
      let (State m0) = f a
      m0 s')

  member _.Run(x: State<'b, 's>) = x

  member this.Get() = State(fun s -> s, s)
  member _.Put newState = State(fun _ -> (), newState)

  member _.Fold (f: State<'b, 's> -> 'a -> State<'b, 's>) (acc: State<'b, 's>) (xs: List<'a>) =
    let rec loop acc remaining =
      match remaining with
      | [] -> acc
      | x :: xs' ->
        let next = f acc x
        loop next xs'

    loop acc xs


let state = StateBuilder()

type ResultBuilder() =
  member this.Return x = Ok x

  member this.Bind(r: Result<'a, 'c>, f: 'a -> Result<'b, 'c>) =
    match r with
    | Ok x -> f x
    | Error e -> Error e

  member this.Fold (f: 'b -> 'a -> Result<'b, 'c>) (acc: 'b) (xs: List<'a>) =
    match xs with
    | [] -> Ok acc
    | y :: ys ->
      match f acc y with
      | Ok m -> this.Fold f m ys
      | Error e -> Error e

let result = ResultBuilder()

type StateResult<'ok, 'err, 's> = StateResult of ('s -> Result<'ok, 'err> * 's)

let runStateResult (st: StateResult<'ok, 'err, 's>) (x: 's) =
  let (StateResult f) = st
  f x

type StateResultBuilder() =
  member _.Bind((StateResult x): StateResult<'ok, 'err, 's>, f: 'ok -> StateResult<'nok, 'err, 's>) =
    StateResult(fun s ->
      match x s with
      | Ok y, ns ->
        let (StateResult n) = f y
        n ns
      | Error e, ns -> Error e, ns)

  member _.Return x = StateResult(fun s -> Ok x, s)

  member _.Get() = StateResult(fun s -> Ok s, s)

  member _.Put s = StateResult(fun _ -> Ok(), s)

  member _.ReturnFrom(StateResult s) = StateResult s

  member this.Fold
    (f: StateResult<'ok, 'err, 's> -> 'a -> StateResult<'ok, 'err, 's>)
    (acc: StateResult<'ok, 'err, 's>)
    (xs: List<'a>)
    =
    match xs with
    | [] -> acc
    | y :: ys ->
      StateResult(fun s ->
        // Run one step: apply f to accumulator and current element
        let (StateResult step) = f acc y

        match step s with
        | Ok v, s' ->
          // Create a new accumulator that just returns v (state comes from input)
          let newAcc = StateResult(fun s'' -> Ok v, s'')
          // Recurse on the rest of the list
          let (StateResult cont) = this.Fold f newAcc ys
          cont s'
        | Error e, s' -> Error e, s')

let stateResult = StateResultBuilder()
