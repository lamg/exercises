module Monads

type OriginalState<'a, 's> = State of ('s -> 'a * 's)

type OriginalStateBuilder() =
  member _.Return x = State(fun s -> x, s)
  member _.ReturnFrom x = x

  member _.Bind(State m, f) =
    State(fun s ->
      let a, s' = m s
      let (State m0) = f a
      m0 s')

  member _.Run(x: OriginalState<'b, 's>) = x

  member this.Get() = State(fun s -> s, s)
  member _.Put newState = State(fun _ -> (), newState)

  member _.Fold (f: OriginalState<'b, 's> -> 'a -> OriginalState<'b, 's>) (acc: OriginalState<'b, 's>) (xs: List<'a>) =
    let rec loop acc remaining =
      match remaining with
      | [] -> acc
      | x :: xs' ->
        let next = f acc x
        loop next xs'

    loop acc xs

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

// a combination of the State and Result monads aboveo
type State<'ok, 'err, 's> = State of ('s -> Result<'ok, 'err> * 's)

let runStateResult (st: State<'ok, 'err, 's>) (x: 's) =
  let (State f) = st
  f x

type StateBuilder() =
  member _.Bind((State x): State<'ok, 'err, 's>, f: 'ok -> State<'nok, 'err, 's>) =
    State(fun s ->
      match x s with
      | Ok y, ns ->
        let (State n) = f y
        n ns
      | Error e, ns -> Error e, ns)

  member _.Return x = State(fun s -> Ok x, s)

  member _.Get() = State(fun s -> Ok s, s)

  member _.Put s = State(fun _ -> Ok(), s)

  member _.ReturnFrom(State s) = State s

  member this.Fold (f: State<'ok, 'err, 's> -> 'a -> State<'ok, 'err, 's>) (acc: State<'ok, 'err, 's>) (xs: List<'a>) =
    match xs with
    | [] -> acc
    | y :: ys ->
      State(fun s ->
        // Run one step: apply f to accumulator and current element
        let (State step) = f acc y

        match step s with
        | Ok v, s' ->
          // Create a new accumulator that just returns v (state comes from input)
          let newAcc = State(fun s'' -> Ok v, s'')
          // Recurse on the rest of the list
          let (State cont) = this.Fold f newAcc ys
          cont s'
        | Error e, s' -> Error e, s')

// a combination of the State and Result monads
let state = StateBuilder()
