module Monads

type State<'s, 'a> = State of ('s -> 'a * 's)

type StateBuilder() =
  member _.Return x = State(fun s -> x, s)

  member _.Bind(State m, f) =
    State(fun s ->
      let a, s' = m s
      let (State m0) = f a
      m0 s')

  member _.Run s (State f) = f s

  member this.get() = State(fun s -> s, s)
  member _.put newState = State(fun _ -> (), newState)

  member _.fold (f: State<'s, 'b> -> 'a -> State<'s, 'b>) (acc: State<'s, 'b>) (xs: List<'a>) =
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

  member this.fold (f: 'b -> 'a -> Result<'b, 'c>) (acc: 'b) (xs: List<'a>) =
    match xs with
    | [] -> Ok acc
    | y :: ys ->
      match f acc y with
      | Ok m -> this.fold f m ys
      | Error e -> Error e

let result = ResultBuilder()
