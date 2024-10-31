module Main

open Elmish
open Bolero

type Model = { counter: int }

let initModel = { counter = 0 }

type Message =
  | Increment
  | Decrement
  | SetCounter of int

let update message model =
  let change =
    match message with
    | Increment -> (+) 1
    | Decrement -> (+) -1
    | SetCounter v -> (fun _ -> v)

  let model =
    { model with
        counter = change model.counter }

  model, Cmd.none


type Main = Template<"wwwroot/main.html">

let view model dispatch =
  Main
    .Counter()
    .Decrement(fun _ -> dispatch Decrement)
    .Increment(fun _ -> dispatch Increment)
    .Value(model.counter, fun v -> dispatch (SetCounter v))
    .Elt()

type Counter() =
  inherit ProgramComponent<Model, Message>()

  override _.Program =
    Program.mkProgram (fun _ -> initModel, Cmd.ofMsg (SetCounter 0)) update view
