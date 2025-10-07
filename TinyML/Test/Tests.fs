module Tests

open Xunit
open TinyML.Expr
open TinyML.Eval

let boolType =
  TypeExpr.Let("bool", [ TypeExpr.Const "True"; TypeExpr.Const "False" ])

let trueVal = ValueExpr.Const("True", boolType)

[<Fact>]
let ``eval literal behaves as id`` () =
  [ ValueExpr.Const("True", boolType) ]
  |> List.iter (fun x ->
    let actual = eval Map.empty x
    Assert.Equal(x, actual))

[<Fact>]
let ``eval variable`` () =
  [ ValueExpr.Var("x", boolType), [ "x", trueVal ], trueVal ]
  |> List.iter (fun (expr, env, expected) ->
    let actual = eval (Map.ofList env) expr
    Assert.Equal(expected, actual))
