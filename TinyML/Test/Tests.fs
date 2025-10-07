module Tests

open Xunit
open TinyML.Expr
open TinyML.Eval

let boolType =
  TypeExpr.Let("bool", [ TypeExpr.Const "True"; TypeExpr.Const "False" ])

let trueVal = ValueExpr.Const("True", boolType)
let falseVal = ValueExpr.Const("False", boolType)

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

[<Fact>]
let ``eval match`` () =
  [ ValueExpr.Match(
      ValueExpr.Var("x", boolType),
      [ Case(Pattern.Const "True", trueVal); Case(Pattern.Const "False", falseVal) ],
      boolType
    ),
    [ "x", trueVal ],
    trueVal ]
  |> List.iter (fun (expr, decls, expected) ->
    let actual = eval (Map.ofList decls) expr
    Assert.Equal(expected, actual))
