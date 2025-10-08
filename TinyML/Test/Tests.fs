module Tests

open Xunit
open TinyML.Expr
open TinyML.Eval

let boolType =
  TypeExpr.Let("bool", [ TypeExpr.Const "True"; TypeExpr.Const "False" ])

let trueVal = ValueExpr.Const("True", boolType)
let falseVal = ValueExpr.Const("False", boolType)
let truePat = Pattern.Const("True", boolType)
let falsePat = Pattern.Const("False", boolType)

let notFun =
  ValueExpr.Fun(
    Pattern.Var("x", boolType),
    ValueExpr.Match(ValueExpr.Var("x", boolType), [ Case(falsePat, trueVal); Case(truePat, falseVal) ], boolType),
    TypeExpr.Arrow(boolType, boolType)
  )

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
  [ ValueExpr.Match(ValueExpr.Var("x", boolType), [ Case(truePat, trueVal); Case(falsePat, falseVal) ], boolType),
    [ "x", trueVal ],
    trueVal ]
  |> List.iter (fun (expr, decls, expected) ->
    let actual = eval (Map.ofList decls) expr
    Assert.Equal(expected, actual))

[<Fact>]
let ``eval app`` () =
  [ ValueExpr.Let("not", notFun, ValueExpr.App("not", trueVal, boolType)), falseVal ]
  |> List.iter (fun (expr, expected) ->
    let actual = eval Map.empty expr
    Assert.Equal(expected, actual))
