module Tests

open Xunit

open AlgorithmW

[<Fact>]
let ``infer var type`` () =
  [ // Expr.Var "x", Error(InferenceError.UnboundVariable "x")
    // Expr.Let("x", Expr.Lit(Lit.Int 0), Expr.Var "x"), Ok Type.Int
    Expr.Let("f", Expr.Abs("x", Expr.Lit(Lit.Int 0)), Expr.Var "f"), Ok(Type.Arrow(Type.Var "t0", Type.Int)) ]
  |> List.iter (fun (expr, expected) ->
    let actual = inferTypeOnly expr
    Assert.Equal(expected, actual))
