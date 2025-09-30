module Tests

open Xunit
open Monads
open AlgorithmW

[<Fact>]
let ``infer type`` () =
  [ // Expr.Var "x", Error(InferenceError.UnboundVariable "x")
    // Expr.Let("x", Expr.Lit(Lit.Int 0), Expr.Var "x"), Ok Type.Int]
    // Expr.Abs("x", Expr.Lit(Lit.Int 0)), Ok(Type.Arrow(Type.Var "t0", Type.Int))
    Expr.Let ("v", Expr.Lit (Lit.Int 0), Expr.Var "v"), Ok Type.Int
    // Expr.Let("f", Expr.Abs("x", Expr.Lit(Lit.Int 0)), Expr.Var "f"), Ok(Type.Arrow(Type.Var "t0", Type.Int))
     ]
  |> List.iter (fun (expr, expected) ->
    let (StateResult f) = inferTypeOnly expr
    let actual, _ = f (InferenceState (0, Map.empty))
    Assert.Equal(expected, actual))
