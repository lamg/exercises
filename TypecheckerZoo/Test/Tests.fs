module Tests

open Xunit
open Monads
open AlgorithmW

[<Fact>]
let ``simple instantiate`` () =
  let scheme = Scheme([ "a" ], Type.Tuple [ Type.Var "a"; Type.Int ])
  let defaultCounter = CounterVarState(0, Map.empty)
  let st = StateResult(fun s -> Ok scheme, defaultCounter)
  let expected = Type.Tuple [ Type.Var "t0"; Type.Int ]

  match runStateResult (instantiate st) defaultCounter with
  | Ok actual, m ->
    let programVars = Map.toList m.ProgramVars
    Assert.Equal<List<TmVar * Scheme>>([], programVars)
    Assert.Equal(expected, actual)
  | Error e, _ -> Assert.Fail $"error {e}"


[<Fact>]
let ``infer type`` () =
  [ Expr.Var "x", Error(InferenceError.UnboundVariable "x")
    Expr.Let("x", Expr.Lit(Lit.Int 0), Expr.Var "x"), Ok Type.Int
    Expr.Abs("x", Expr.Lit(Lit.Int 0)), Ok(Type.Arrow(Type.Var "t0", Type.Int))
    Expr.Let("v", Expr.Lit(Lit.Int 0), Expr.Var "v"), Ok Type.Int
    Expr.Tuple [ Expr.Lit(Lit.Int 0); Expr.Lit(Lit.Bool false) ], Ok(Type.Tuple [ Type.Int; Type.Bool ])
    Expr.Let("f", Expr.Abs("x", Expr.Lit(Lit.Int 0)), Expr.Var "f"), Ok(Type.Arrow(Type.Var "t0", Type.Int)) ]
  |> List.iter (fun (expr, expected) ->
    let (StateResult f) = inferTypeOnly expr
    let actual, _ = f (CounterVarState(0, Map.empty))

    match expected, actual with
    | Ok x, Ok y -> Assert.Equal(prettyType x, prettyType y)
    | _ -> Assert.Equal(expected, actual))
