module TinyML.Eval

open Expr

let rec substitute (var: string) (expr: ValueExpr) (inExpr: ValueExpr) =
  match inExpr with
  | ValueExpr.Var(v, ty) when v = var && ty = expr.Type -> expr
  | ValueExpr.Var(v, ty) when v = var && ty <> expr.Type ->
    failwith $"cannot substitute variable {v} of type {ty} with value of type {expr.Type}"
  | ValueExpr.Var _ -> inExpr
  | ValueExpr.App(f, arg, ty) -> ValueExpr.App(f, substitute var expr arg, ty)
  | ValueExpr.Fun(arg, body, ty) -> ValueExpr.Fun(arg, substitute var expr body, ty)
  | ValueExpr.Let(var, varExpr, inExpr) -> ValueExpr.Let(var, varExpr, inExpr)
  | ValueExpr.Const(_, _) -> inExpr
  | ValueExpr.ConstFun(ctor, arg, ty) -> ValueExpr.ConstFun(ctor, substitute var expr arg, ty)
  | ValueExpr.Match(matchExpr, cases, ty) ->
    let newExpr = substitute var expr matchExpr

    let newCases =
      cases
      |> List.map (fun (Case(pat, guardedExpr)) -> Case(pat, substitute var expr guardedExpr))

    ValueExpr.Match(newExpr, newCases, ty)

let rec matchPattern (pat: Pattern) (expr: ValueExpr) =
  match pat, expr with
  | Pattern.Var(x, _), _ -> Some [ x, expr ]
  | Pattern.Const(c, _), ValueExpr.Const(c', _) when c = c' -> Some []
  | Pattern.ConstFun(c, Pattern.Var(x, _), _), ValueExpr.ConstFun(c', e, _) when c = c' -> Some [ x, e ]
  | Pattern.ConstFun(c, Pattern.All _, _), ValueExpr.ConstFun(c', _, _) when c = c' -> Some []
  | Pattern.ConstFun(c, f, _), ValueExpr.ConstFun(c', e, _) when c = c' -> matchPattern f e
  | Pattern.All _, _ -> Some []
  | _, _ -> None


let rec eval (decls: Map<string, ValueExpr>) (expr: ValueExpr) =
  match expr with
  | ValueExpr.Var(x, ty) ->
    match decls.TryGetValue x with
    | true, v when v.Type = ty -> v
    | true, v ->
      failwith $"value doesn't match with variable type: {x} has type {ty} in {expr}, but {v} has type {v.Type}"
    | _, _ -> failwith $"failed to evaluate: undeclared {x} in map {Map.toList decls}"
  | ValueExpr.App(f, arg, ty) ->
    match decls.TryGetValue f with
    | true, tyExpr ->
      match tyExpr with
      | ValueExpr.Fun(pat, body, TypeExpr.Arrow(ty_x, t_result)) when ty_x = arg.Type && t_result = ty ->
        let newDecls =
          matchPattern pat arg
          |> Option.defaultValue []
          |> List.fold (fun decls (var, expr) -> Map.add var expr decls) decls

        assert (newDecls.Count = decls.Count + pat.DeclarationCount())

        eval newDecls body
      | _ -> failwith $"{f} has type {ty}, but for evaluating {expr} type {expr.Type} is required"
    | false, _ -> failwith $"not found definition for {f}"
  | ValueExpr.Fun(pat, body, ty) ->
    let newBody = eval decls body
    ValueExpr.Fun(pat, newBody, ty)
  | ValueExpr.Let(var, varExpr, inExpr) ->
    let newDecls = decls |> Map.add var varExpr
    eval newDecls inExpr
  | ValueExpr.Const _ -> expr
  | ValueExpr.ConstFun(cf, expr, ty) -> ValueExpr.ConstFun(cf, eval decls expr, ty)
  | ValueExpr.Match(expr, cases, ty) ->
    let e = eval decls expr

    cases
    |> Seq.choose (fun (Case(pat, expr)) ->
      match matchPattern pat e with
      | Some xs ->
        let newExpr = xs |> List.fold (fun acc (v, e) -> substitute v e acc) expr
        Some(eval decls newExpr)
      | None -> None)
    |> Seq.tryHead
    |> function
      | Some r when r.Type = ty -> r
      | Some r -> failwith $"expecting {expr} to be evaluated to a {ty}, but got {r.Type}"
      | None -> failwith $"no case matched {expr} in {cases}"
