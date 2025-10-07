module TinyML.Eval

open Expr

let rec substitute (var: string) (expr: ValueExpr) (inExpr: ValueExpr) =
  match inExpr with
  | ValueExpr.Var(v, ty) when v = var && ty = expr.Type -> expr
  | ValueExpr.Var(v, ty) when v = var && ty <> expr.Type ->
    failwith $"cannot substitute variable {v} of type {ty} with value of type {expr.Type}"
  | ValueExpr.Var _ -> inExpr
  | ValueExpr.Binary(op, left, right, ty) ->
    ValueExpr.Binary(op, substitute var expr left, substitute var expr right, ty)
  | ValueExpr.Unary(op, right, ty) -> ValueExpr.Unary(op, substitute var expr right, ty)
  | ValueExpr.Fun(arg, body, ty) -> ValueExpr.Fun(arg, substitute var expr body, ty)
  | ValueExpr.Let(var, varExpr, inExpr) -> ValueExpr.Let(var, varExpr, inExpr)
  | ValueExpr.Const(_, _) -> inExpr
  | ValueExpr.ConstFun(_, _, _) -> failwith "Not Implemented"
  | ValueExpr.Match(expr, cases, ty) -> failwith "Not Implemented"

let rec matchPattern (pat: Pattern) (expr: ValueExpr) =
  match pat, expr with
  | Pattern.Const c, ValueExpr.Const(c', _) when c = c' -> Some []
  | Pattern.ConstFun(c, Pattern.Var x), ValueExpr.ConstFun(c', e, _) when c = c' -> Some [ x, e ]
  | Pattern.ConstFun(c, Pattern.All), ValueExpr.ConstFun(c', _, _) when c = c' -> Some []
  | Pattern.ConstFun(c, f), ValueExpr.ConstFun(c', e, _) when c = c' -> matchPattern f e
  | Pattern.All, _ -> Some []
  | _, _ -> None


let rec eval (decls: Map<string, ValueExpr>) (expr: ValueExpr) =
  match expr with
  | ValueExpr.Var(x, ty) ->
    match decls.TryGetValue x with
    | true, v when v.Type = ty -> v
    | true, v when v.Type <> ty ->
      failwith $"value doesn't match with variable type: {x} has type {ty} in {expr}, but {v} has type {v.Type} "
    | _, _ -> failwith $"failed to evaluate: undeclared {x}"
  | ValueExpr.Binary(op, left, right, ty) ->
    match decls.TryGetValue op with
    | true, tyExpr ->
      match tyExpr with
      | ValueExpr.Fun(x, ValueExpr.Fun(y, body, _), TypeExpr.Arrow(ty_x, TypeExpr.Arrow(ty_y, t_result))) when
        ty_x = left.Type && ty_y = right.Type && t_result = ty
        ->
        let subst0 = substitute y right body
        let subst1 = substitute x left subst0
        eval decls subst1
      | _ -> failwith $"{op} has type {ty}, but for evaluating {expr} type {expr.Type} is required"
    | false, _ -> failwith $"not found definition for {op}"
  | ValueExpr.Unary(op, right, ty) ->
    match decls.TryGetValue op with
    | true, tyExpr ->
      match tyExpr with
      | ValueExpr.Fun(x, body, TypeExpr.Arrow(ty_x, t_result)) when ty_x = right.Type && t_result = ty ->
        let subst = substitute x right body
        eval decls subst
      | _ -> failwith $"{op} has type {ty}, but for evaluating {expr} type {expr.Type} is required"
    | false, _ -> failwith $"not found definition for {op}"
  | ValueExpr.Fun _ -> expr
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
