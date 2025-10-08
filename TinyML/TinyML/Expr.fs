module TinyML.Expr

[<RequireQualifiedAccess>]
type TypeExpr =
  | Const of string
  | App of string * TypeExpr list
  | Arrow of TypeExpr * TypeExpr
  | Let of name: string * union: TypeExpr list

[<RequireQualifiedAccess>]
type Pattern =
  | Const of string * TypeExpr
  | ConstFun of string * Pattern * TypeExpr
  | Var of string * TypeExpr
  | All of TypeExpr

  member this.Type =
    match this with
    | Pattern.Const(_, ty) -> ty
    | Pattern.ConstFun(_, _, ty) -> ty
    | Pattern.Var(_, ty) -> ty
    | Pattern.All ty -> ty

  member this.DeclarationCount() =
    match this with
    | Pattern.Var _ -> 1
    | Pattern.ConstFun(_, pat, _) -> 1 + pat.DeclarationCount()
    | _ -> 0

type Case = Case of pattern: Pattern * ValueExpr

and [<RequireQualifiedAccess>] ValueExpr =
  | Var of string * ty: TypeExpr
  | Const of string * ty: TypeExpr
  | ConstFun of string * ValueExpr * TypeExpr
  | App of string * ValueExpr * TypeExpr
  | Fun of pat: Pattern * body: ValueExpr * ty: TypeExpr
  | Let of var: string * ValueExpr * ValueExpr
  | Match of expr: ValueExpr * cases: Case list * ty: TypeExpr

  override this.ToString() : string =
    match this with
    | ValueExpr.Var(x, _) -> x
    | ValueExpr.Const(x, _) -> x
    | ValueExpr.ConstFun(f, arg, _) -> $"{f} {arg}"
    | ValueExpr.App(f, arg, _) -> $"{f} {arg}"
    | ValueExpr.Fun(arg, body, _) -> $"fun {arg} -> {body}"
    | ValueExpr.Let(var, valueExpr, inExpr) -> $"let {var} = {valueExpr} in {inExpr}"
    | ValueExpr.Match(expr, cases, _) ->
      let cs =
        cases
        |> List.map (fun (Case(pattern, guardedExpr)) -> $"| {pattern} -> {guardedExpr}")
        |> String.concat "\n"

      $"match {expr} with\n{cs}"

  member this.Type =
    match this with
    | Var(_, ty) -> ty
    | Const(_, ty) -> ty
    | ConstFun(_, _, ty) -> ty
    | App(_, _, ty) -> ty
    | Fun(_, _, ty) -> ty
    | Let(_, _, inExpr) -> inExpr.Type
    | Match(_, _, ty) -> ty
