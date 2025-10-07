module TinyML.Expr

[<RequireQualifiedAccess>]
type TypeExpr =
  | Const of string
  | App of string * TypeExpr list
  | Arrow of TypeExpr * TypeExpr
  | Let of name: string * union: TypeExpr list

[<RequireQualifiedAccess>]
type Pattern =
  | Const of string
  | ConstFun of string * Pattern
  | Var of string
  | All

type Case = Case of pattern: Pattern * ValueExpr

and [<RequireQualifiedAccess>] ValueExpr =
  | Var of string * ty: TypeExpr
  | Const of string * ty: TypeExpr
  | ConstFun of string * ValueExpr * TypeExpr
  | Binary of string * ValueExpr * ValueExpr * ty: TypeExpr
  | Unary of string * ValueExpr * ty: TypeExpr
  | Fun of arg: string * ValueExpr * ty: TypeExpr
  | Let of var: string * ValueExpr * ValueExpr
  | Match of expr: ValueExpr * cases: Case list * ty: TypeExpr

  override this.ToString() : string =
    match this with
    | ValueExpr.Var(x, _) -> x
    | ValueExpr.Const(x, _) -> x
    | ValueExpr.ConstFun(f, arg, _) -> $"{f} {arg}"
    | ValueExpr.Binary(op, left, right, _) -> $"{left} {op} {right}"
    | ValueExpr.Unary(op, right, _) -> $"{op} {right}"
    | ValueExpr.Fun(arg, body, _) -> $"fun {arg} -> {body}"
    | ValueExpr.Let(var, valueExpr, inExpr) -> $"let {var} = {valueExpr} in {inExpr}"
    | ValueExpr.Match(expr, cases, _) ->
      let cs =
        cases
        |> List.map (fun (Case(pattern, exp)) -> $"| {pattern} -> {expr}")
        |> String.concat "\n"

      $"match {expr} with\n{cs}"

  member this.Type =
    match this with
    | Var(_, ty) -> ty
    | Const(_, ty) -> ty
    | ConstFun(_, _, ty) -> ty
    | Binary(_, _, _, ty) -> ty
    | Unary(_, _, ty) -> ty
    | Fun(_, _, ty) -> ty
    | Let(_, _, inExpr) -> inExpr.Type
    | Match(_, _, ty) -> ty
