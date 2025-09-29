module AlgorithmW

open Tree
open Monads

let log (s: string) =
  System.IO.File.AppendAllText("algorithw.log", $"{s}\n")

// Lambda calculus three syntactic constructions (Var, Abs and App)
// the additional constructions are added to make easier to the expression of
// common patterns

[<RequireQualifiedAccess>]
type Expr =
  | Var of string // x
  | Abs of string * Expr // (fun x -> EXPR)
  | App of Expr * Expr // f x
  | Let of string * Expr * Expr
  | Lit of Lit
  | Tuple of List<Expr>

and [<RequireQualifiedAccess>] Lit =
  | Int of int
  | Bool of bool

let rec prettyExpr (expr: Expr) =
  match expr with
  | Expr.Var name -> name
  | Expr.Abs(var, expr) -> $"λ{var} → {prettyExpr expr}"
  | Expr.App(f, x) -> $"{prettyExpr f} {prettyExpr x}"
  | Expr.Let(var, expr, inExpr) -> $"let {var} = {prettyExpr expr} in {prettyExpr inExpr}"
  | Expr.Lit(Lit.Int n) -> string n
  | Expr.Lit(Lit.Bool b) -> string b
  | Expr.Tuple ts ->
    let body = ts |> List.map prettyExpr |> String.concat ", "
    $"({body})"

// Alpha equivalence: the name of a bound variable is irrelevant, i.e. a
// name like x in the following expression can be replaced by any other: (fun x -> x + 1)

// Type checking rules

// x - variable
// T - type variable
// N - concrete type
// G - a particular set of typed variables (like the one you have when you're implementing a function
// or evaluating expressions in an interpreter)
// alhpa - a placeholder for a concrete type to be calculated during unification

// T-Var if x:T belongs to G, and N is an instance of T, then G proves that x can have type N

// T-Lam if x:alpha belongs to G, and e:N, then G proves that (fun x -> e): alpha -> N

// T-App if G proves that e0:N0 and e1:N1, and we can unify the type N0 with `N1 -> alpha`, then
// e0 e1: N3, where N3 is the concrete type calculated during unification for the unknown alpha

// T-Let if G proves that e0:N0, generalize all components alpha of N0, i.e. e0:(forall alpha, N0),
// and if G proves that e1:N1, then `let x = e0 in e1: N1`

[<RequireQualifiedAccess>]
type Type =
  | Var of string
  | Arrow of Type * Type
  | Int
  | Bool
  | Tuple of List<Type>

type Scheme =
  | Scheme of vars: List<string> * ty: Type // forall vars, ty

  member this.Vars =
    let (Scheme(vars, _)) = this
    vars

  member this.Ty =
    let (Scheme(_, ty)) = this
    ty

type TyVar = string // type variable
type TmVar = string // term variable (program variables that appear in expressions)
type Env = Map<TmVar, Scheme> // term variable -> type scheme
type Subst = Map<TyVar, Type> // type variable -> inferred type

type InferenceNode = InferenceNode of rule: string * input: string * output: string
type InferenceTree = Tree<InferenceNode>

let newLeaf rule input output : InferenceTree =
  Tree(InferenceNode(rule, input, output), [])

let newBranch rule input output children : InferenceTree =
  Tree(InferenceNode(rule, input, output), children)


type InferenceError =
  | UnificationFailure of expected: Type * actual: Type
  | OccursCheck of var: string * ty: Type
  | TupleLengthMismatch of lengthLeft: int * lengthRight: int
  | UnboundVariable of string

type InferenceState =
  | InferenceState of counter: int * programVars: Env

  member this.Counter =
    let (InferenceState(counter, _)) = this
    counter

  member this.ProgramVars =
    let (InferenceState(_, programVars)) = this
    programVars

  member this.freshTyVar() =
    $"t{this.Counter}", InferenceState(this.Counter + 1, this.ProgramVars)

let rec applySubst (subst: Subst) (ty: Type) =
  match ty with
  | Type.Var name ->
    match subst.TryGetValue name with
    | true, v -> applySubst subst v // ensures transitive substitution. Example `Map ["a", "b"; "b", "Int"]
    | false, _ -> ty // leave unchanged, it means at this point there's no enough information
  | Type.Arrow(t0, t1) -> Type.Arrow(applySubst subst t0, applySubst subst t1)
  | Type.Int -> ty
  | Type.Bool -> ty
  | Type.Tuple types -> types |> List.map (applySubst subst) |> Type.Tuple

let composeSubst subst0 subst1 =
  // merges subst1 into subst0. Each value of subst1 is has the type information from subst0 substituted
  subst1 |> Map.fold (fun m k v -> m |> Map.add k (applySubst m v)) subst0

let applySubstScheme (subst: Subst) (scheme: Scheme) =
  let filteredSubst =
    scheme.Vars |> List.fold (fun (acc: Subst) x -> acc.Remove x) subst

  Scheme(scheme.Vars, applySubst filteredSubst scheme.Ty)

let applySubstEnv (subst: Subst) (env: Env) =
  env |> Map.map (fun _ v -> applySubstScheme subst v)


let prettyMap (subst: Map<'k, 'v>) =
  []
  |> Map.foldBack (fun k v acc -> $"{k} |-> {v}" :: acc) subst
  |> String.concat ", "

let prettySubst (subst: Subst) = prettyMap subst

// unification algorithm

// unify N N succeeds

// if alpha is already generalized, i.e. it doesn't belong to flexible variables in T,
// then unify(T, alpha) = Subst [ alpha, T]

// tuple unification requires component-wise unification

let rec unify t0 t1 : Result<Subst * InferenceTree, InferenceError> =
  let input = $"{t0} {t1}"

  // prevents infinite types by ensuring that a type variable doesn’t appear within the type it’s being unified with.
  let rec occursCheck (v: string) (ty: Type) =
    match ty with
    | Type.Var v' -> v = v'
    | Type.Arrow(t0, t1) -> occursCheck v t0 || occursCheck v t1
    | Type.Tuple ts -> ts |> List.exists (occursCheck v)
    | _ -> false

  let unifyVars (v: string) (ty: Type) =
    match ty with
    | Type.Var w when v = w -> Ok(Map.empty, newLeaf "Unify-Var-Same" input "{}")
    | _ when occursCheck v ty -> Error(OccursCheck(v, ty))
    | _ ->
      let subst = Map.ofList [ v, ty ]
      let output = $"{v} |-> {ty}"
      let tree = newLeaf "Unify-Var" input output
      Ok(subst, tree)

  let unifyArrows ((x, y): Type * Type) ((w, z): Type * Type) =
    result {
      let! s0, children0 = unify x w
      let ySubst = applySubst s0 y
      let zSubst = applySubst s0 z
      let! s1, children1 = unify ySubst zSubst
      let finalSubst = composeSubst s1 s0
      let output = prettySubst finalSubst
      let tree = newBranch "Unify-Arrow" input output [ children0; children1 ]

      return finalSubst, tree
    }


  let unifyTuples (xs: List<Type>) (ys: List<Type>) =
    if xs.Length <> ys.Length then
      Error(InferenceError.TupleLengthMismatch(xs.Length, ys.Length))
    else
      result {
        let! subst, children =
          List.zip xs ys
          |> result.fold
            (fun (subst, trees) (x, y) ->
              result {
                let xsSubst = applySubst subst x
                let ysSubst = applySubst subst y
                let! s, tree = unify xsSubst ysSubst
                return composeSubst s subst, tree :: trees
              })
            (Map.empty, [])

        let output = prettySubst subst
        let tree = newBranch "Unify-Tuple" input output children
        return subst, tree
      }


  match t0, t1 with
  | Type.Int, Type.Int
  | Type.Bool, Type.Bool -> Ok(Map.empty, newLeaf "Unify-Base" input "{}")
  | Type.Var v, ty
  | ty, Type.Var v -> unifyVars v ty
  | Type.Arrow(x, y), Type.Arrow(w, z) -> unifyArrows (x, y) (w, z)
  | Type.Tuple xs, Type.Tuple ys -> unifyTuples xs ys
  | _, _ -> Error(UnificationFailure(t0, t1))

let prettyEnv (env: Env) = prettyMap env

let generalize env ty =
  let rec freeTypeVarsScheme (scheme: Scheme) =
    let schemeVars = set scheme.Vars
    let typeVars = freeTypeVars scheme.Ty
    typeVars - schemeVars

  and freeTypeVarsEnv (env: Env) =
    env.Values |> Seq.map (freeTypeVarsScheme >> set) |> Set.unionMany

  and freeTypeVars ty =
    match ty with
    | Type.Var name -> set [ name ]
    | Type.Arrow(t0, t1) -> Set.union (freeTypeVars t0) (freeTypeVars t1)
    | Type.Tuple ts -> ts |> List.map freeTypeVars |> Set.unionMany
    | Type.Int
    | Type.Bool -> set []

  let freeVars =
    Set.difference (freeTypeVars ty) (freeTypeVarsEnv env)
    |> Set.toList
    |> List.sort

  Scheme(freeVars, ty)

let rec infer (st: InferenceState) (expr: Expr) : Result<Subst * Type * InferenceTree, InferenceError> =
  let mutable st = st

  let instantiate (scheme: Scheme) =
    let mutable subst = Map.empty

    for v in scheme.Vars do
      let fresh, newSt = st.freshTyVar ()
      subst <- subst |> Map.add v (Type.Var fresh)
      st <- newSt

    applySubst subst scheme.Ty

  let inferVar (expr: Expr) name =
    let input = $"{prettyEnv st.ProgramVars} |- {expr}"

    match st.ProgramVars.TryGetValue name with
    | true, scheme ->
      let instantiated = instantiate scheme
      let output = $"{instantiated}"
      let tree = newLeaf "T-Var" input output
      Ok(Map.empty, instantiated, tree)
    | _, _ -> Error(InferenceError.UnboundVariable name)

  let inferAbs expr (parameter: string) (body: Expr) =
    let input = $"{prettyEnv st.ProgramVars} |- {expr} =>"
    let fresh, newSt = st.freshTyVar ()
    st <- newSt

    log $"abs {prettyExpr expr}"
    let paramType = Type.Var fresh
    let paramScheme = Scheme([], paramType)
    let newEnv = st.ProgramVars |> Map.add parameter paramScheme

    result {
      let! s0, bodyType, tree0 = infer (InferenceState(st.Counter, newEnv)) body
      let paramTypeSubst = applySubst s0 paramType
      let resultType = Type.Arrow(paramTypeSubst, bodyType)
      let output = string resultType
      let tree = newBranch "T-Abs" input output [ tree0 ]
      return s0, resultType, tree
    }

  let inferApp expr func arg =
    result {
      let input = $"{prettyEnv st.ProgramVars} |- {expr}"
      let fresh, newSt = st.freshTyVar ()
      st <- newSt
      let resultType = Type.Var fresh
      let! s0, funcType, tree0 = infer st func
      let envSubst = applySubstEnv s0 st.ProgramVars
      let! s1, argType, tree1 = infer (InferenceState(st.Counter, envSubst)) arg

      let funcTypeSubst = applySubst s1 funcType
      let expectedFuncType = Type.Arrow(argType, resultType)

      let! s2, tree2 = unify funcTypeSubst expectedFuncType

      let finalSubst = composeSubst s2 (composeSubst s1 s0)
      let finalType = applySubst s2 resultType
      let output = string finalType
      let tree = newBranch "T-App" input output [ tree0; tree1; tree2 ]
      return finalSubst, finalType, tree
    }


  let inferLet expr var value body =
    result {
      let input = $"{prettyEnv st.ProgramVars} |- {expr} =>"
      let! s0, valueType, tree0 = infer st value
      let envSubst = applySubstEnv s0 st.ProgramVars
      let generalizedType = generalize envSubst valueType

      let newEnv = envSubst |> Map.add var generalizedType

      let! s1, bodyType, tree1 = infer (InferenceState(st.Counter, newEnv)) body

      let finalSubst = composeSubst s1 s0
      let output = string bodyType
      let tree = newBranch "T-Let" input output [ tree0; tree1 ]
      return finalSubst, bodyType, tree
    }

  let inferTuple expr exprs = failwith "not"

  let inferLitInt expr =
    Ok(Map.empty, Type.Int, newLeaf "T-Int" $"{prettyEnv st.ProgramVars} {expr}" "Int")

  let inferLitBool expr =
    Ok(Map.empty, Type.Bool, newLeaf "T-Bool" $"{prettyEnv st.ProgramVars} {expr}" "Bool")

  log $"expr {prettyExpr expr}"

  match expr with
  | Expr.Var name -> inferVar expr name
  | Expr.Abs(parameter, body) -> inferAbs expr parameter body
  | Expr.App(func, arg) -> inferApp expr func arg
  | Expr.Let(var, value, body) -> inferLet expr var value body
  | Expr.Lit(Lit.Bool _) as expr -> inferLitBool expr
  | Expr.Lit(Lit.Int _) as expr -> inferLitInt expr
  | Expr.Tuple exprs -> inferTuple expr exprs

let runInference (expr: Expr) =
  result {
    let! _, _, tree = infer (InferenceState(0, Map.empty)) expr
    return tree
  }

let inferTypeOnly (expr: Expr) =
  result {
    let! _, ty, _ = infer (InferenceState(0, Map.empty)) expr
    return ty
  }
