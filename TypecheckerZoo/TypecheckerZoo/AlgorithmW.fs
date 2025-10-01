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
  | Expr.Abs(var, expr) -> $"(λ{var} → {prettyExpr expr})"
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

let rec prettyType (ty: Type) =
  match ty with
  | Type.Var x -> x
  | Type.Arrow(x, y) -> $"{prettyType x} → {prettyType y}"
  | Type.Int -> "Int"
  | Type.Bool -> "Bool"
  | Type.Tuple xs -> xs |> List.map prettyType |> String.concat " * "


type QuantifiedType =
  | QuantifiedType of vars: List<string> * ty: Type // forall vars, ty

  member this.Vars =
    let (QuantifiedType(vars, _)) = this
    vars

  member this.Ty =
    let (QuantifiedType(_, ty)) = this
    ty

type TyVar = string // type variable (type variables we pass as parameters to functions)
type ExprVar = string // term variable (program variables that appear in expressions)
type ExprVars = Map<ExprVar, QuantifiedType> // term variable -> type scheme
type TypeVars = Map<TyVar, Type> // type variable -> inferred type

type InferenceNode =
  | InferenceNode of rule: string * input: string * output: string

  override this.ToString() =
    let (InferenceNode(rule, input, output)) = this
    $"{rule} {input} {output}"

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

type CounterVarState =
  | CounterVarState of counter: int * programVars: ExprVars

  member this.Counter =
    let (CounterVarState(counter, _)) = this
    counter

  member this.ProgramVars =
    let (CounterVarState(_, programVars)) = this
    programVars

type InferenceState<'a> = StateResult<'a, InferenceError, CounterVarState>

let freshTyVar: InferenceState<string> =
  stateResult {
    let! s = stateResult.Get()
    do! stateResult.Put(CounterVarState(s.Counter + 1, s.ProgramVars))
    return $"t{s.Counter}"
  }

let rec applySubst (subst: TypeVars) (ty: Type) =
  match ty with
  | Type.Var name ->
    match subst.TryGetValue name with
    | true, Type.Var n when n = name ->
      // do not fall in an infinite loop when there's progress applying the substitition
      ty
    | true, v -> applySubst subst v // ensures transitive substitution. Example `Map ["a", "b"; "b", "Int"]
    | _, _ -> ty // leave unchanged, it means at this point there's no enough information
  | Type.Arrow(t0, t1) -> Type.Arrow(applySubst subst t0, applySubst subst t1)
  | Type.Int -> ty
  | Type.Bool -> ty
  | Type.Tuple types -> types |> List.map (applySubst subst) |> Type.Tuple

let composeSubst subst0 subst1 =
  // merges subst1 into subst0. Each value of subst1 is has the type information from subst0 substituted
  subst1 |> Map.fold (fun m k v -> m |> Map.add k (applySubst m v)) subst0

let substTypeVarsInType (typeVars: TypeVars) (qType: QuantifiedType) =
  QuantifiedType(qType.Vars, applySubst typeVars qType.Ty)

let substTypeVars (typeVars: TypeVars) (env: ExprVars) =
  env |> Map.map (fun _ -> substTypeVarsInType typeVars)


let prettyMap (subst: Map<'k, 'v>) =
  []
  |> Map.foldBack (fun k v acc -> $"{k} ↦ {v}" :: acc) subst
  |> String.concat ", "

let prettySubst (subst: TypeVars) = prettyMap subst

// unification algorithm

// unify N N succeeds

// if alpha is already generalized, i.e. it doesn't belong to flexible variables in T,
// then unify(T, alpha) = Subst [ alpha, T]

// tuple unification requires component-wise unification

let rec unify t0 t1 : InferenceState<TypeVars * InferenceTree> =
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
    | Type.Var w when v = w -> stateResult { return Map.empty, newLeaf "Unify-Var-Same" input "{}" }
    | _ when occursCheck v ty -> StateResult(fun s -> Error(OccursCheck(v, ty)), s)
    | _ ->
      let subst = Map.ofList [ v, ty ]
      let output = $"{v} ↦ {ty}"
      let tree = newLeaf "Unify-Var" input output
      stateResult { return subst, tree }

  let unifyArrows ((x, y): Type * Type) ((w, z): Type * Type) =
    stateResult {
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
      StateResult(fun s -> Error(InferenceError.TupleLengthMismatch(xs.Length, ys.Length)), s)
    else
      stateResult {
        let! subst, children =
          List.zip xs ys
          |> stateResult.Fold
            (fun acc (x, y) ->
              stateResult {
                let! subst, trees = acc
                let xsSubst = applySubst subst x
                let ysSubst = applySubst subst y
                let! s, tree = unify xsSubst ysSubst
                return composeSubst s subst, tree :: trees
              })
            (StateResult(fun _ -> Ok(Map.empty, []), CounterVarState(0, Map.empty)))

        let output = prettySubst subst
        let tree = newBranch "Unify-Tuple" input output children
        return subst, tree
      }


  match t0, t1 with
  | Type.Int, Type.Int
  | Type.Bool, Type.Bool -> stateResult { return Map.empty, newLeaf "Unify-Base" input "{}" }
  | Type.Var v, ty
  | ty, Type.Var v -> unifyVars v ty
  | Type.Arrow(x, y), Type.Arrow(w, z) -> unifyArrows (x, y) (w, z)
  | Type.Tuple xs, Type.Tuple ys -> unifyTuples xs ys
  | _, _ -> StateResult(fun s -> Error(UnificationFailure(t0, t1)), s)

let prettyEnv (env: ExprVars) = prettyMap env

let generalize env ty =
  let rec freeTypeVarsScheme (scheme: QuantifiedType) =
    let schemeVars = set scheme.Vars
    let typeVars = freeTypeVars scheme.Ty
    typeVars - schemeVars

  and freeTypeVarsEnv (env: ExprVars) =
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

  QuantifiedType(freeVars, ty)

let rec instantiate (scheme: InferenceState<QuantifiedType>) : InferenceState<Type> =
  stateResult {
    let! s = scheme
    let! st = stateResult.Get()

    let! subst =
      s.Vars
      |> stateResult.Fold
        (fun (acc: InferenceState<TypeVars>) v ->
          stateResult {
            let! subst = acc
            let! fresh = freshTyVar

            let nsubst = subst |> Map.add v (Type.Var fresh)
            return nsubst
          })

        (StateResult(fun _ -> Ok Map.empty, st))

    return applySubst subst s.Ty
  }

and inferVar (st: InferenceState<unit>) (expr: Expr) name : InferenceState<TypeVars * Type * InferenceTree> =
  stateResult {
    do! st
    let! s = stateResult.Get()
    let input = $"{prettyEnv s.ProgramVars} ⊢ {expr}"

    return!
      match s.ProgramVars.TryGetValue name with
      | true, scheme ->

        stateResult {
          let! instantiated = instantiate (StateResult(fun _ -> Ok scheme, s))
          let output = $"{instantiated}"
          let tree = newLeaf "T-Var" input output
          return Map.empty, instantiated, tree
        }

      | _, _ -> StateResult(fun _ -> Error(InferenceError.UnboundVariable name), s)
  }


and inferAbs (st: InferenceState<unit>) expr (parameter: string) (body: Expr) =
  stateResult {
    do! st
    let! s = stateResult.Get()
    let input = $"{prettyEnv s.ProgramVars} ⊢ {expr} ⇒"
    let! fresh = freshTyVar
    let paramType = Type.Var fresh
    let paramScheme = QuantifiedType([], paramType)
    let newEnv = s.ProgramVars |> Map.add parameter paramScheme
    let! s0, bodyType, tree0 = infer (CounterVarState(s.Counter, newEnv)) body
    let paramTypeSubst = applySubst s0 paramType
    let resultType = Type.Arrow(paramTypeSubst, bodyType)
    let output = string resultType
    let tree = newBranch "T-Abs" input output [ tree0 ]
    return s0, resultType, tree
  }

and inferApp (st: InferenceState<unit>) expr func arg =
  stateResult {
    do! st
    let! s = stateResult.Get()
    let input = $"{prettyEnv s.ProgramVars} ⊢ {expr}"
    let! fresh = freshTyVar
    let resultType = Type.Var fresh
    let! s0, funcType, tree0 = infer s func
    let! s = stateResult.Get()
    let envSubst = substTypeVars s0 s.ProgramVars
    let! s1, argType, tree1 = infer (CounterVarState(s.Counter, envSubst)) arg

    let funcTypeSubst = applySubst s1 funcType
    let expectedFuncType = Type.Arrow(argType, resultType)

    let! s2, tree2 = unify funcTypeSubst expectedFuncType

    let finalSubst = composeSubst s2 (composeSubst s1 s0)
    let finalType = applySubst s2 resultType
    let output = string finalType
    let tree = newBranch "T-App" input output [ tree0; tree1; tree2 ]
    return finalSubst, finalType, tree
  }


and inferLet (st: CounterVarState) expr var value body =
  stateResult {
    let input = $"{prettyEnv st.ProgramVars} ⊢ {expr} ⇒"
    let! s0, valueType, tree0 = infer st value
    let envSubst = substTypeVars s0 st.ProgramVars
    let generalizedType = generalize envSubst valueType

    let newEnv = envSubst |> Map.add var generalizedType

    let! s1, bodyType, tree1 = infer (CounterVarState(st.Counter, newEnv)) body

    let finalSubst = composeSubst s1 s0
    let output = string bodyType
    let tree = newBranch "T-Let" input output [ tree0; tree1 ]
    return finalSubst, bodyType, tree
  }

and inferTuple (st: InferenceState<unit>) (expr: Expr) (exprs: Expr list) =
  stateResult {
    do! st
    let! s = stateResult.Get()
    let input = $"{prettyEnv s.ProgramVars} ⊢ {prettyExpr expr}"

    let! subst, types, trees =
      exprs
      |> stateResult.Fold
        (fun acc x ->
          stateResult {
            let! subst, types, trees = acc
            let! st = stateResult.Get()
            let! s, ty, tree = infer st x
            let nsubst = composeSubst s subst
            return nsubst, ty :: types, tree :: trees
          })
        (StateResult(fun s -> Ok(Map.empty, [], []), s))

    let resultType = Type.Tuple(List.rev types)
    let tree = newBranch "T-Tuple" input (string resultType) trees
    return subst, resultType, tree
  }

and inferLitInt (st: CounterVarState) expr =
  stateResult { return Map.empty, Type.Int, newLeaf "T-Int" $"{prettyEnv st.ProgramVars} {expr}" "Int" }

and inferLitBool (st: CounterVarState) expr =
  stateResult { return Map.empty, Type.Bool, newLeaf "T-Bool" $"{prettyEnv st.ProgramVars} {expr}" "Bool" }

and infer (cvState: CounterVarState) (expr: Expr) : InferenceState<TypeVars * Type * InferenceTree> =
  let st = StateResult(fun _ -> Ok(), cvState)

  match expr with
  | Expr.Var name ->
    stateResult {
      let! subst, ty, tree = inferVar st expr name
      return subst, ty, tree
    }

  | Expr.Abs(parameter, body) -> inferAbs st expr parameter body
  | Expr.App(func, arg) -> inferApp st expr func arg
  | Expr.Let(var, value, body) -> inferLet cvState expr var value body
  | Expr.Lit(Lit.Bool _) as expr -> inferLitBool cvState expr
  | Expr.Lit(Lit.Int _) as expr -> inferLitInt cvState expr
  | Expr.Tuple exprs -> inferTuple st expr exprs

let runInference (expr: Expr) : InferenceState<InferenceTree> =
  stateResult {
    let! _, _, tree = infer (CounterVarState(0, Map.empty)) expr
    return tree
  }

let inferTypeOnly (expr: Expr) : InferenceState<Type> =
  stateResult {
    let! _, ty, _ = infer (CounterVarState(0, Map.empty)) expr
    return ty
  }
