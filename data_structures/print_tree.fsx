type Branch<'a, 'b> =
  { value: 'a
    children: Tree<'a, 'b> seq }

and Tree<'a, 'b> =
  | Branch of Branch<'a, 'b>
  | Leaf of 'b

type PrinterContext<'a, 'b> =
  abstract member branchToString: 'a -> string
  abstract member leafToString: 'b -> string

// the trick:
// when you are in node N, wich children XS
// connect N directly to each X in XS
// each X in XS produces a list of lines,
// indent each one and include them in the result for N

let printTree (ctx: PrinterContext<'a, 'b>) (t: Tree<'a, 'b>) =
  let connectIndent (isLast: bool) (child: string, grandChild: string list) =
    let childConn, colConn = if isLast then "└── ", "   " else "├── ", "│   "
    let connected = childConn + child
    let indented = grandChild |> List.map (fun x -> colConn + x)
    connected :: indented

  let rec treeToLines t =
    match t with
    | Branch { value = v; children = xs } ->
      let l = Seq.length xs

      let root = ctx.branchToString v

      let children =
        xs
        |> Seq.mapi (fun i c -> treeToLines c |> connectIndent (i = l - 1))
        |> Seq.concat
        |> Seq.toList

      (root, children)
    | Leaf v -> ctx.leafToString v, []

  let r, chl = treeToLines t
  r :: chl |> String.concat "\n"

type Operator =
  | And
  | Or
  | Equivales

type Identifier = string

type Expression = Tree<Operator, Identifier>

let binary op x y =
  Branch { value = op; children = [ x; y ] }

let andOp x y : Expression = binary And x y
let orOp x y : Expression = binary Or x y
let equivOp x y : Expression = binary Equivales x y


let x = Leaf "x"
let y = Leaf "y"
let z = Leaf "z"

let original = "((x ≡ y) ∨ (y ≡ z)) ∧ z"
let expr = andOp (orOp (equivOp x y) (equivOp y z)) z

let ctx =
  { new PrinterContext<Operator, Identifier> with

      member _.branchToString op =
        match op with
        | And -> "∧"
        | Or -> "∨"
        | Equivales -> "≡"

      member _.leafToString l = l }

printfn $"expression: {original}\n"
printfn $"tree:\n{printTree ctx expr}"

(*
expression: ((x ≡ y) ∨ (y ≡ z)) ∧ z

tree:
∧
├── ∨
│   ├── ≡
│   │   ├── x
│   │   └── y
│   └── ≡
│      ├── y
│      └── z
└── z
*)
