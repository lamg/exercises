// the trick:
// each node must be connected directly to its direct children (with visible characters)
// and indirectly (through indentation) to its children's descendants

type Tree<'a> =
  | Leaf of 'a
  | Branch of 'a * list<Tree<'a>>

let printTree (t: Tree<'a>) =
  let connectIndent (isLast: bool) (child: string, grandChild: string list) =
    let childConn, colConn = if isLast then "└── ", "   " else "├── ", "│   "
    let connected = childConn + child
    let indented = grandChild |> List.map (fun x -> colConn + x)
    connected :: indented

  let rec treeToLines t =
    match t with
    | Branch(v, xs) ->
      let l = Seq.length xs

      let root = v.ToString()

      let children =
        xs
        |> List.mapi (fun i c -> treeToLines c |> connectIndent (i = l - 1))
        |> List.concat

      root, children
    | Leaf v -> v.ToString(), []

  let r, chl = treeToLines t
  r :: chl

let tree = Branch(10, [ Branch(15, [ Leaf 12; Leaf 18 ]) ])

for x in printTree tree do
  printfn $"{x}"
