module Tree


type Tree<'a> = Tree of value: 'a * children: List<Tree<'a>>

let printTree (t: Tree<'a>) =
  let connectIndent (isLast: bool) (child: string, grandChild: string list) =
    let childConn, colConn = if isLast then "└── ", "   " else "├── ", "│   "
    let connected = childConn + child
    let indented = grandChild |> List.map (fun x -> colConn + x)
    connected :: indented

  let rec treeToLines t =
    let (Tree(v, children)) = t

    match children with
    | [] -> string v, []

    | _ ->
      let l = Seq.length children
      let root = string v

      let childrenLines =
        children
        |> List.mapi (fun i c -> treeToLines c |> connectIndent (i = l - 1))
        |> List.concat

      root, childrenLines

  let r, chl = treeToLines t
  r :: chl |> String.concat "\n"
