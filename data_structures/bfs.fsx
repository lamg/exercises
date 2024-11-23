type GetChildren<'a> =
  { get: 'a -> (GetChildren<'a> * 'a list) }

let rec bfs (gc: GetChildren<'a>, n: int, level: 'a list) =
  seq {
    yield (n, level)

    let nextLevel =
      level
      |> List.fold
        (fun (gc, xs) x ->
          let newGc, ys = gc.get x
          (newGc, xs @ ys))

        (gc, []) // initial state

    yield!
      match nextLevel with
      | _, [] -> Seq.empty
      | (chl, nl) -> bfs (chl, n + 1, nl)
  }

type Graph<'a when 'a: comparison> = Map<'a, List<'a>>

let graphChildren (g: Graph<'a>) =
  let rec children visited =
    { get =
        fun x ->
          if Set.contains x visited then
            // x is already visited, no need to mark it as visited
            (children visited, [])
          else
            let newChildren = Set.add x visited |> children

            match Map.tryFind x g with
            | Some xs -> (newChildren, xs)
            | None -> (newChildren, []) }

  children Set.empty

let g = Map [ 1, [ 2; 3; 4 ]; 2, [ 5; 6 ]; 3, [ 7; 8 ]; 4, [ 9; 10 ] ]

bfs (graphChildren g, 0, [ 1 ]) |> Seq.iter (printfn "%A")

type Tree<'a> = Node of 'a * Tree<'a> list

let rec childrenSeq (Node(_, xs)) =
  seq {
    match xs with
    | [] -> ()
    | _ ->
      let nodeValues = xs |> List.map (fun (Node(x, _)) -> x)
      yield nodeValues

    for x in xs do
      yield! childrenSeq x
  }

let treeChildren (t: Tree<'a>) =
  let chs = childrenSeq t |> Seq.toList

  let rec loop (chs: ('a list) list) =
    { get =
        fun _ ->
          match chs with
          | [] -> (loop [], [])
          | head :: tail -> (loop tail, head) }

  loop chs

let t =
  Node(
    1,
    [ Node(2, [ Node(5, []); Node(6, []) ])
      Node(3, [ Node(7, []); Node(8, []) ])
      Node(4, [ Node(9, []); Node(10, []) ]) ]
  )

bfs (treeChildren t, 0, [ 1 ]) |> Seq.iter (printfn "%A")
