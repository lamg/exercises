open System

type Node<'a when 'a :> IComparable> =
    { value: 'a
      left: 'a BinaryTree
      right: 'a BinaryTree }

and BinaryTree<'a when 'a :> IComparable> =
    | Leaf of 'a
    | Node of 'a Node

let contains (t: 'a BinaryTree) (x: 'a) =
    let rec loop (t: 'a BinaryTree) =
        match t with
        | Leaf y -> x = y
        | Node { value = y; left = l } when x.CompareTo y < 0 -> loop l
        | Node { value = y; right = r } when x.CompareTo y > 0 -> loop r
        | _ -> true

    loop t

let insert (t: 'a BinaryTree) (x: 'a) =
    let rec loop t =
        match t with
        | Leaf y when x.CompareTo y < 0 ->
            Node
                { value = y
                  left = Leaf x
                  right = Leaf y }
        | Leaf y when x.CompareTo y > 0 ->
            Node
                { value = y
                  left = Leaf y
                  right = Leaf x }
        | Node({ value = y; left = l } as n) when x.CompareTo y < 0 -> Node { n with left = loop l }
        | Node({ value = y; right = r } as n) when x.CompareTo y > 0 -> Node { n with right = loop r }
        | _ -> t

    loop t

let tree0 = { 1..100 } |> Seq.fold insert (Leaf 0)

printfn $"tree0 (0 to 100) contains 42 = %b{contains tree0 42}"
