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
        | Leaf y ->
            if x.CompareTo y < 0 then
                Node
                    { value = y
                      left = Leaf x
                      right = Leaf y }
            elif x.CompareTo y > 0 then
                Node
                    { value = y
                      left = Leaf y
                      right = Leaf x }
            else
                t
        | Node { value = y; left = l; right = r } ->
            if x.CompareTo y < 0 then
                Node { value = y; left = loop l; right = r }
            elif x.CompareTo y > 0 then
                Node { value = y; left = l; right = loop r }
            else
                t

    loop t

let tree0 = { 1..100 } |> Seq.fold insert (Leaf 0)

printfn $"tree0 (0 to 100) contains 42 = %b{contains tree0 42}"
