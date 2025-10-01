
inductive Tree (t: Type) where
| Node (v: t) (children: List (Tree t))


def Tree.size : Tree α → Nat
  | Node _ children => 1 + (children.foldl (fun acc c => acc + c.size) 0)

theorem size_lt_size_sum {c : Tree α} {children : List (Tree α)} (h : c ∈ children) :
  c.size < 1 + children.foldl (fun acc c => acc + c.size) 0 := by
  have h₁ : c.size ≤ children.foldl (fun acc c => acc + c.size) 0 := by
    -- standard lemma: if c ∈ children, then c.size ≤ sum sizes
    sorry
  apply Nat.lt_of_le_of_lt h₁
  apply Nat.lt_add_of_pos_left
  apply Nat.succ_pos


def connectIndent (isLast : Bool) (child : String) (grandChildren : List String) : List String :=
  let childConn := if isLast then "└── " else "├── "
  let colConn := if isLast then "    " else "│   "
  let connected := childConn ++ child
  let indented := grandChildren.map (· |> (colConn ++ ·))
  connected :: indented


def treeToLines [ToString t] (tree: Tree t) :=
  match tree with
  | Tree.Node v [] => (toString v, [])
  | Tree.Node v children =>
    let root := toString v
    let l := children.length

    let childrenLines :=
      children
      |> List.mapIdx (fun i c =>
        let (child, grand) := treeToLines c
        connectIndent (i == l - 1) child grand)
      |> List.flatMap id

    (root , childrenLines)

  termination_by tree.size
  decreasing_by
    simp [Tree.size]
    apply size_lt_size_sum
    sorry


def printTree [ToString α] (t : Tree α) : String :=
  let (root, children) := treeToLines t
  String.intercalate "\n" (root :: children)

#eval! println! printTree (Tree.Node 1 [Tree.Node 2 [], Tree.Node 3 []])
