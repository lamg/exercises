module Tree


type Tree<'a> = Tree of value: 'a * children: List<Tree<'a>>
