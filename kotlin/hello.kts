sealed class Tree<out T> {
    data class Leaf<T>(val value: T) : Tree<T>()
    data class Branch<T>(
      val value: T,
      val children: List<Tree<T>>,
    ) : Tree<T>()
}
  
fun <T> printTree(tree: Tree<T>): List<String> {
  fun connectIndent(isLast: Boolean, child: String, grandChildren: List<String>): List<String> {
    val childConn = if (isLast) "└── " else "├── "
    val colConn = if (isLast) "    " else "│   "
    val connected = childConn + child
    val indented = grandChildren.map { colConn + it }
    return listOf(connected) + indented
  }

  fun treeToLines(t: Tree<T>): Pair<String, List<String>> {
    return when (t) {
      is Tree.Leaf -> t.value.toString() to emptyList()
      is Tree.Branch -> {
        val root = t.value.toString()
        val children = t.children.mapIndexed { i, c ->
          val isLast = i == t.children.lastIndex
          val (childRoot, childLines) = treeToLines(c)
          connectIndent(isLast, childRoot, childLines)
        }.flatten()
        root to children
      }
    }
  }

  val (rootLine, childLines) = treeToLines(tree)
  return listOf(rootLine) + childLines
}

val tree: Tree<Int> = Tree.Branch(
  10,
  listOf(Tree.Branch(15, listOf(Tree.Leaf(12), Tree.Leaf(18))))
)

for (x in printTree(tree)) {
  println(x)
}