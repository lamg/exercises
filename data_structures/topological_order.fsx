open System.Collections.Generic

// directed graph using adjacency list representation
type Graph<'a> = Dictionary<'a, HashSet<'a>>

let newGraph () = Dictionary<'a, HashSet<'a>>()

let addEdge (graph: Graph<'a>) (u: 'a, v: 'a) =
  if not (graph.ContainsKey(u)) then
    graph[u] <- HashSet<'a>()

  graph[u].Add(v) |> ignore

let topologicalSort (graph: Graph<'a>) =
  let visited = HashSet<'a>()
  let stack = Stack<'a>()

  let rec visit node =
    if not (visited.Contains(node)) then
      visited.Add node |> ignore

      if graph.ContainsKey node then
        for neighbor in graph[node] do
          visit neighbor

      stack.Push node

  for key in graph.Keys do
    visit key

  stack.ToArray() |> Array.toList


let graph = newGraph ()
[ "A", "C"; "B", "C"; "C", "D"; "D", "E" ] |> List.iter (addEdge graph)


let sorted = topologicalSort graph
printfn "Topological Sort: %A" sorted
