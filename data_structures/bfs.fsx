// vertices are implicit in the set of values of type 'a
type Graph<'a when 'a: comparison> = { edges: Set<'a * 'a> }

let adjacent (g: Graph<'a>) (x: 'a) =
  g.edges |> Set.filter (fun (y, _) -> x = y) |> Set.map snd

let graphLevels (startVertex: 'a) (g: Graph<'a>) =
  let rec subLevels (level: Set<'a>, visited: Set<'a>) =
    match level with
    | _ when level.IsEmpty -> []
    | _ ->
      let adj = level |> Set.map (adjacent g) |> Set.unionMany
      let newLevel = adj - visited
      let newVisited = newLevel + visited
      Set.toList level :: subLevels (newLevel, newVisited)

  subLevels (Set [ startVertex ], Set [ startVertex ])


let printLevels xs =
  xs
  |> List.iter (fun xs -> xs |> List.map _.ToString() |> String.concat "; " |> printfn "[%s]")

type KönigsbergShores =
  | Kneiphof
  | Altstadt
  | Lomse
  | Vorstadt

let königsbergBridges =
  { edges =
      Set
        [ Kneiphof, Altstadt
          Altstadt, Kneiphof
          Kneiphof, Lomse
          Kneiphof, Vorstadt
          Vorstadt, Kneiphof
          Altstadt, Lomse
          Lomse, Vorstadt ] }

königsbergBridges |> graphLevels Altstadt |> printLevels

// assumes every other natural number not in the edges is a vertex of the graph
let intGraph = { edges = Set [ 0, 1; 0, 3; 1, 2; 2, 3; 3, 0; 3, 4; 4, 5 ] }

intGraph |> graphLevels 0 |> printLevels
