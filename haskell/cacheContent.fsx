type State =
  | State of priorities: Map<int, int> * cache: Set<int>

  member this.Priorities =
    let (State(ps, _)) = this
    ps

  member this.Cache =
    let (State(_, cache)) = this
    cache

let procLog (priorities: Map<int, int>) (xs: list<int * int>) =
  let increased =
    xs
    |> List.fold
      (fun (m: Map<int, int>) (id, accesses) ->
        match m.TryGetValue id with
        | true, v -> Map.add id (v + 2 * accesses) m
        | false, _ -> Map.add id (2 * accesses) m)
      priorities

  let decreased = Set.ofSeq priorities.Keys - (Set.ofList (List.map fst xs))

  decreased
  |> Set.fold
    (fun m x ->
      Map.change
        x
        (function
        | Some v when v > 0 -> Some(v - 1)
        | Some _ -> Some 0
        | None -> None)
        m)
    increased

let chooseMap (f: int -> int -> int option) (m: Map<int, int>) =
  m |> Map.map f |> _.Values |> Seq.choose id |> Set.ofSeq

let addLogState (s: State) (xs: list<int * int>) =
  let priorities = procLog s.Priorities xs

  let toCache = priorities |> chooseMap (fun k v -> if v > 5 then Some k else None)

  let toMemory = priorities |> chooseMap (fun k v -> if v <= 3 then Some k else None)
  State(priorities, s.Cache - toMemory + toCache)

let squashLogs (xs: list<int * int>) =
  let m = Map.empty<int * int, int>

  xs
  |> List.fold
    (fun (m: Map<int * int, int>) (timestamp, id) ->
      match m.TryGetValue((timestamp, id)) with
      | true, v -> Map.add (timestamp, id) (v + 1) m
      | _, _ -> Map.add (timestamp, id) 1 m)
    m
  |> Map.toList
  |> List.map (fun ((_, id), times) -> id, times)

let cacheContents (xs: list<int * int>) =
  let s = State(Map.empty, Set.empty)
  let sq = squashLogs xs
  let r = addLogState s sq
  Set.toList r.Cache
