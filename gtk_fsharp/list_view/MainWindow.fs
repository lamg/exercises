module Main

open Gtk

type ListViewWindow(baseBuilder: nativeint) =
  inherit Window(baseBuilder)

let commands =
  [ "open"; "close"; "run"; "help" ]
  |> List.map (fun c -> c, new Label(c))
  |> Map.ofList

let showCommands (xs: string seq) =
  xs |> Seq.iter (fun c -> commands[c].Show())

let newMainWindow () =
  let builder = new Builder("ListViewWindow.glade")
  let window = builder.GetRawOwnedObject "ListViewWindow"

  let m = new ListViewWindow(window)
  builder.Autoconnect m
  m.DeleteEvent.Add(fun _ -> Application.Quit())

  let searchList = builder.GetObject "search_list" :?> SearchEntry
  let listView = builder.GetObject "list_view" :?> ListBox

  searchList.Changed.Add(fun _ ->
    commands
    |> Map.iter (fun c lc -> if c.Contains searchList.Text then lc.Show() else lc.Hide()))

  commands.Values |> Seq.iter listView.Add
  m
