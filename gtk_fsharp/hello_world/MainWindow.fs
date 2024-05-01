module Main

open Gtk

type MainWindow(baseBuilder: nativeint) =
  inherit Window(baseBuilder)

let newMainWindow () =
  let builder = new Builder("MainWindow.glade")
  let window = builder.GetRawOwnedObject "MainWindow"

  let m = new MainWindow(window)
  builder.Autoconnect m
  m.DeleteEvent.Add(fun _ -> Application.Quit())

  let mutable _label1 = builder.GetObject "_label1" :?> Label

  let mutable _button1 = builder.GetObject "_button1" :?> Button

  let mutable _counter = 0

  _button1.Clicked.Add(fun _ ->
    _counter <- _counter + 1
    _label1.Text <- $"This button has been clicked {_counter}")

  m
