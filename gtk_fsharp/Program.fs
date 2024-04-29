open System
open Gtk

[<EntryPoint>]
let main args =
  Application.Init()
  let app = new Application("org.interacto.interacto", GLib.ApplicationFlags.None)
  app.Register(GLib.Cancellable.Current) |> ignore
  let win = Main.newMainWindow ()
  app.AddWindow(win)
  win.Show()
  Application.Run()
  0
