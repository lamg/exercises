#r "nuget: GirCore.Gtk-4.0,0.5.0"
#r "nuget: GirCore.GtkSource-5, 0.5.0"

open System
open Gtk
open GtkSource

let sourceView () =
  Module.Initialize()
  let buf = Buffer.New(null)

  let view = GtkSource.View.NewWithBuffer(buf)
  view.Monospace <- true
  view.ShowLineNumbers <- true
  let m = LanguageManager.New()
  m.GetLanguage("markdown") |> buf.SetLanguage

  view

let box () =
  let box = new Box()
  box.SetOrientation Orientation.Vertical
  box.SetHomogeneous false

  sourceView () |> box.Append
  box

let onActivateApp (sender: Gio.Application) (_: EventArgs) =
  let window = ApplicationWindow.New(sender :?> Application)
  window.Title <- "ListBox search example"
  window.SetDefaultSize(800, 600)
  window.SetChild(box ())
  window.Show()

let application = Application.New("org.gir.core", Gio.ApplicationFlags.FlagsNone)
application.add_OnActivate (new GObject.SignalHandler<Gio.Application>(onActivateApp))
application.RunWithSynchronizationContext(null)
