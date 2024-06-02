#r "nuget: GirCore.Gtk-4.0,0.5.0"

open System
open Gtk

let label () =
  let label = new Label()
  label.SetText "hello"
  label

let button (label: Label) =
  let button = new Button()
  button.SetLabel "click me"
  let mutable counter = 0

  let clickHnd (_: Button) (_: EventArgs) =
    label.SetText $"hello {counter}"
    counter <- counter + 1

  button.add_OnClicked (new GObject.SignalHandler<Button>(clickHnd))
  button

let box () =
  let box = new Box()
  box.SetOrientation Orientation.Vertical
  box.SetHomogeneous true

  let l = label ()
  box.Append l
  button l |> box.Append
  box

let onActivateApp (sender: Gio.Application) (_: EventArgs) =
  let window = ApplicationWindow.New(sender :?> Application)
  window.Title <- "Gtk4 Window"
  window.SetDefaultSize(300, 300)
  window.SetChild(box ())
  window.Show()

let application = Application.New("org.gir.core", Gio.ApplicationFlags.FlagsNone)
application.add_OnActivate (new GObject.SignalHandler<Gio.Application>(onActivateApp))
application.RunWithSynchronizationContext(null)
