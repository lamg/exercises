open System
open Gtk
open GtkSource

// steps to reproduce

// execute
// dotnet publish -c release
// bin/release/net8.0/source

// output
// UnhandledException - unhandled exception: System.DllNotFoundException: Unable to load shared library 'GtkSource' or
// one of its dependencies. In order to help diagnose loading problems, consider using a tool like strace. If you're using glibc, consider setting the LD_DEBUG environment variable

// execute
// export LD_DEBUG='libs bin/release/net8.0/source'
// bin/release/net8.0/source 2> result.txt

// output file result.txt
// it shows the program is looking for /usr/lib/x86_64-linux-gnu/libGtkSource.so
// it should be looking for libgtksourceview-5.so instead

let sourceView () =
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

[<EntryPoint>]
let main _ =
  let application = Application.New("org.gir.core", Gio.ApplicationFlags.FlagsNone)
  application.add_OnActivate (new GObject.SignalHandler<Gio.Application>(onActivateApp))
  application.RunWithSynchronizationContext(null)
