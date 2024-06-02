[<EntryPoint>]
let main _ =
  let application =
    Gtk.Application.New("org.gir.core", Gio.ApplicationFlags.FlagsNone)

  let f (sender: Gio.Application) (_: System.EventArgs) =
    let window = Gtk.ApplicationWindow.New(sender :?> Gtk.Application)
    window.Title <- "Gtk4 Window"
    window.SetDefaultSize(300, 300)
    window.Show()

  let g = new GObject.SignalHandler<Gio.Application>(f)

  application.add_OnActivate g

  application.RunWithSynchronizationContext(null)
