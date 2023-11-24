open Gtk

[<EntryPoint>]
let main argv =
    Application.Init()

    let app = new Application("org.gtk_sharp_experiment.gtk_sharp_experiment", GLib.ApplicationFlags.None)
    app.Register(GLib.Cancellable.Current) |> ignore;

    let win = new Main.MainWindow()
    app.AddWindow(win)

    win.Show()
    Application.Run()
    0
