#r "nuget: GirCore.Gtk-4.0,0.5.0"
#r "nuget: GirCore.GtkSource-5, 0.5.0"

open System
open Gtk
open GtkSource

[<Literal>]
let exampleText =
  "
**Verse 1:**
In the shadows, where the echoes lie,
A silent scream beneath a starless sky.
Whispers of a life that never came,
Trapped in the darkness, bound by shame.

**Pre-Chorus:**
Veins of sorrow in a fractured mind,
Pieces of a soul, too hard to find.
Ghosts of promises turned to dust,
Lost in the silence of broken trust.

**Chorus:**
Blackest eyes, they never lie,
Windows to a world where angels cry.
Behind the mask, a void of pain,
In the blackest eyes, the scars remain.
"

let sourceView () =
  Module.Initialize()
  let buf = Buffer.New(null)

  let view = GtkSource.View.NewWithBuffer(buf)
  view.Monospace <- true
  view.ShowLineNumbers <- true
  let m = LanguageManager.New()
  m.GetLanguage("markdown") |> buf.SetLanguage
  buf.Text <- exampleText
  view

let listBox () =
  let l = new ListBox()

  let items =
    [ "Schöneberg", "a nice place"
      "Pankow", "a beautiful place"
      "Kreuzberg", "a fun place"
      "Wilmersdorf", "a quiet place"
      "Steglitz", "a far away place"
      "Tempelhof", "an open place"
      "Friedrichshain", "a hippster place"
      "Köpenick", "where the rivers meet"
      "Tegel", "an old place"
      "Spandau", "an empty place" ]

  for main, descr in items do
    let mainLabel = new Label()
    mainLabel.SetText main
    mainLabel.SetHalign Align.Start
    mainLabel.SetValign Align.Start
    mainLabel.SetHexpand true
    mainLabel.SetVexpand true
    mainLabel.SetWrap true
    mainLabel.SetMarginBottom 10
    mainLabel.AddCssClass "main"

    let descrLabel = new Label()
    descrLabel.SetText descr
    descrLabel.SetEllipsize Pango.EllipsizeMode.End
    descrLabel.SetHalign Align.Start
    descrLabel.SetValign Align.End
    descrLabel.SetHexpand true
    descrLabel.SetVexpand false
    descrLabel.SetMarginBottom 10
    descrLabel.AddCssClass "description"

    let item = new Box()
    item.Name <- main

    item.SetOrientation Orientation.Vertical
    item.Append mainLabel
    item.Append descrLabel
    l.Append item

  let onActivate (l: ListBox) (e: ListBox.RowActivatedSignalArgs) =

    printfn $"activated {e.Row.Child.Name} row"

  l.add_OnRowActivated (GObject.SignalHandler<ListBox, ListBox.RowActivatedSignalArgs> onActivate)
  l.GrabFocus() |> ignore
  l

let fontButton () =
  let box = new Box()
  box.SetOrientation Orientation.Vertical
  box.SetHomogeneous true

  let font = new FontButton()

  let onFontSet _ _ =
    printfn $"selected font = {font.FontDesc.GetFamily()} {font.FontDesc.GetVariant()} {font.FontDesc.GetWeight()}"

  font.add_OnFontSet (GObject.SignalHandler<FontButton> onFontSet)

  let check = new CheckButton()

  let onToggled (c: CheckButton) _ = printfn $"toggled {c.Active}"
  check.add_OnToggled (GObject.SignalHandler<CheckButton> onToggled)

  let toggle = new ToggleButton()

  let onToggleToggle (t: ToggleButton) _ =
    if t.Active then
      t.Label <- "active"
    else
      t.Label <- "inactive"

    printfn $"toggled {t.Active}"

  toggle.add_OnToggled (GObject.SignalHandler<ToggleButton> onToggleToggle)

  box.Append font
  box.Append check
  box.Append toggle
  box

let newControls () =
  [ listBox () :> Widget; sourceView (); fontButton () ]

let gallery () =
  let stack = new Stack()

  newControls ()
  |> List.iter (fun c ->
    let name = c.GetType().FullName
    stack.AddTitled(c, name, name) |> ignore)

  let switcher = new StackSwitcher()
  switcher.SetStack stack

  let box = new Box()
  box.SetOrientation Orientation.Vertical
  box.SetHomogeneous false
  box.Append switcher
  box.Append stack
  box

let onActivateApp (sender: Gio.Application) (_: EventArgs) =
  let window = ApplicationWindow.New(sender :?> Application)
  let css = CssProvider.New()
  //css.LoadFromPath "gallery.css"
  css.LoadFromString
    "
.main {
    color: #000000;
    font-weight: normal;
}

.description {
    color: #a8a1a0;
    font-weight: normal;
    font-style: italic;
}"

  StyleContext.AddProviderForDisplay(Gdk.Display.GetDefault(), css, 1ul)
  window.Title <- "Gallery of GTK4 controls"
  window.SetDefaultSize(800, 600)
  window.SetChild(gallery ())
  window.Show()

let application = Application.New("org.gir.core", Gio.ApplicationFlags.FlagsNone)
application.add_OnActivate (new GObject.SignalHandler<Gio.Application>(onActivateApp))
application.RunWithSynchronizationContext(null)
