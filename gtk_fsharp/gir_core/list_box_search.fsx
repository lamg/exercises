#r "nuget: GirCore.Gtk-4.0,0.5.0"

open System
open Gtk

let onSearchChanged (l: ListBox) (_: 'a) (_: EventArgs) = l.InvalidateFilter()

let onFilterInvalidate (s: SearchEntry) (row: ListBoxRow) =
  let box = row.GetChild() :?> Box
  let f = s.GetText().TrimStart().ToLower()
  let r = box.Name.ToLower()
  r.Contains f

let initSearchEntry (s: SearchEntry, l: ListBox) =
  s.add_OnSearchChanged (new GObject.SignalHandler<SearchEntry>(onSearchChanged l))

let initListBox (s: SearchEntry, l: ListBox) =
  let cmds =
    [ "Schöneberg"
      "Pankow"
      "Kreuzberg"
      "Wilmersdorf"
      "Steglitz"
      "Tempelhof"
      "Friedrichshain"
      "Köpenick"
      "Tegel"
      "Spandau" ]

  l.ShowSeparators <- true

  for c in cmds do
    let row = new Box()
    row.Name <- c
    row.SetOrientation Orientation.Horizontal
    l.Append row

    let label = new Label()
    label.SetText c
    label.SetHalign Align.Start
    label.SetProperty("hexpand", new GObject.Value(true))
    label.Selectable <- true
    row.Append label

    let image = Image.NewFromIconName "network-workgroup-symbolic"
    image.SetProperty("margin-end", new GObject.Value(5))
    image.SetValign Align.End
    row.Append image

  l.SetFilterFunc(onFilterInvalidate s)

let box () =
  let box = new Box()
  box.SetOrientation Orientation.Vertical
  box.SetHomogeneous false
  let s = new SearchEntry()
  let l = new ListBox()

  initListBox (s, l)
  initSearchEntry (s, l)
  box.Append s
  box.Append l
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
