open Microsoft.AspNetCore.Components.WebAssembly.Hosting

[<EntryPoint>]
let main args =
  let builder = WebAssemblyHostBuilder.CreateDefault(args)
  builder.RootComponents.Add<Main.Counter>("#main")

  builder.Build().RunAsync() |> ignore
  0
