namespace bolero.Server

open Microsoft.AspNetCore
open Microsoft.AspNetCore.Authentication.Cookies
open Microsoft.AspNetCore.Builder
open Microsoft.AspNetCore.Hosting
open Microsoft.Extensions.DependencyInjection
open Microsoft.Extensions.Hosting
open Bolero
open Bolero.Remoting.Server
open Bolero.Server
open bolero
open Bolero.Templating.Server

type Startup() =

  // This method gets called by the runtime. Use this method to add services to the container.
  // For more information on how to configure your application, visit https://go.microsoft.com/fwlink/?LinkID=398940
  member this.ConfigureServices(services: IServiceCollection) =
    services.AddMvc() |> ignore
    services.AddServerSideBlazor() |> ignore

    services
      .AddAuthorization()
      .AddAuthentication(CookieAuthenticationDefaults.AuthenticationScheme)
      .AddCookie()
      .Services.AddBoleroRemoting<BookService>()
      .AddBoleroHost()
#if DEBUG
      .AddHotReload(templateDir = __SOURCE_DIRECTORY__ + "/../client")
#endif
    |> ignore

  // This method gets called by the runtime. Use this method to configure the HTTP request pipeline.
  member this.Configure(app: IApplicationBuilder, env: IWebHostEnvironment) =
    if env.IsDevelopment() then
      app.UseWebAssemblyDebugging()

    app
      .UseAuthentication()
      .UseStaticFiles()
      .UseRouting()
      .UseAuthorization()
      .UseBlazorFrameworkFiles()
      .UseEndpoints(fun endpoints ->
#if DEBUG
        endpoints.UseHotReload()
#endif
        endpoints.MapBoleroRemoting() |> ignore
        endpoints.MapBlazorHub() |> ignore
        endpoints.MapFallbackToBolero(Index.page) |> ignore)
    |> ignore

module Program =

  [<EntryPoint>]
  let main args =
    WebHost
      .CreateDefaultBuilder(args)
      .UseStaticWebAssets()
      .UseStartup<Startup>()
      .Build()
      .Run()

    0
