#r "nuget: Betalgo.OpenAI, 8.2.2"
#r "nuget: dotenv.net,3.1.3"

open OpenAI.Managers
open OpenAI.ObjectModels
open OpenAI.ObjectModels.RequestModels

dotenv.net.DotEnv.Load()

let token =
  System.Environment.GetEnvironmentVariable "openai_key"
  |> Option.ofObj
  |> function
    | Some x -> x
    | None -> failwith "environment variable openai_key not found"

let service = new OpenAIService(OpenAI.OpenAiOptions(ApiKey = token))

let req =
  new ImageCreateRequest(
    Prompt = "A hedgehog solving complex mathematical equations while traveling at the speed of light.",
    N = 1,
    Size = StaticValues.ImageStatics.Size.Size1024,
    ResponseFormat = StaticValues.ImageStatics.ResponseFormat.Url,
    User = "user-1234"
  )

req.Model <- Models.Dall_e_3
req.Quality <- StaticValues.ImageStatics.Quality.Hd

let resp =
  service.Image.CreateImage req |> Async.AwaitTask |> Async.RunSynchronously

if resp.Successful then
  let r = resp.Results[0]
  printfn $"Success: {r.Url}"
else
  printfn $"Error: {resp.Error}"
