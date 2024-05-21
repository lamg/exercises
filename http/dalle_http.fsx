#r "nuget: FsHttp"
#r "nuget: dotenv.net,3.1.3"

open System.Net
open FsHttp

dotenv.net.DotEnv.Load()
// docs at https://platform.openai.com/docs/api-reference/images/create

let token =
  System.Environment.GetEnvironmentVariable "openai_key"
  |> Option.ofObj
  |> function
    | Some x -> x
    | None -> failwith "environment variable openai_key not found"

type Image =
  { url: string option
    revised_prompt: string option
    b64_json: string option }

http {
  POST "https://api.openai.com/v1/images/generations"
  AuthorizationBearer token
  config_timeoutInSeconds 90
  body

  jsonSerialize
    {| model = "dall-e-3"
       prompt = "Logo for blog Structured Programming in F#"
       n = 1
       size = "1024x1024"
       quality = "hd"
       //response_format = "b64_json"
       response_format = "url" |}
}
|> Request.send
|> Response.print
|> printfn "%s"
// |> Response.expectHttpStatusCode HttpStatusCode.OK
// |> function
//   | Ok r ->
//     let img = Response.deserializeJson<Image>
//     printfn $"Success: {img}"
//   | Error e -> printfn "Error: %A" e
