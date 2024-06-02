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

type DalleResponse = {created: int; data: Image list}

type Base64Png = string
let storeBase64Png (file:string) (content: Base64Png) =
  let bs = System.Convert.FromBase64String content
  System.IO.File.WriteAllBytes(file,bs)

http {
  POST "https://api.openai.com/v1/images/generations"
  AuthorizationBearer token
  config_timeoutInSeconds 90
  body

  jsonSerialize
    {| model = "dall-e-3"
       prompt = "Logo with complex but structured maze. Background suggests the form of a hedgehog. Shades of purple and violet"
       n = 1
       size = "1024x1024"
       quality = "hd"
       //response_format = "url" 
       response_format = "b64_json" |}
}
|> Request.send
//|> Response.print
//|> printfn "%s"
|> Response.expectHttpStatusCode HttpStatusCode.OK
|> function
  | Ok r ->
    match Response.deserializeJson<DalleResponse> r with
    | {data = [{b64_json = Some content }]} ->

      storeBase64Png "logo.png" content
    | img -> printfn $"No b64_json in {img}"
  | Error e -> printfn "Error: %A" e
