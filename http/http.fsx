#r "nuget: FsHttp"

open System.Net
open FsHttp

http {
    POST "http://addr.com/api/generate"
    config_timeoutInSeconds 90
    body

    jsonSerialize
        {| model = "orca2"
           prompt = "who are you" |}
}
|> Request.send
|> Response.expectHttpStatusCode HttpStatusCode.OK
|> function
    | Ok r -> printfn $"Success: {r.content.ReadAsStringAsync().Result}"
    | Error e -> printfn "Error: %A" e
