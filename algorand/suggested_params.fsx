#r "nuget: FsHttp"

open FsHttp

[<Measure>]
type MicroAlgo

type TransactionParametersResponse =
  { fee: uint64<MicroAlgo>
    ``genesis-id``: string
    ``genesis-hash``: string
    ``last-round``: uint64
    ``min-fee``: uint64
    ``consensus-version``: string }

let localAlgod = "http://localhost:4001"
let authToken = String.replicate 64 "a"

http {
  config_useBaseUrl localAlgod
  header "X-Algo-API-Token" authToken
  GET "/v2/transactions/params"
}
|> Request.send
|> Response.deserializeJson<TransactionParametersResponse>
|> printfn "%A"

// in order to work correctly you need to follow the instructions at
// https://developer.algorand.org/docs/get-started/algokit/#prerequisites
// until the command `algokit localnet start` executes successfully
