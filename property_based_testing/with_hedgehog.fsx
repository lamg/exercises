#r "nuget: Hedgehog, 0.13.0"
#r "nuget: Microsoft.Data.Sqlite"

open Hedgehog
open Microsoft.Data.Sqlite

let propReverse: Property<bool> =
  property {
    let! xs = Gen.list (Range.linear 0 100) Gen.alpha
    return xs |> List.rev |> List.rev = xs
  }

let r = Property.renderBool propReverse
printfn $"result = {r}"

let createDb (dbFile: string) =
  let conn = new SqliteConnection($"Data Source={dbFile};Mode=ReadWriteCreate;")
  conn.Open()
  let cmd = conn.CreateCommand()
  cmd.CommandText <- "CREATE TABLE IF NOT EXISTS users (id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL)"
  cmd.ExecuteNonQuery() |> ignore
  conn

let propInsert () =
  let dbFile = "test_db.sqlite3"
  use conn = createDb dbFile

  property {
    let cmd = conn.CreateCommand()
    let! name = Gen.string (Range.linear 0 100) Gen.alpha
    cmd.CommandText <- $"INSERT INTO users (name) VALUES ('{name}')"
    cmd.ExecuteNonQuery() |> ignore
    cmd.CommandText <- "SELECT COUNT(*) FROM users"
    let count = cmd.ExecuteScalarAsync() |> Async.AwaitTask |> Async.RunSynchronously
    return count = 1L
  }

let propInsertTx () =
  let dbFile = "test_db.sqlite3"
  use conn = createDb dbFile

  property {
    conn.Open()
    use tx = conn.BeginTransaction()
    let cmd = conn.CreateCommand()
    let! name = Gen.string (Range.linear 0 100) Gen.alpha
    cmd.CommandText <- $"INSERT INTO users (name) VALUES ('{name}')"
    cmd.ExecuteNonQuery() |> ignore
    tx.Commit() |> ignore
    cmd.CommandText <- "SELECT COUNT(*) FROM users"
    let count = cmd.ExecuteScalarAsync() |> Async.AwaitTask |> Async.RunSynchronously
    return count = 1L
  }

// measure time
let time f =
  let sw = System.Diagnostics.Stopwatch.StartNew()
  let r = f ()
  sw.Stop()
  printfn $"time = {sw.ElapsedMilliseconds}ms"
  r

time (fun () -> Property.renderBool (propInsert ()))
time (fun () -> Property.renderBool (propInsertTx ()))

// propInsert: 96ms
// propInsertTx: 9ms
// => transaction is faster
