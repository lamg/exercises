open System
open Dapper.FSharp.SQLite
open System.Data
open Microsoft.Data.Sqlite

type Migration =
  { id: int
    hash: string
    message: string
    date: DateTimeOffset
    dbFile: string }

type NewMigration =
  { hash: string
    message: string
    date: DateTimeOffset
    dbFile: string }

type Step =
  { migrationId: int
    stepIndex: int
    reason: string }

type Statement =
  { id: int
    migrationId: int
    stepIndex: int
    statementIndex: int
    sql: string }

type Error = { statementId: string; error: string }

type SqliteMaster = { sql: string }

Dapper.FSharp.SQLite.OptionTypes.register ()

let connect () =
  new SqliteConnection("Data Source=db.sqlite3")

let sqliteMaster = table'<SqliteMaster> "sqlite_master"
let migrationTable = table'<Migration> "github_com_lamg_migrate_migration"
let newMigrationTable = table'<NewMigration> "github_com_lamg_migrate_migration"

let allMigrations (conn: IDbConnection) =
  task {
    let! ms =
      select {
        for m in migrationTable do
          orderByDescending m.date
      }
      |> conn.SelectAsync<Migration>

    return ms
  }
  |> Async.AwaitTask
  |> Async.RunSynchronously
  |> Seq.toList

let schemaSql (conn: IDbConnection) =
  task {
    let! sms =
      select {
        for p in sqliteMaster do
          where (p.sql <> null && p.sql <> "")
      }
      |> conn.SelectAsync<SqliteMaster>

    return sms
  }
  |> Async.AwaitTask
  |> Async.RunSynchronously
  |> Seq.toList

let exec (conn: IDbConnection) (statements: string list) =
  let c = conn.CreateCommand()

  statements
  |> List.iter (fun s ->
    c.CommandText <- s
    c.ExecuteNonQuery() |> ignore)

let selectArb (conn: IDbConnection) (table: string) =
  let c = conn.CreateCommand()
  c.CommandText <- sprintf "SELECT * FROM %s" table
  let rd = c.ExecuteReader()

  seq {
    while rd.Read() do
      yield (rd.GetInt32 0, rd.GetString 1)
  }

let main =
  use conn = connect ()
  conn.Open()

  insert {
    into newMigrationTable

    value
      { hash = "blibli"
        message = "bla"
        date = DateTimeOffset.Now
        dbFile = "bla" }
  }
  |> conn.InsertAsync
  |> Async.AwaitTask
  |> Async.RunSynchronously
  |> ignore

  allMigrations conn |> List.iter (fun m -> printfn "%A" m)
  schemaSql conn |> List.iter (fun s -> printfn "%A" s)

  [ "CREATE TABLE IF NOT EXISTS bla(id INTEGER PRIMARY KEY, name TEXT NOT NULL)"
    "INSERT INTO bla(name) 
      VALUES(strftime('%Y-%m-%dT%H:%M:%fZ', 'now'))" ]
  |> exec conn


  selectArb conn "bla"
  |> Seq.iter (fun (id, name) -> printfn "bla: %d %s" id name)
// let c = conn.CreateCommand()

// c.CommandText <- "CREATE TABLE IF NOT EXISTS bla(id INTEGER PRIMARY KEY, name TEXT NOT NULL)"
// c.ExecuteNonQuery() |> ignore
// c.CommandText <- "INSERT INTO bla(name) VALUES('hello')"
// c.ExecuteNonQuery() |> ignore
