#r "nuget: FsToolkit.ErrorHandling"

open FsToolkit.ErrorHandling

let operation0 () =
  printfn "operation0 done"
  Some()

let operation1 () =
  printfn "operation1 failed"
  None

let operation2 () =
  printfn "operation2"
  Some()

option {
  do! operation0 ()
  do! operation1 ()
  do! operation2 ()
}

// prints
// operation0 done
// operation1 failed
