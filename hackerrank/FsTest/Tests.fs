module Tests

open Problems
open Xunit

[<Fact>]
let diagonalTest () =
  Assert.Equal<int list>([ 1; 5; 9 ], FsProblems.firstDiagonal)
  Assert.Equal<int list>([ 3; 5; 7 ], FsProblems.secondDiagonal)
