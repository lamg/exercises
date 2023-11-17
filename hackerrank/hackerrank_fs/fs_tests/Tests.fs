module Tests

open Xunit

[<Fact>]
let diagonalTest () =
    Assert.Equal<int list>([ 1; 5; 9 ], Problems.FsProblems.firstDiagonal)
    Assert.Equal<int list>([ 3; 5; 7 ], Problems.FsProblems.secondDiagonal)
