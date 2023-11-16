# How to improve error messages in the F# compiler

## Setup

```sh
git clone git@github.com:dotnet/fsharp.git
cd fsharp
dotnet restore FSharp.Compiler.Service.sln
```

## A debugging session

- Open with your IDE the `Fsharp.Compiler.Service` solution
- Open the file `FSComp.txt`. It contains error codes associated to error messages. 
- Let's run now the `fsi` project in debugging mode. A terminal executing the F# interpreter should appear.
- type the expression `"a" 0`. This should show a message like 
`This value is not a function and cannot be applied`, which we can find in `FSComp.txt`.
- the error code associated to that message is `notAFunction`. It appears in the file `CheckExpression.fs`.
- Let's put a break point there, in a line similar to `error (NotAFunction(denv, overallTy.Commit, mExpr, mArg))`.
- Now type again `"a" 0` in the interpreter. In case it doesn't hit the break point,
then put another one in a line similar to the one above, since there are several.
Then type again `"a" 0` until you find the right one.
- Once the execution reaches the break point you can inspect the value of `expr`,
which contains useful information to make better error messages.

For more detailed walkthroughs:

- https://amplifying-fsharp.github.io/sessions/2023/09/01/
- https://amplifying-fsharp.github.io/sessions/2023/06/02/
- https://amplifying-fsharp.github.io/sessions/2023/05/17/
