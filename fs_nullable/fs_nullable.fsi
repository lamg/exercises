#r "CsNullable/bin/Debug/net9.0/CsNullable.dll"

open CsNullable;
let maybeAValue: string | null = Nullable.CsString()

let safeLen (str: string | null) =
    match str with
    | null -> -1
    | s -> s.Length

printfn $"{safeLen maybeAValue}"
// prints 8 or -1 randomly