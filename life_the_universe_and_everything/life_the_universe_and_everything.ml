let rec read_and_write () =
    let n = read_int () in

    if n = 42 then
        ()
    else
        (print_int n
         print_newline ()
         read_and_write ())

let () = read_and_write ()
