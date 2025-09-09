(|>) :: a -> (a -> b) -> b
x |> f = f x

infixl 0 |>

mod5 = [1 .. 5] |> cycle

mod3 = [1 .. 3] |> cycle

oneToN n = [1 .. n]

multiples n = zip3 (oneToN n) mod3 mod5

soundOf (_, 3, 5) = "FizzBuzz"
soundOf (_, 3, _) = "Fizz"
soundOf (_, _, 5) = "Buzz"
soundOf (n, _, _) = show n

fizzBuzz n = multiples n |> map soundOf |> unlines |> putStr
