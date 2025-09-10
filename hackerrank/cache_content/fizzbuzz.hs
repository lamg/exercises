(|>) :: a -> (a -> b) -> b
x |> f = f x

infixl 0 |>

mod5 :: [Integer]
mod5 = [1 .. 5] |> cycle

mod3 :: [Integer]
mod3 = [1 .. 3] |> cycle

oneToN :: Integer -> [Integer]
oneToN n = [1 .. n]

multiples :: Integer -> [(Integer, Integer, Integer)]
multiples n = zip3 (oneToN n) mod3 mod5

soundOf :: (Integer, Integer, Integer) -> String
soundOf (_, 3, 5) = "FizzBuzz"
soundOf (_, 3, _) = "Fizz"
soundOf (_, _, 5) = "Buzz"
soundOf (n, _, _) = show n

fizzBuzz :: Integer -> IO ()
fizzBuzz n = multiples n |> map soundOf |> unlines |> putStr
