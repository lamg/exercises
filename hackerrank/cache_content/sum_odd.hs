(|>) :: a -> (a -> b) -> b
x |> f = f x

sumOdd ::  [Int] -> Int
sumOdd xs = xs |> filter (\n -> mod n 2 == 1) |> sum