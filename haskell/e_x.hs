
(|>) :: a -> (a -> b) -> b
x |> f = f x

term :: (Double, Int) -> Double -> Int -> (Double, Int)
term (_, _) x 0 = (1,1)
term (_,_) x 1 = (x,1)
term (x_n, fac_n) x n = (x_n * x, fac_n * n)

fracSum :: Double -> ((Double, Int), Double) -> Int -> ((Double, Int), Double)
fracSum x (frac, sum) n =
  let (num, den) = term frac x n in
  ((num, den), sum + (num/ fromIntegral den :: Double))
 
expand10 :: Double -> ((Double, Int), Double)
expand10 x = [0..9] |> foldl (fracSum x) ((0,0), 0)

powE :: Double -> Double
powE x = expand10 x |> snd
