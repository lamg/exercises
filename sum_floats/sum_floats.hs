module Lib
    ( getInput, sumFloats
    ) where
import System.IO (getContents)

getInput :: IO [String]
getInput =  prepareFloats . lines <$> getContents

prepareFloat :: String -> String
prepareFloat = map (\c -> if c == ',' then '.' else c) . removeSpaces 

removeSpaces :: String -> String
removeSpaces = foldr (\c acc -> if c == ' ' then acc else c:acc) ""
                                                                  
prepareFloats :: [String] -> [String]
prepareFloats = map prepareFloat

convertFloat :: String -> Maybe Float
convertFloat s = case (reads s :: [(Float, String)]) of
  [(r, "")] -> Just r
  _ -> Nothing

sumFloats :: [String] -> Maybe Float
sumFloats = foldl sumAcc (Just 0)

sumAcc :: Maybe Float -> String -> Maybe Float
sumAcc acc s = case convertFloat s of
  Nothing -> Nothing
  (Just r) -> fmap (r +) acc