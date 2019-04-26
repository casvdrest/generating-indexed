{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UnicodeSyntax #-}

module Enumerate where

  import Gen

  merge :: [a] -> [a] -> [a] 
  merge []     ys = ys 
  merge (x:xs) ys = x : merge ys xs

  (.~.) :: (Gen a t, Gen t t) -> Int -> [a]
  (Pure x, tg) .~. 0    = [x] 
  (Mu    , tg) .~. 0    = []
  (gen, tg)  .~. n = 
    case gen of 
      None       -> []
      Pure x     -> [x]
      Or g1 g2   -> merge ((g1, tg) .~. n) ((g2, tg) .~. n)
      Ap g1 g2   -> ((g1, tg) .~. n) <*> ((g2, tg) .~. n)
      Bind g1 g2 -> ((g1, tg) .~. n) >>= \x -> (g2 x, tg) .~. n
      Mu         -> (tg, tg) .~. (n - 1) 
      Call gen'  -> (gen', gen') .~. n

  run :: G a a -> Int -> [a]
  run (G gen) n = (gen, gen) .~. n
