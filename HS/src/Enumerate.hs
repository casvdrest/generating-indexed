{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UnicodeSyntax #-}

module Enumerate where

  import Gen

  import Debug.Trace

  merge :: [a] -> [a] -> [a] 
  merge []     ys = ys 
 
  (!~.) :: (Gen i a t, i -> Gen i t t) -> Int -> [a]
  (Pure x, tg)  !~. 0    = [x] 
  (Mu   _ , tg) !~. 0    = []
  (gen, tg)  !~. n    =  
    case gen of 
      None                -> []
      Pure x              -> [x]
      Or g1 g2            -> merge ((g1, tg) !~. n) ((g2, tg) !~. n)
      Ap g1 g2            -> ((g1, tg) !~. n) <*> ((g2, tg) !~. n)
      Bind g1 g2          -> ((g1, tg) !~. n) >>= \x -> (g2 x, tg) !~. n
      Mu i                -> (tg i, tg) !~. (n - 1) 
      Call gen' i         -> (gen' i, gen') !~. n

  run :: (i -> G i a a) -> i -> Int -> [a]
  run fg i n = (unG (fg i), unG . fg) !~. n

