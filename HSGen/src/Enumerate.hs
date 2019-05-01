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
  merge (x:xs) ys = x : merge ys xs

  (.~.) :: (Gen a t, Gen t t) -> Int -> [a]
  (Pure x, tg) .~. 0    = [x] 
  (Mu   _ , tg) .~. 0    = []
  (gen, tg)  .~. n = 
    case gen of 
      None        -> []
      Pure x      -> [x]
      Or g1 g2    -> merge ((g1, tg) .~. n) ((g2, tg) .~. n)
      Ap g1 g2    -> ((g1, tg) .~. n) <*> ((g2, tg) .~. n)
      Bind g1 g2  -> ((g1, tg) .~. n) >>= \x -> (g2 x, tg) .~. n
      Mu _        -> (tg, tg) .~. (n - 1) 
      Call gen'   -> (gen', gen') .~. n
 
  (!~.) :: (Gen a t, i -> Gen t t, Ex -> i) -> Int -> [a]
  (Pure x, tg, _)  !~. 0    = [x] 
  (Mu   _ , tg, _) !~. 0    = []
  (gen, tg, conv)  !~. n    =  
    case gen of 
      None                -> []
      Pure x              -> [x]
      Or g1 g2            -> merge ((g1, tg, conv) !~. n) ((g2, tg, conv) !~. n)
      Ap g1 g2            -> ((g1, tg, conv) !~. n) <*> ((g2, tg, conv) !~. n)
      Bind g1 g2          -> ((g1, tg, conv) !~. n) >>= \x -> (g2 x, tg, conv) !~. n
      Mu x                -> (tg (conv x), tg, conv) !~. (n - 1) 
      Call  gen'          -> (gen', gen') .~. n
      CallF i gen' conv'  -> (gen' i, gen', conv') !~. n

  run :: G a a -> Int -> [a]
  run (G gen) n = (gen, gen) .~. n

  runI :: (Ex -> i) -> (i -> G a a) -> i -> Int -> [a]
  runI conv f i n = (unG (f i), unG . f, conv) !~. n 
  
