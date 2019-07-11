{-# LANGUAGE GADTs, RankNTypes, DeriveGeneric, DeriveAnyClass #-}

{-|
Module      : Interpret
Description : Generator interpretations
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

Interpretations map values of the abstract generator type to a concrete 
interpretation, such as size-bounded lists or random generators. This 
module contains an interpretretation to lists bounded by recursive depth
(i.e. generators in the sense of SmallCheck) as an example. 
-}
module Interpret where

  import Gen
  import Singleton

  -- | An instance 'Interpret a' Describes how a generator can be interpreted
  --   to a value of type 'a'. 
  class Interpretation a where 
    interpret :: (i -> G i t) -> i -> a t

  -- | Fair merge of two lists
  merge :: [a] -> [a] -> [a] 
  merge []     ys = ys 
  merge (x:xs) ys = x : merge ys xs

  -- | Enumerative interpretation of generators, with recursive depth as 
  --   the size parameter
  (!~.) :: (Gen i t a, i -> Gen i t t) -> Int -> [a]
  (Pure x, tg)  !~. 0    = [x] 
  (Mu   _ , tg) !~. 0    = []
  (gen, tg)  !~. n    =  
    case gen of 
      None                -> []
      Pure x              -> [x]
      Or g1 g2            -> ((g1, tg) !~. n) `merge` ((g2, tg) !~. n)
      Ap g1 g2            -> ((g1, tg) !~. n) <*> ((g2, tg) !~. n)
      Bind g1 g2          -> ((g1, tg) !~. n) >>= \x -> (g2 x, tg) !~. n
      Mu i                -> (tg i, tg) !~. (n - 1) 
      Call gen' i         -> (gen' i, gen') !~. n
 
  -- | Execute the enumerative interpretetation
  runEnum :: (i -> G i a) -> i -> Int -> [a]
  runEnum fg i = (!~.) (fg i, fg) 

  newtype BoundedList a = Bounded (Int -> [a])

  -- | 'Interpretation' instance for the enumerative interpretation 
  instance Interpretation BoundedList where
    interpret gen i = Bounded (runEnum gen i)
