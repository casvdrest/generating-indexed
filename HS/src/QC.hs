{-# LANGUAGE GADTs #-}

{-|
Module      : QC
Description : QuickCheck interpretation for generators
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

This module contains a generator interpretation that maps abstract generators
to a quickcheck generator 
-}
module QC where

  import qualified Gen

  import Test.QuickCheck
  import Test.QuickCheck.Gen

  import Control.Applicative

  import Debug.Trace 

  -- TODO: return value as maybe in case sampling fails
  toQcGen' :: Gen.Gen i a t -> (i -> Gen.Gen i t t) -> Gen a
  toQcGen' (Gen.Pure x) tg = pure x
  toQcGen' (Gen.Or g1 g2) tg = oneof [toQcGen' g1 tg, toQcGen' g2 tg]
  toQcGen' (Gen.Ap g1 g2) tg = toQcGen' g1 tg <*> toQcGen' g2 tg
  toQcGen' (Gen.Bind g1 gf) tg = toQcGen' g1 tg >>= (flip  toQcGen' tg) . gf
  toQcGen' (Gen.Mu i) tg = toQcGen' (tg i) tg
  toQcGen' (Gen.Call g x) tg = toQcGen' (g x) g

  
  toQcGen :: (i -> Gen.G i a a) -> i -> Gen a
  toQcGen g x = toQcGen' (Gen.unG $ g x) (Gen.unG . g)

  bool :: Gen.G () Bool Bool
  bool = pure True <|> pure False

  nat :: Gen.G () Gen.Nat Gen.Nat
  nat  =  pure Gen.Zero
      <|> Gen.Suc <$> Gen.mu ()

  type SOPGen i a = [(Int , Gen.G i a a)]

  toSizedQcGen' :: Int -> Gen.Gen i a t -> (i -> SOPGen i t) -> Int -> Gen a
  toSizedQcGen' n (Gen.Pure x) tg size = pure x
  toSizedQcGen' n (Gen.Ap g1 g2) tg size =
    toSizedQcGen' n g1 tg size <*> toSizedQcGen' n g2 tg size
  toSizedQcGen' n (Gen.Bind g1 gf) tg size =
    toSizedQcGen' n g1 tg size >>= (\x -> toSizedQcGen' n x tg size) . gf
  toSizedQcGen' n (Gen.Mu i) tg size = toSizedQcGen tg i ((size - 1) `div` n)
  toSizedQcGen' n (Gen.Call g i) tg size = toQcGen' (g i) g

  toSizedQcGen :: (i -> SOPGen i a) -> i -> Int -> Gen a
  toSizedQcGen gs i size = 
    frequency (map (\(n , Gen.G gen) -> (if n > 0 then size else 1 , toSizedQcGen' n gen gs size)) (gs i))

  nat' :: SOPGen () Gen.Nat
  nat' =
    [ (0 , pure Gen.Zero)
    , (1 , Gen.Suc <$> Gen.mu ())
    ]

  data Tree = Leaf | Node Tree Tree deriving (Show)

  data Term = Var Gen.Nat | Abs Gen.Nat Term | App Term Term deriving (Show)

  tree :: SOPGen () Tree
  tree =
    [ (0, pure Leaf)
    , (2 , Node <$> Gen.mu () <*> Gen.mu ())
    ]

  term :: SOPGen () Term
  term =
    [ (0 , Var <$> (Gen.G (Gen.Call (Gen.unG . Gen.triv nat) ())))
    , (1 , Abs <$>  (Gen.G (Gen.Call (Gen.unG . Gen.triv nat) ())) <*> (Gen.mu ()))
    , (2 , App <$> (Gen.mu ()) <*> (Gen.mu ()))
    ]
  

  

  
