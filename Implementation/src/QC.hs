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
  import Datatypes

  import Test.QuickCheck
  import Test.QuickCheck.Gen

  import Control.Applicative

  import Debug.Trace 

  -- | Build a QuickCheck generatr from our abstract generator type 
  -- TODO: return value as maybe in case sampling fails
  toQcGen' :: Gen.Gen i t a -> (i -> Gen.G i t) -> Gen a
  toQcGen' (Gen.Pure x) tg = pure x
  toQcGen' (Gen.Or g1 g2) tg = oneof [toQcGen' g1 tg, toQcGen' g2 tg]
  toQcGen' (Gen.Ap g1 g2) tg = toQcGen' g1 tg <*> toQcGen' g2 tg
  toQcGen' (Gen.Bind g1 gf) tg = toQcGen' g1 tg >>= (flip  toQcGen' tg) . gf
  toQcGen' (Gen.Mu i) tg = toQcGen' (tg i) tg
  toQcGen' (Gen.Call g x) tg = toQcGen' (g x) g

  -- | Build a QuickCheck generator from a function from index to generator
  toQcGen :: (i -> Gen.G i a ) -> i -> Gen a
  toQcGen g x = toQcGen' (g x) g

  -- | Representation for generators that are build from a sum of products
  type SOPGen i a = [(Int , Gen.G i a)]

  -- | Build a sized QuickCheck generator from an abstract generator that is 
  --   in a sum of product representation
  toSizedQcGen' :: Int -> Gen.Gen i t a -> (i -> SOPGen i t) -> Int -> Gen a
  toSizedQcGen' n (Gen.Pure x) tg size = pure x
  toSizedQcGen' n (Gen.Ap g1 g2) tg size =
    toSizedQcGen' n g1 tg size <*> toSizedQcGen' n g2 tg size
  toSizedQcGen' n (Gen.Bind g1 gf) tg size =
    toSizedQcGen' n g1 tg size >>= (\x -> toSizedQcGen' n x tg size) . gf
  toSizedQcGen' n (Gen.Mu i) tg size = toSizedQcGen tg i ((size - 1) `div` n)
  toSizedQcGen' n (Gen.Call g i) tg size = toQcGen' (g i) g

  toSizedQcGen :: (i -> SOPGen i a) -> i -> Int -> Gen a
  toSizedQcGen gs i size = 
    frequency (map (\(n , gen) -> (if n > 0 then size else 1 , toSizedQcGen' n gen gs size)) (gs i))

  -- | Sum of product generator for natural numbers
  nat' :: SOPGen () Nat
  nat' =
    [ (0 , pure Zero)
    , (1 , Suc <$> Gen.mu ())
    ]

  

  
