{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MonoLocalBinds #-}

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Gen 
import Generic
import Depth

import Data.List
import Data.Proxy

genNat :: MonadGen m => m Nat 
genNat = Gen.recursive Gen.choice [ pure Z ] [ Gen.subterm genNat S ]

genBool :: MonadGen m => m Bool 
genBool = Gen.choice [ pure True , pure False ]

genEither :: MonadGen m => m a -> m b -> m (Either a b)
genEither gl gr = Gen.choice [Left <$> gl , Right <$> gr]

genMaybe :: MonadGen m => m a -> m (Maybe a)
genMaybe gen = Gen.choice [ pure Nothing , Just <$> gen ]

genTuple :: MonadGen m => m a -> m b -> m (a, b)
genTuple gena genb = (,) <$> gena <*> genb 

-- | Assert that values of types that are an instance of the 'Generatable' 
--   class occur in the production of their generators
main :: IO Bool
main = do 
  putStrLn ""
  checkParallel $ Group "Derived instances of the Generatable class" 
    [ ("iselem_derived (Nat)", iselem_derived genNat)
    , ("iselem_derived (Bool)", iselem_derived genBool)
    , ("iselem_derived (Maybe Nat)", iselem_derived (genMaybe genNat) )
    , ("iselem_derived (Maybe Bool)", iselem_derived (genMaybe genBool) )
    , ("iselem_derived (Either Nat Bool)", iselem_derived (genEither genNat genBool))
    , ("iselem_derived (Nat, Bool)", iselem_derived (genTuple genNat genBool))

    , ("not_iselem_derived (Nat)", not_iselem_derived genNat)
    , ("not_iselem_derived (Maybe Nat)", not_iselem_derived (genMaybe genNat) )
    , ("not_iselem_derived (Either Nat Bool)", not_iselem_derived (genEither genNat genBool))
    , ("not_iselem_derived (Nat, Bool)", not_iselem_derived (genTuple genNat genBool))
    ] 

-- | Any generatable element is an element of the list produced by its 
--   generator, applied with its depth
iselem_derived :: (Generatable a, DepthCalc a, Eq a, Show a) 
  => Hedgehog.Gen a -> Property 
iselem_derived generator = 
  property $ do  
    x <- forAll generator
    assert (x `elem` (run gen (depth x)))

-- | Any generateble value is NOT a member of the list produced by its generator, applied
--   with a depth smaller than that of the value
not_iselem_derived :: (Generatable a, DepthCalc a, Eq a, Show a) 
  => Hedgehog.Gen a -> Property 
not_iselem_derived generator =
  property $ do 
      x <- forAll (Gen.filter (\v -> depth v > 0) (generator))
      assert (not (x `elem` (run gen (depth x - 1))))

