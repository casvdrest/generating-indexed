{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}

import Hedgehog

import SpecGeneric
import SpecIDesc

-- | Collection of all test groups
main :: IO Bool
main = do 
  putStrLn ""
  checkParallel $ Group "Derived instances of the Generatable class" spec_group_generic
  checkParallel $ Group "IDesc Generators" spec_group_idesc

