{-# OPTIONS --type-in-type #-}

open import src.Gen.Base
open import src.Data

open import Data.Nat
open import Data.Unit

open import Data.Bool

open import Codata.Musical.Notation

open import Category.Monad


open import Relation.Binary.PropositionalEquality

module src.Gen.Regular.Generic where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  
