open import Level hiding (suc ; zero)
open import Data.List hiding (map; fromMaybe)
open import Relation.Binary.PropositionalEquality hiding ([_])

-- Contains some miscelaneous datatypes and functions
module Model.Data where

  -- Fair merge between two lists
  merge : ∀ {ℓ} {a : Set ℓ} → List a → List a → List a
  merge [] ys = ys
  merge (x ∷ xs) ys = x ∷ merge ys xs

  -- A proof of type 'x ∈ xs' asserts that 'x' is an element of the list
  -- 'xs'
  data _∈_ {ℓ} {a : Set ℓ} : a → List a → Set ℓ where
    here  : ∀ {x : a} {xs : List a} → x ∈ (x ∷ xs)
    there : ∀ {x y : a} {xs : List a} → x ∈ xs → x ∈ (y ∷ xs)

  -- A proof of type 'x ∈' xs' asserts that 'x' is an element of the list
  -- 'xs', using explicit equalities
  data _∈'_ {ℓ} {a : Set ℓ} : a → List a → Set ℓ where
    here'  : ∀ {x y : a} {xs : List a} → x ≡ y  → x ∈' (y ∷ xs)
    there' : ∀ {x y : a} {xs : List a} → x ∈ xs → x ∈' (y ∷ xs) 
