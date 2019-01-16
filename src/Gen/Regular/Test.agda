open import src.Gen.Base
open import src.Gen.Regular.Examples

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.Maybe using (just; nothing)

module src.Gen.Regular.Test where

  prop1 : 𝔾-run nat 10 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  prop1 = refl

  
  prop2 : 𝔾-run bool 10  ≡ true ∷ false ∷ []
  prop2 = refl

  
  prop3 : 𝔾-run (maybe nat) 10 ≡ nothing ∷ just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷ just 4 ∷ just 5 ∷ just 6 ∷ just 7 ∷ just 8 ∷ []
  prop3 = refl

 
  prop4 : 𝔾-run (list nat) 3 ≡ [] ∷ (0 ∷ []) ∷ (0 ∷ 0 ∷ []) ∷ (1 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ []
  prop4 = refl
