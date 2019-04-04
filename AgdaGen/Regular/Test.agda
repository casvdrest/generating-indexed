open import AgdaGen.Base
open import AgdaGen.Regular.Examples

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.Maybe using (just; nothing)

module AgdaGen.Regular.Test where

  prop1 : ⟨ nat ⟩ 10 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  prop1 = refl

  
  prop2 : ⟨ bool ⟩ 10  ≡ true ∷ false ∷ []
  prop2 = refl

  
  prop3 : ⟨ (maybe nat) ⟩ 10 ≡ nothing ∷ just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷ just 4 ∷ just 5 ∷ just 6 ∷ just 7 ∷ just 8 ∷ just 9 ∷ []
  prop3 = refl

 
  prop4 : ⟨ (list nat) ⟩ 3 ≡ [] ∷ (0 ∷ []) ∷ (0 ∷ 0 ∷ []) ∷ (0 ∷ 1 ∷ []) ∷ (1 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ (1 ∷ 1 ∷ []) ∷ (2 ∷ []) ∷ (2 ∷ 0 ∷ []) ∷ (2 ∷ 1 ∷ []) ∷ []
  prop4 = refl

