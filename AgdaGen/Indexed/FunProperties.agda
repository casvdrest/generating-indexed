open import AgdaGen.Indexed.Isomorphism

open import Data.Sum
open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality

module AgdaGen.Indexed.FunProperties where

  ⊎-split : ∀ {a b c : Set} → (h : a ⊎ b → c) → Σ[ f ∈ (a → c) ] Σ[ g ∈ (b → c) ] (λ { (inj₁ x) → f x ; (inj₂ y) → g y }) ≡ h
  ⊎-split f = (λ x → f ((inj₁ x))) , (λ y → f (inj₂ y)) , funext λ { {inj₁ x} → refl ; {inj₂ y} → refl }

  ⊤-split : ∀ {a : Set} → (h : ⊤ → a) → Σ[ x ∈ a ] (λ { tt → x }) ≡ h
  ⊤-split h = (h tt) , refl

  
