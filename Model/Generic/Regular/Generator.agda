open import Model.Base
open import Model.Combinators

open import Model.Generic.Isomorphism

open import Model.Generic.Regular.Instances
open import Model.Generic.Regular.Universe
open import Model.Generic.Regular.Cogen

open import Data.Unit
open import Data.Sum
open import Data.Product

import Level

open import Function

module Model.Generic.Regular.Generator where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄

  -- Derive a generator for regular types
  deriveGen :
    ∀ {f g : Reg}
    → RegInfo (λ S → 𝔾 (λ _ → S) tt) f
    → Gen (⟦ f ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt
  deriveGen {U} {g} c = pure tt
  deriveGen {f₁ ⊕ f₂}  {g} (c₁ ⊕~ c₂) =
    ⦇ inj₁ (deriveGen c₁) ⦈ ∥ ⦇ inj₂ (deriveGen c₂) ⦈
  deriveGen {f₁ ⊗ f₂}  {g} (c₁ ⊗~ c₂) =
    ⦇ (deriveGen c₁) , (deriveGen c₂) ⦈
  deriveGen {I} {g} c   = ⦇ In (μ tt) ⦈
  deriveGen {K a} {g} (K~ gₖ) = Call tt λ _ → gₖ
  deriveGen {Z} Z~ = None

  -- Derive a generator for any type, given that it is isomorphic to some
  -- regular type
  isoGen :
    ∀ (a : ⊤ → Set) → ⦃ p : Regular (a tt) ⦄
    → RegInfo (λ S → 𝔾 (λ _ → S) tt) (getPf p) → 𝔾 a tt
  isoGen a ⦃ record { W = f , iso } ⦄ reginfo =
    ⦇ (_≃_.to iso ∘ In) (Call tt λ _ → deriveGen reginfo) ⦈

  -- Derive a cogenerator for any type, given that it is isomorphic to
  -- a regular type
  isoCogen :
    ∀ (a : ⊤ → Set) → ⦃ p : Regular (a tt) ⦄
    → RegInfo (λ S → co𝔾 (λ _ → S) tt) (getPf p) → co𝔾 a tt
  isoCogen a ⦃ record { W = f , iso } ⦄ reginfo {b} gₐ =
    ⦇ (λ f → f ∘ (λ { (In x) → x }) ∘ _≃_.from iso)
      (Call (Level.lift tt) (λ _ → deriveCogen {g = f} reginfo gₐ)) ⦈
