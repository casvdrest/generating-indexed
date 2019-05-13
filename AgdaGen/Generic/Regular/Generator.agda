open import AgdaGen.Base
open import AgdaGen.Combinators

open import AgdaGen.Generic.Isomorphism

open import AgdaGen.Generic.Regular.Instances
open import AgdaGen.Generic.Regular.Universe
open import AgdaGen.Generic.Regular.Cogen

open import Data.Unit
open import Data.Sum
open import Data.Product

import Level

open import Function

module AgdaGen.Generic.Regular.Generator where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄

  deriveGen :
    ∀ {f g : Reg}
    → RegInfo 𝔾 f
    → Gen (⟦ f ⟧ (Fix g)) (⟦ g ⟧ (Fix g))
  deriveGen {U} {g} c = pure tt
  deriveGen {f₁ ⊕ f₂}  {g} (c₁ ⊕~ c₂) =
    ⦇ inj₁ (deriveGen c₁) ⦈ ∥ ⦇ inj₂ (deriveGen c₂) ⦈
  deriveGen {f₁ ⊗ f₂}  {g} (c₁ ⊗~ c₂) =
    ⦇ (deriveGen c₁) , (deriveGen c₂) ⦈
  deriveGen {I} {g} c   = ⦇ In μ ⦈
  deriveGen {K a} {g} (K~ gₖ) = ` gₖ
  deriveGen {Z} Z~ = None

  isoGen :
    ∀ (a : Set) → ⦃ p : Regular a ⦄
    → RegInfo (𝔾) (getPf p) → 𝔾 a
  isoGen a ⦃ record { W = f , iso } ⦄ reginfo =
    ⦇ (_≅_.to iso ∘ In) (` deriveGen reginfo) ⦈

  isoCogen :
    ∀ (a : Set) → ⦃ p : Regular a ⦄
    → RegInfo co𝔾 (getPf p) → co𝔾 a
  isoCogen a ⦃ record { W = f , iso } ⦄ reginfo {b} gₐ =
    ⦇ (λ f → f ∘ (λ { (In x) → x }) ∘ _≅_.from iso)
      (` deriveCogen {g = f} reginfo gₐ) ⦈
