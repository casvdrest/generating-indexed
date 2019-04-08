open import AgdaGen.Base renaming (μ to μBase; ⟨_⟩ to ⟨_⟩Base)
open import AgdaGen.Combinators

open import AgdaGen.Generic.Indexed.IDesc.Universe
open import AgdaGen.Generic.Indexed.IDesc.Instances

open import Data.Unit
open import Data.Product
open import Data.Nat

open import Level renaming (suc to sucL ; zero to zeroL)

module AgdaGen.Generic.Indexed.IDesc.Generator where

  Sl-gen : ∀ {ℓ} → 𝔾ᵢ {ℓ = ℓ} Sl
  Sl-gen zero    = None
  Sl-gen (suc n) = ⦇ ▻_ (` Sl-gen n) ⦈ ∥ ⦇ ∙ ⦈

  IDesc-gen :
    ∀ {ℓ} {I : Set} {d₁ : IDesc ℓ I} {d₂ : I → IDesc ℓ I}
    → (x : I) → Gen (⟦ d₁ ⟧ (μ (mk d₂))) (⟦ d₂ x ⟧ (μ (mk d₂)))
  IDesc-gen {d₁ = `var i} {d₂} x = {!!}
  IDesc-gen {d₁ = `1} {d₂} x = ⦇ (lift tt) ⦈
  IDesc-gen {d₁ = dₗ `× dᵣ} {d₂} x =
    ⦇ (IDesc-gen {d₁ = dₗ}  x) , (IDesc-gen {d₁ = dᵣ} x) ⦈
  IDesc-gen {d₁ = `σ n T} {d₂} x =
    do sl ← ` Sl-gen n
       r  ← IDesc-gen {d₁ = T sl} {d₂ = d₂} x
       pure (sl , r)
  IDesc-gen {d₁ = `Σ S T} {d₂} x = {!!}
