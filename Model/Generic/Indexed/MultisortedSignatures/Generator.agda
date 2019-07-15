{-# OPTIONS --type-in-type #-}

open import Model.Generic.Indexed.MultisortedSignatures.Signature
open import Model.Generic.Regular.Universe
open import Model.Generic.Isomorphism
open import Model.Generic.Regular.Generator
open import Model.Base
open import Model.Combinators
open import Model.Generic.Regular.Cogen
open import Model.Generic.Indexed.PiGen

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Data.List
open import Data.Vec hiding (_>>=_)

open import Data.Fin hiding (toℕ)

open import Function
open import Level

module Model.Generic.Indexed.MultisortedSignatures.Generator where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
  open GMonad       ⦃...⦄
  
  Gen-Σ : ∀ {i : Set} {P : i → Set} → 𝔾 (λ _ → i) tt → ((x : i) → 𝔾 P x) → 𝔾 (λ _ → Σ[ x ∈ i ] P x) tt
  Gen-Σ g₁ g₂ = (Call tt (λ _ → g₁)) >>= λ x → Call x g₂ >>= λ y → Pure (x , y)

  {-# TERMINATING #-}
  deriveGenᵢ :
    ∀ {i : Set} {Σ : Sig i}
    → ((x : i) → RegInfo (λ op → 𝔾 (λ _ → op) tt × Π𝔾 op) (Sig.Op Σ x))
    → ((x : i) → (op : Fix (Sig.Op Σ x)) → RegInfo (λ ar → 𝔾 (λ _ → ar) tt × Π𝔾 ar) (Sig.Ar Σ op))
    → (x : i) → 𝔾 (λ x → ⟦ Σ ⟧ₛ (Fixₛ Σ) x) x
  deriveGenᵢ {i} {Op ◃ Ar ∣ Ty} sig₁ sig₂ x =
    do op ← Call {x = x} tt (λ _ → deriveGen (map-reginfo proj₁ (sig₁ x)))
       ar ← Call {x = x} tt (λ _ → derivePiGen (map-reginfo proj₂ (sig₂ x (In op))) λ ar → ⦇ Inₛ (Call (Ty (In ar)) (deriveGenᵢ sig₁ sig₂)) ⦈)
       pure (In op , λ { (In x) → ar x })
