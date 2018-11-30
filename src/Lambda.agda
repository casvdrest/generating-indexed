open import Data.Nat

module src.Lambda where

  data τ : Set where
    _↦_ : τ → τ → τ
    nat : τ

  data Λ : ℕ → τ → Set where
    λ→ : ∀ {ℓ : ℕ} {τ₁ : τ} → Λ ℓ τ₁ → Λ (suc ℓ) (nat ↦ τ₁)
    α  : ∀ {ℓ : ℕ} → Λ ℓ nat
    ap : ∀ {ℓ : ℕ} → Λ ℓ nat
