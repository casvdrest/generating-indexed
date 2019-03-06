{-# OPTIONS --type-in-type #-}

open import src.Gen.Indexed.Signature
open import src.Gen.Base

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Bool

open import Category.Functor
open import Category.Monad

module src.Gen.Indexed.Generic where

  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawMonad ⦃...⦄ using (_>>_; _>>=_; return; pure)

  𝕌-gen : (u : 𝕌) → (`u : 𝕌~ (λ a → ⟪ 𝔾 a ⟫) u) → ∀ {n : ℕ} → 𝔾 ⟦ u ⟧ᵤ n
  𝕌-gen 𝟘 m = uninhabited
  𝕌-gen 𝟙 m = pure tt
  𝕌-gen (u₁ ⊞ u₂) (m₁ ⊞~ m₂) =
    ⦇ inj₁ (𝕌-gen u₁ m₁) ⦈ ∥ ⦇ inj₂ (𝕌-gen u₂ m₂) ⦈
  𝕌-gen (u₁ ⊠ u₂) (m₁ ⊠~ m₂) =
    ⦇ (𝕌-gen u₁ m₁) , (𝕌-gen u₂ m₂) ⦈
  𝕌-gen (𝕂 x) (𝕂~ x₁) = ⟨ x₁ ⟩

  Σ-gen : ∀ {a : Set} {P : a → Set} {n : ℕ}
          → ⟪ 𝔾 a ⟫ → ⟪ 𝔾ᵢ P ⟫ → 𝔾 (Σ[ x ∈ a ] P x) n
  Σ-gen gₐ gₚ =
    do x ← ⟨ gₐ ⟩
       y ← ⟨ gₚ ⟩ᵢ x
       return (x , y)

  _~Π~_ : ∀ {a : Set} {P : a → Set} {n : ℕ}
          → 𝔾 a n → (∀ {n : ℕ} → 𝔾ᵢ P n) → 𝔾 (Π[ a ] P) n
  gₐ ~Π~ gₚ = {!!}

  {-
  deriveGenᵢ : ∀ {i : Set} {Σ : Sig i} {n : ℕ}
               → ((x : i) → 𝕌~ (λ a → ⟪ 𝔾 a ⟫) (Sig.Op Σ x))
               → ((x : i) → (op : ⟦ Sig.Op Σ x ⟧ᵤ) → 𝕌~ (λ a → ⟪ 𝔾 a ⟫) (Sig.Ar Σ op))
               → (∀ {n : ℕ} → 𝔾ᵢ (⟦ Σ ⟧ (μ Σ)) n) → 𝔾ᵢ (⟦ Σ ⟧ (μ Σ)) n
  deriveGenᵢ {Σ = Op ◃ Ar ∣ Ty} sig₁ sig₂ μ ind =
    do op ← 𝕌-gen (Op ind) (sig₁ ind)
       f  ← 𝕌-gen (Ar op) (sig₂ ind op) ~Π~ (λ ind → ⦇ `μ (μ (Ty ind)) ⦈)
       return (op , f) 

  -}
  
