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

  𝕌-gen : (u : 𝕌) → ∀ {n : ℕ} → 𝔾 ⟦ u ⟧ᵤ n
  𝕌-gen 𝟘 = uninhabited
  𝕌-gen 𝟙 = pure tt
  𝕌-gen (u₁ ⊞ u₂) = ⦇ inj₁ (𝕌-gen u₁) ⦈ ∥ ⦇ inj₂ (𝕌-gen u₂) ⦈
  𝕌-gen (u₁ ⊠ u₂) = ⦇ (𝕌-gen u₁) , (𝕌-gen u₂) ⦈

  _~Σ~_ : ∀ {a : Set} {P : a → Set} {n : ℕ}
          → (∀ {n : ℕ} → 𝔾 a n) → (∀ {n : ℕ} → 𝔾ᵢ P n)
          → 𝔾 (Σ[ x ∈ a ] P x) n
  gₐ ~Σ~ gₚ =
    do idx ← gₐ
       val ← gₚ idx
       return (idx , val)

  _~Π~_ : ∀ {a : Set} {P : a → Set} {n : ℕ}
          → 𝔾 a n → (∀ {n : ℕ} → 𝔾ᵢ P n) → 𝔾 (Π[ a ] P) n
  gₐ ~Π~ gₚ =
    do idx ← gₐ
       val ← gₚ idx
       return λ {x → {!!}}

  deriveGenᵢ : ∀ {i : Set} {Σ : Sig i} {n : ℕ} → (∀ {n : ℕ}
               → 𝔾ᵢ (⟦ Σ ⟧ (μ Σ)) n) → 𝔾ᵢ (⟦ Σ ⟧ (μ Σ)) n
  deriveGenᵢ {Σ = Op ◃ Ar ∣ Ty} μ ind =
    do op ← 𝕌-gen (Op ind)
       let gen = 𝕌-gen (Ar op)
       f  ← 𝕌-gen (Ar op) ~Π~ (λ ind → ⦇ `μ (μ (Ty ind)) ⦈)
       return (op , f) 
