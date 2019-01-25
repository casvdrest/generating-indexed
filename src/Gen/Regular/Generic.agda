
{-# OPTIONS --type-in-type #-}

open import src.Gen.Base

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.List

open import Category.Monad

open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Sum

open import Function

open import Codata.Thunk using (Thunk; force)
open import Size

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module src.Gen.Regular.Generic where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  data Reg : Set where
    U   : Reg
    _⊕_ : Reg → Reg → Reg
    _⊗_ : Reg → Reg → Reg
    I   : Reg
    K   : Σ[ a ∈ Set ] ⟪ 𝔾 a ⟫ → Reg

  ⟦_⟧ : Reg → Set → Set
  ⟦ U           ⟧ r = ⊤
  ⟦ reg₁ ⊕ reg₂ ⟧ r = ⟦ reg₁ ⟧ r ⊎ ⟦ reg₂ ⟧ r
  ⟦ reg₁ ⊗ reg₂ ⟧ r = ⟦ reg₁ ⟧ r × ⟦ reg₂ ⟧ r 
  ⟦ I           ⟧ r = r
  ⟦ K (a , g)   ⟧ r = a
  
  data μ (f : Reg) : Set where
    `μ : ⟦ f ⟧ (μ f) → μ f

  mapᵣ : ∀ {a b : Set} → (f : Reg) → (a → b) → ⟦ f ⟧ a → ⟦ f ⟧ b
  mapᵣ U f tt = tt
  mapᵣ (pf₁ ⊕ pf₂) f (inj₁ x) = inj₁ (mapᵣ pf₁ f x)
  mapᵣ (pf₁ ⊕ pf₂) f (inj₂ y) = inj₂ (mapᵣ pf₂ f y)
  mapᵣ (pf₁ ⊗ pf₂) f (fst , snd) = mapᵣ pf₁ f fst , mapᵣ pf₂ f snd
  mapᵣ I f i     = f i
  mapᵣ (K x) f i = i

  ugen : ∀ {n : ℕ} {a : Set} → 𝔾 (⟦ U ⟧ a) n
  ugen = pure tt

  igen : ∀ {n : ℕ} {a : Set} {f : Reg} → 𝔾 (⟦ f ⟧ a) n →
         𝔾 (⟦ f ⟧ a) n
  igen μ = μ

  ⊕gen : ∀ {n : ℕ} {f g : Reg} {a : Set} →
         𝔾 (⟦ f ⟧ a) n → 𝔾 (⟦ g ⟧ a) n →
         𝔾 (⟦ f ⊕ g ⟧ a) n
  ⊕gen f g = ⦇ inj₁ f ⦈ ∥ ⦇ inj₂ g ⦈

  ⊗gen : ∀ {n : ℕ} {f g : Reg} {a : Set} →
         𝔾 (⟦ f ⟧ a) n → 𝔾 (⟦ g ⟧ a) n →
         𝔾 (⟦ f ⊗ g ⟧ a) n
  ⊗gen f g = ⦇ f , g ⦈

  deriveGen : ∀ {f g : Reg} {n : ℕ}
              → 𝔾 (⟦ g ⟧ (μ g)) n
              → 𝔾 (⟦ f ⟧ (μ g)) n
  deriveGen {U}      {g} rec = ugen {a = μ g}
  deriveGen {f ⊕ f₁} {g} rec = ⊕gen {f = f} {g = f₁} (deriveGen {f = f} rec) (deriveGen {f = f₁} rec)
  deriveGen {f ⊗ f₁} {g} rec = ⊗gen {f = f} {g = f₁} (deriveGen {f = f} rec) (deriveGen {f = f₁} rec)
  deriveGen {I}      {g} rec = ⦇ `μ (igen {f = g} rec) ⦈
  deriveGen {K (a , gen)} {g} {n} rec = ⟨ gen ⟩
