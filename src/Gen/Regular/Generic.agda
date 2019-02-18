
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
    K   : Set → Reg

  data RegInfo (P : Set → Set) : Reg → Set where
    U~   : RegInfo P U
    
    _⊕~_ : ∀ {f₁ f₂ : Reg}
           → RegInfo P f₁ → RegInfo P f₂
           → RegInfo P (f₁ ⊕ f₂)
           
    _⊗~_ : ∀ {f₁ f₂ : Reg}
           → RegInfo P f₁ → RegInfo P f₂
           → RegInfo P (f₁ ⊗ f₂)
           
    I    : RegInfo P I
    
    K    : ∀ {a : Set} → P a → RegInfo P (K a)
    

  ⟦_⟧ : Reg → Set → Set
  ⟦ U           ⟧ r = ⊤
  ⟦ reg₁ ⊕ reg₂ ⟧ r = ⟦ reg₁ ⟧ r ⊎ ⟦ reg₂ ⟧ r
  ⟦ reg₁ ⊗ reg₂ ⟧ r = ⟦ reg₁ ⟧ r × ⟦ reg₂ ⟧ r 
  ⟦ I           ⟧ r = r
  ⟦ K a         ⟧ r = a
  
  data μ (f : Reg) : Set where
    `μ : ⟦ f ⟧ (μ f) → μ f

  mapᵣ : ∀ {a b : Set} → (f : Reg) → (a → b) → ⟦ f ⟧ a → ⟦ f ⟧ b
  mapᵣ U f tt = tt
  mapᵣ (pf₁ ⊕ pf₂) f (inj₁ x) = inj₁ (mapᵣ pf₁ f x)
  mapᵣ (pf₁ ⊕ pf₂) f (inj₂ y) = inj₂ (mapᵣ pf₂ f y)
  mapᵣ (pf₁ ⊗ pf₂) f (fst , snd) = mapᵣ pf₁ f fst , mapᵣ pf₂ f snd
  mapᵣ I f i     = f i
  mapᵣ (K x) f i = i

  deriveGen : ∀ {f g : Reg} {n : ℕ}
              → RegInfo (λ a → ⟪ 𝔾 a ⟫) f
              → 𝔾 (⟦ g ⟧ (μ g)) n
              → 𝔾 (⟦ f ⟧ (μ g)) n
  deriveGen {U}       {g} c rec = pure tt
  deriveGen {f ⊕ f₁}  {g} (c₁ ⊕~ c₂) rec =
    ⦇ inj₁ (deriveGen {f = f} c₁ rec) ⦈ ∥ ⦇ inj₂ (deriveGen {f = f₁} c₂ rec) ⦈ 
  deriveGen {f ⊗ f₁}  {g} (c₁ ⊗~ c₂) rec =
    ⦇ (deriveGen {f = f} c₁ rec) , (deriveGen {f = f₁} c₂ rec) ⦈
  deriveGen {I}       {g} c rec = ⦇ `μ rec ⦈
  deriveGen {K a} {g} {n} (K x) rec = ⟨ x ⟩
