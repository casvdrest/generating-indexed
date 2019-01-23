{-# OPTIONS --type-in-type #-}

open import src.Gen.Base

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool

open import Category.Monad

open import Data.Product using (_×_; _,_)
open import Data.Sum

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module src.Gen.Regular.Generic where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  data Reg : Set →  Set where
    U   : Reg ⊥
    K   : (a : Set) → Reg a
    _⊕_ : ∀ {a : Set} → Reg a → Reg a → Reg a
    _⊗_ : ∀ {a : Set} → Reg a → Reg a → Reg a
    I   : Reg ⊥

  ⟦_⟧ : ∀ {a : Set} → Reg a → Set → Set
  ⟦ U           ⟧ r = ⊤
  ⟦ K a         ⟧ r = a
  ⟦ reg₁ ⊕ reg₂ ⟧ r = ⟦ reg₁ ⟧ r ⊎ ⟦ reg₂ ⟧ r
  ⟦ reg₁ ⊗ reg₂ ⟧ r = ⟦ reg₁ ⟧ r × ⟦ reg₂ ⟧ r 
  ⟦ I           ⟧ r = r
  
  data μ {a : Set} (f : Reg a) : Set where
    `μ : ⟦ f ⟧ (μ f) → μ f

  mapᵣ : ∀ {a b c : Set} → (f : Reg c) → (a → b) → ⟦ f ⟧ a → ⟦ f ⟧ b
  mapᵣ U f tt = tt
  mapᵣ (K x) f i = i
  mapᵣ (pf₁ ⊕ pf₂) f (inj₁ x) = inj₁ (mapᵣ pf₁ f x)
  mapᵣ (pf₁ ⊕ pf₂) f (inj₂ y) = inj₂ (mapᵣ pf₂ f y)
  mapᵣ (pf₁ ⊗ pf₂) f (fst , snd) = mapᵣ pf₁ f fst , mapᵣ pf₂ f snd
  mapᵣ I f i = f i

  BoolF : Set
  BoolF = μ (U ⊕ U)

  fromBool : Bool → BoolF
  fromBool false = `μ (inj₁ tt)
  fromBool true = `μ (inj₂ tt)

  toBool : BoolF → Bool
  toBool (`μ (inj₁ tt)) = false
  toBool (`μ (inj₂ tt)) = true

  isoBool₁ : ∀ {b : Bool} → toBool (fromBool b) ≡ b
  isoBool₁ {false} = refl
  isoBool₁ {true} = refl

  isoBool₂ : ∀ {bf : BoolF} → fromBool (toBool bf) ≡ bf
  isoBool₂ {`μ (inj₁ x)} = refl
  isoBool₂ {`μ (inj₂ y)} = refl

  ℕF : Set
  ℕF = μ (U ⊕ I)

  fromℕ : ℕ → ℕF
  fromℕ zero = `μ (inj₁ tt)
  fromℕ (suc n) = `μ (inj₂ (fromℕ n))

  toℕ : ℕF → ℕ
  toℕ (`μ (inj₁ tt)) = zero
  toℕ (`μ (inj₂ y)) = suc (toℕ y)

  isoℕ₁ : ∀ {n : ℕ} → toℕ (fromℕ n) ≡ n
  isoℕ₁ {zero} = refl
  isoℕ₁ {suc n} = cong suc isoℕ₁

  isoℕ₂ : ∀ {nf : ℕF} → fromℕ (toℕ nf) ≡ nf
  isoℕ₂ {`μ (inj₁ x)} = refl
  isoℕ₂ {`μ (inj₂ y)} = cong (`μ ∘ inj₂) isoℕ₂

  gen𝔾 : ∀ {a : Set} → (g : ⟪ 𝔾 a ⟫) → (f : Reg a) → ⟪ 𝔾 (μ f) ⟫
  gen𝔾 k U        μ = ⦇ (`μ tt) ⦈
  gen𝔾 k (K x)    μ = ⦇ `μ  ⟨ k ⟩ ⦈
  gen𝔾 k (f ⊕ g) μ = ⦇ {!!} ⦈ ∥ {!!}
  gen𝔾 k (f ⊗ g) μ = {!!}
  gen𝔾 k I        μ = ⦇ `μ μ ⦈

  

  
