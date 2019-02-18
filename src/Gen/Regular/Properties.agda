{-# OPTIONS --type-in-type #-}

open import src.Gen.Base
open import src.Gen.Properties
open import src.Gen.Regular.Generic
open import src.Gen.Regular.Isomorphism
open import src.Data using (_∈_; here; Π)

open import Data.Unit hiding (_≤_)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum
open import Data.Nat
open import Data.List

open import Category.Monad

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

module src.Gen.Regular.Properties where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  ------ U Combinator (Unit) ------

  ugen-complete : ∀ {g : Reg}
                  -------------------------
                  → Complete (ugen {a = μ g})
  ugen-complete = 1 , here
  
  
  ------ ⊕ combinator (Coproduct) ------

  -- If 'x' is produced by a generator, 'inj₁ x' is produced by generator derived
  -- from the coproduct of that generator with any other generator
  ⊕gen-complete-left : ∀ {a : Set} {f g : Reg}
                         {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                         {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                         {x : ⟦ f ⟧ a} → g₁ ↝ x
                       -------------------------------------
                       → ⊕gen {f = f} {g = g} g₁ g₂ ↝ inj₁ x
  ⊕gen-complete-left {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-left {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₁} p)

  -- If 'y' is produced by a generator, 'inj₂ y' is produced by the generator
  -- derived from the coproduct of any generator with that generator. 
  ⊕gen-complete-right : ∀ {a : Set} {f g : Reg}
                          {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                          {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                        → {y : ⟦ g ⟧ a} → g₂ ↝ y
                        -------------------------------------
                        → ⊕gen {f = f} {g = g} g₁ g₂ ↝ inj₂ y
  ⊕gen-complete-right {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-right {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₂} p)

  -- Given that its operands are complete, the generator derived from
  -- a coproduct is complete
  ⊕gen-Complete : ∀ {a : Set} {f g : Reg}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                  → Complete g₁ → Complete g₂
                  ---------------------------------------
                  → Complete (⊕gen {f = f} {g = g} g₁ g₂)
  ⊕gen-Complete {f = f} {g = g} {g₁} {g₂} p₁ p₂ {inj₁ x} =
    ⊕gen-complete-left {f = f} {g = g} {g₁ = g₁} {g₂ = g₂} p₁
  ⊕gen-Complete {f = f} {g = g} {g₁} {g₂} p₁ p₂ {inj₂ y} =
    ⊕gen-complete-right {f = f} {g = g} {g₁ = g₁} {g₂ = g₂} p₂

  
  ------ ⊗ combinator (Product) ------

  -- If both operands are complete, the generator derived from a product
  -- is complete as well. 
  ⊗gen-complete : ∀ {a : Set} {f g : Reg}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                    {x : ⟦ f ⟧ a} {y : ⟦ g ⟧ a}
                  → (p₁ : g₁ ↝ x) → (p₂ : g₂ ↝ y)
                  --------------------------------------
                  → ⊗gen {f = f} {g = g} g₁ g₂ ↝ (x , y)
  ⊗gen-complete {g₁ = g₁} {g₂ = g₂} p1 p2 = ⊛-complete {f = g₁} {g = g₂} p1 p2

  -- Completeness for product, but now with the quantification over arbitrary values
  -- hidden. 
  ⊗gen-Complete : ∀ {a : Set} {f g : Reg}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                  → (p₁ : Complete g₁) → (p₂ : Complete g₂)
                  -----------------------------------------------------------
                  → Complete (⊗gen {f = f} {g = g} g₁ g₂)
  ⊗gen-Complete {f = f} {g = g} {g₁} {g₂} p₁ p₂  =
    ⊗gen-complete {f = f} {g = g} {g₁ = g₁} {g₂ = g₂} p₁ p₂


  ------ K combinator (constants) ------

  -- The generator derived from a constant is complete if
  -- the generator for that constant is complete
  kgen-complete : ∀ {a b : Set} {x : b} {f : ⟪ 𝔾 b ⟫}
                  → ⟨ f ⟩ ↝ x
                  --------------------------------------------
                  → kgen {a = a} {g = f} ↝ x
  kgen-complete (p , snd) = p , snd

  postulate depth-monotonicity : ∀ {a : Set} {n m : ℕ} → n ≤ m → 𝔾 a n → 𝔾 a m 

  {-# TERMINATING #-}
  deriveGen-complete : ∀ {f g : Reg} {x : ⟦ f ⟧ (μ g)}
                       → deriveGen {f = f} {g = g} ⟨ deriveGen {f = g} {g = g} ⟩ ↝ x
  deriveGen-complete {U} {g} = ugen-complete {g = g}
  deriveGen-complete {f₁ ⊕ f₂} {g} =
    ⊕gen-Complete {f = f₁} {g = f₂}
      {g₁ = deriveGen {f = f₁} ⟨ deriveGen {f = g} ⟩}
      {g₂ = deriveGen {f = f₂} ⟨ deriveGen {f = g} ⟩}
      (deriveGen-complete {f = f₁})
      (deriveGen-complete {f = f₂})
  deriveGen-complete {f₁ ⊗ f₂} {g} =
    ⊗gen-Complete {f = f₁} {g = f₂}
      {g₁ = deriveGen {f = f₁} ⟨ deriveGen {f = g} ⟩}
      {g₂ = deriveGen {f = f₂} ⟨ deriveGen {f = g} ⟩}
      (deriveGen-complete {f = f₁})
      (deriveGen-complete {f = f₂})
  deriveGen-complete {I} {g} {x = `μ x} with deriveGen-complete {f = g} {g = g} {x = x}
  ... | n , prf = suc n , (∈-rewr (sym ++-right-ident) (map-preserves-elem {f = `μ} prf))
  deriveGen-complete {K x} {g} = {!!}


  --=============================================--
  ------ Completeness for derived generators ------
  --=============================================--

  deriveGen-Complete : ∀ {f : Reg} → Complete ⟨ deriveGen {f = f} {g = f} ⟩
  deriveGen-Complete {f} {x} with deriveGen-complete {f = f} {g = f} {x = x}
  deriveGen-Complete {f} {x} | n , p = suc n , p
