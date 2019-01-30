{-# OPTIONS --type-in-type #-}

open import src.Gen.Base
open import src.Gen.Properties
open import src.Gen.Regular.Generic
open import src.Gen.Regular.Isomorphism
open import src.Data using (_∈_; here; Π)

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.List

open import Category.Monad

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

module src.Gen.Regular.Properties where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  ------ U Combinator (Unit) ------

  ugen-complete : ∀ {n : ℕ} {a : Set}
                  -------------------------
                  → Complete (ugen {a = a})
  ugen-complete {n} = n , here
  
  
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
  -- a coproduct is com
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
                  → depth {f = g₁} p₁ ≡ depth {f = g₂} p₂
                  --------------------------------------
                  → ⊗gen {f = f} {g = g} g₁ g₂ ↝ (x , y)
  ⊗gen-complete {g₁ = g₁} {g₂ = g₂}  p1 p2 = ⊛-complete {f = g₁} {g = g₂} p1 p2

  -- Completeness for product, but now with the quantification over arbitrary values
  -- hidden. 
  ⊗gen-Complete : ∀ {a : Set} {f g : Reg}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                  → (p₁ : Complete g₁) → (p₂ : Complete g₂)
                  → (∀ {x y} → depth {f = g₁} {x} p₁ ≡ depth {f = g₂} {y} p₂)
                  -----------------------------------------------------------
                  → Complete (⊗gen {f = f} {g = g} g₁ g₂)
  ⊗gen-Complete {f = f} {g = g} {g₁} {g₂} p₁ p₂ dp =
    ⊗gen-complete {f = f} {g = g} {g₁ = g₁} {g₂ = g₂} p₁ p₂ dp
 
  ------ K combinator (constants) ------

  -- The generator derived from a constant is complete if
  -- the generator for that constant is complete
  kgen-complete : ∀ {a b : Set} {x : b} {f : ⟪ 𝔾 b ⟫}
                  → ⟨ f ⟩ ↝ x
                  --------------------------------------------
                  → kgen {a = a} {g = f} ↝ x
  kgen-complete (p , snd) = p , snd

-- ### TODO ###
--
-- * prove completeness for recursion
-- * Assemble lemma's into proof about
--   generators derived from pattern functors
