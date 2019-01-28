{-# OPTIONS --type-in-type #-}

open import src.Gen.Base
open import src.Gen.Properties
open import src.Gen.Regular.Generic
open import src.Data using (_∈_; here)

open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.List

open import Category.Monad

open import Relation.Binary.PropositionalEquality

module src.Gen.Regular.Properties where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  ------ U Combinator (Unit) ------

  ugen-complete : ∀ {n : ℕ} {a : Set} → ugen {n} {a} ↝ tt
  ugen-complete {n} = (n , refl) , here
  

  ------ ⊕ combinator (Coproduct) ------

  constr-preserves-elem : ∀ {n : ℕ} {a b : Set} {f : a → b}
                            {g : 𝔾 a n} {x : a}
                          → g ↝ x
                          ---------------
                          → ⦇ f g ⦈ ↝ f x
  constr-preserves-elem {f = f} (p , elem) =
    p , list-ap-complete {fs = f ∷ []} here elem

  ⊕gen-complete-left : ∀ {n : ℕ} {a : Set} {f g : Reg}
                         {g₁ : 𝔾 (⟦ f ⟧ a) n} {g₂ : 𝔾 (⟦ g ⟧ a) n}
                         {x : ⟦ f ⟧ a} → g₁ ↝ x
                       -------------------------------------
                       → ⊕gen {f = f} {g = g} g₁ g₂ ↝ inj₁ x
  ⊕gen-complete-left p = ∥-complete-left (constr-preserves-elem p)

  ⊕gen-complete-right : ∀ {n : ℕ} {a : Set} {f g : Reg}
                          {g₁ : 𝔾 (⟦ f ⟧ a) n} {g₂ : 𝔾 (⟦ g ⟧ a) n}
                        → {y : ⟦ g ⟧ a} → g₂ ↝ y
                        -------------------------------------
                        → ⊕gen {f = f} {g = g} g₁ g₂ ↝ inj₂ y
  ⊕gen-complete-right p = ∥-complete-right (constr-preserves-elem p)


  ------ ⊗ combinator (Product) ------

  ⊗gen-complete : ∀ {n : ℕ} {a : Set} {f g : Reg}
                    {g₁ : 𝔾 (⟦ f ⟧ a) n} {g₂ : 𝔾 (⟦ g ⟧ a) n}
                    {x : ⟦ f ⟧ a} {y : ⟦ g ⟧ a}
                  → g₁ ↝ x → g₂ ↝ y
                  --------------------------------------
                  → ⊗gen {f = f} {g = g} g₁ g₂ ↝ (x , y)
  ⊗gen-complete p1 p2 = ⊛-complete p1 p2


  ------ K combinator (constants) ------

  kgen-complete : ∀ {n : ℕ} {a b : Set} {x : b} {f : ⟪ 𝔾 b ⟫}
                  → ⟨_⟩ {n = n} f ↝ x
                  --------------------------------------------
                  → _↝_ {n = n} (kgen {a = a} {g = f}) x
  kgen-complete (p , snd) = p , snd


  ------ I combinator (constants) ------

  igen-complete : ∀ {n : ℕ} {a : Set} {f : Reg} {x : ⟦ f ⟧ a} {g : 𝔾 (⟦ f ⟧ a) n} → g ↝ x → igen {f = f} g ↝ x
  igen-complete p = p
