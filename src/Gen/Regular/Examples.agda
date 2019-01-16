open import src.Data
open import src.Gen.Base

open import Data.Bool
open import Data.Maybe using (just; nothing; Maybe)
open import Data.Nat
open import Data.List

open import Category.Applicative
open import Category.Functor

open import Relation.Binary.PropositionalEquality

module src.Gen.Regular.Examples where

  open RawApplicative ⦃...⦄ using (_⊛_; pure)

  bool : ⟪ 𝔾 Bool ⟫
  bool _ = ⦇ true  ⦈
         ∥ ⦇ false ⦈

  maybe : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 (Maybe a) ⟫
  maybe a _ = ⦇ nothing    ⦈
            ∥ ⦇ just ⟨ a ⟩ ⦈

  nat : ⟪ 𝔾 ℕ ⟫
  nat μ = ⦇ zero  ⦈
        ∥ ⦇ suc μ ⦈

  list : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 (List a) ⟫
  list a μ = ⦇ [] ⦈
           ∥ ⦇ ⟨ a ⟩ ∷ μ ⦈

  pair : ∀ {a b} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫
         → ⟪ 𝔾 (a ⊗ b) ⟫
  pair a b _ = ⦇ ⟨ a ⟩ , ⟨ b ⟩ ⦈


  either : ∀ {a b} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫
           → ⟪ 𝔾 (a ⊕ b) ⟫
  either a b _ = ⦇ inl ⟨ a ⟩ ⦈
               ∥ ⦇ inr ⟨ b ⟩ ⦈

  
