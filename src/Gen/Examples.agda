open import src.Data
open import src.Gen.Base

open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.List

open import Category.Applicative
open import Category.Functor

open import Relation.Binary.PropositionalEquality

module src.Gen.Examples where

  open RawApplicative ⦃...⦄ using (_⊛_; pure)

  bools : ⟪ 𝔾 Bool ⟫
  bools _ = ⦇ true  ⦈
          ∥ ⦇ false ⦈

  maybes : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 (Maybe a) ⟫
  maybes a _ = ⦇ nothing    ⦈
             ∥ ⦇ just ⟨ a ⟩ ⦈

  nats : ⟪ 𝔾 ℕ ⟫
  nats μ = ⦇ zero  ⦈
         ∥ ⦇ suc μ ⦈

  list : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 (List a) ⟫
  list a μ = ⦇ [] ⦈
           ∥ ⦇ ⟨ a ⟩ ∷ μ ⦈

  
  pairs : ∀ {a b} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫
          → ⟪ 𝔾 (a ⊗ b) ⟫
  pairs a b _ = ⦇ ⟨ a ⟩ , ⟨ b ⟩ ⦈


  eithers : ∀ {a b} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫
            → ⟪ 𝔾 (a ⊕ b) ⟫
  eithers a b _ = ⦇ inl ⟨ a ⟩ ⦈
                ∥ ⦇ inr ⟨ b ⟩ ⦈
  
  prop1 : 𝔾-run nats 10 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  prop1 = refl

  
  prop2 : 𝔾-run bools 10  ≡ true ∷ false ∷ []
  prop2 = refl

  
  prop3 : 𝔾-run (maybes nats) 10 ≡ nothing ∷ just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷ just 4 ∷ just 5 ∷ just 6 ∷ just 7 ∷ just 8 ∷ []
  prop3 = refl

 
  prop4 : 𝔾-run (list nats) 3 ≡ [] ∷ (0 ∷ []) ∷ (0 ∷ 0 ∷ []) ∷ (1 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ []
  prop4 = refl

  
