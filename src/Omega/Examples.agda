open import src.Data
open import src.Omega.Base

open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.List

open import Category.Applicative
open import Category.Functor

open import Relation.Binary.PropositionalEquality

module src.Omega.Examples where

  open RawApplicative ⦃...⦄ using (_⊛_; pure)

  bools : ω Bool
  bools = ⦇ true ⦈
        ∥ ⦇ false ⦈

  maybes : ∀ {ℓ} {a : Set ℓ} → ω a → ω (Maybe a)
  maybes a = ⦇ nothing    ⦈
           ∥ ⦇ just (κ a) ⦈

  nats : ω ℕ → ω ℕ
  nats μ = ⦇ zero  ⦈
         ∥ ⦇ suc μ ⦈

  lists : ∀ {ℓ} {a : Set ℓ} → ω a → ω (List a) → ω (List a)
  lists a μ = ⦇ [] ⦈
            ∥ ⦇ (κ a) ∷ μ ⦈

  pairs : ∀ {ℓ} {a b : Set ℓ} → ω a → ω b → ω (a ⊗ b)
  pairs a b = ⦇ a , b ⦈

  eithers : ∀ {ℓ} {a b : Set ℓ} → ω a → ω b → ω (a ⊕ b)
  eithers a b = ⦇ inl (κ a) ⦈
              ∥ ⦇ inr (κ b) ⦈
  
  prop1 : (fix nats) 10 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  prop1 = refl

  prop2 : bools 10 ≡ true ∷ false ∷ []
  prop2 = refl

  prop3 : maybes (fix nats) 10 ≡ nothing ∷ just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷ just 4 ∷ just 5 ∷ just 6 ∷ just 7 ∷ just 8 ∷ []
  prop3 = refl

  prop4 : fix (lists (fix nats)) 4 ≡ [] ∷ (0 ∷ []) ∷ (0 ∷ 0 ∷ []) ∷ (1 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ []
  prop4 = refl
