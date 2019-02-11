open import Data.Product
open import Data.Nat

open import Function

open import src.Gen.Base
open import src.Gen.Properties

open import Category.Applicative

module src.Gen.Equivalence where

  open RawApplicative ⦃...⦄

  -- Equivalence between generators: g₁ and g₂ are equivalent if
  -- for every x, if g₁ produces x, then g₂ produces x as well,
  -- and vice versa. 
  _∼_ : ∀ {a} (g₁ g₂ : ∀ {n} → 𝔾 a n) → Set
  g₁ ∼ g₂ =
      (∀ {x} → g₁ ↝ x → g₂ ↝ x)
    × (∀ {x} → g₂ ↝ x → g₁ ↝ x)

  -- If two generators are complete and generate the same type,
  -- then they are equivalent
  Complete→eq : ∀ {a} {g₁ g₂ : ∀ {n} → 𝔾 a n}
                → Complete g₁ → Complete g₂
                ---------------------------
                → g₁ ∼ g₂
  Complete→eq p₁ p₂ =
    (λ _ → p₂) , λ _ → p₁

  -- Equivalence is reflexive
  ~-reflexive : ∀ {a : Set} {g : ∀ {n : ℕ} → 𝔾 a n}
               → g ∼ g
  ~-reflexive = id , id

  -- Equivalence is symmetric
  ~-symmetric : ∀ {a : Set} {g₁ g₂ : ∀ {n : ℕ} → 𝔾 a n} 
                → g₁ ∼ g₂
                → g₂ ∼ g₁
  ~-symmetric (f , g) = g , f

  -- Equivalence is transitive
  ~-transitive : ∀ {a : Set} {g₁ g₂ g₃ : ∀ {n : ℕ} → 𝔾 a n}
                 → g₁ ∼ g₂ → g₂ ∼ g₃
                 → g₁ ∼ g₃
  ~-transitive (f₁ , g₁) (f₂ , g₂) = f₂ ∘ f₁ , g₁ ∘ g₂
