open import Data.Product

open import src.Gen.Base
open import src.Gen.Properties 

module src.Gen.Equivalence where

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

  
