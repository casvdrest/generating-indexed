open import Data.Product
open import Data.Nat

open import Function

open import AgdaGen.Base
open import AgdaGen.Properties

module AgdaGen.Equivalence where

  -- Equivalence between generators: g₁ and g₂ are equivalent if
  -- for every x, if g₁ produces x, then g₂ produces x as well,
  -- and vice versa. 
  _∼_ : ∀ {a : Set} (g₁ g₂ : 𝔾 a) → Set
  _∼_ g₁ g₂ =
      (∀ {x} → g₁ ∣ g₁ ↝ x → g₂ ∣ g₂ ↝ x)
    × (∀ {x} → g₂ ∣ g₂ ↝ x → g₁ ∣ g₁ ↝ x)
  
  -- If two generators are complete and generate the same type,
  -- then they are equivalent
  Complete→eq : ∀ {a : Set} {g₁ g₂ : 𝔾 a}
                → Complete g₁ g₁ → Complete g₂ g₂
                ---------------------------------
                → g₁ ∼ g₂
  Complete→eq p₁ p₂ =
    (λ _ → p₂) , λ _ → p₁
  
  -- Equivalence is reflexive
  ~-reflexive : ∀ {a : Set} {g : 𝔾 a}
               → g ∼ g
  ~-reflexive = id , id

  -- Equivalence is symmetric
  ~-symmetric : ∀ {a : Set} {g₁ g₂ : 𝔾 a}
                → g₁ ∼ g₂
                → g₂ ∼ g₁
  ~-symmetric (f , g) = g , f

  -- Equivalence is transitive
  ~-transitive : ∀ {a t : Set} {g₁ g₂ g₃ : 𝔾 a} 
                 → g₁ ∼ g₂ → g₂ ∼ g₃
                 → g₁ ∼ g₃
  ~-transitive (f₁ , g₁) (f₂ , g₂) = f₂ ∘ f₁ , g₁ ∘ g₂

