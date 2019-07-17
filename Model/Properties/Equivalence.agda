open import Data.Product
open import Data.Nat
open import Data.Unit

open import Function

open import Model.Base
open import Model.Properties.Completeness

module Model.Properties.Equivalence where

  -- Equivalence between generators: g₁ and g₂ are equivalent if
  -- for every x, if g₁ produces x, then g₂ produces x as well,
  -- and vice versa.
  --
  -- Currently only defined for non-indexed generators
  _∼_ : ∀ {a : ⊤ → Set} (g₁ g₂ : ⊤ → 𝔾 a tt) → Set
  _∼_ g₁ g₂ =
      (∀ {x} → g₁ tt ∣ g₁ ↝ x → g₂ tt ∣ g₂ ↝ x)
    × (∀ {x} → g₂ tt ∣ g₂ ↝ x → g₁ tt ∣ g₁ ↝ x)
  
  -- If two generators are complete and generate the same type,
  -- then they are equivalent
  Complete→eq :
    ∀ {a : ⊤ → Set} {g₁ g₂ : ⊤ → 𝔾 a tt}
    → Complete (g₁  tt) g₁ → Complete (g₂ tt) g₂
    → g₁ ∼ g₂
  Complete→eq p₁ p₂ =
    (λ _ → p₂) , λ _ → p₁
  
  -- Equivalence is reflexive
  ~-reflexive :
    ∀ {a : ⊤ → Set} {g : ⊤ → 𝔾 a tt}
    → g ∼ g
  ~-reflexive = id , id

  -- Equivalence is symmetric
  ~-symmetric :
    ∀ {a : ⊤ → Set} {g₁ g₂ : ⊤ → 𝔾 a tt}
    → g₁ ∼ g₂
    → g₂ ∼ g₁
  ~-symmetric (f , g) = g , f

  -- Equivalence is transitive
  ~-transitive :
    ∀ {a t : ⊤ → Set} {g₁ g₂ g₃ : ⊤ → 𝔾 a tt} 
    → g₁ ∼ g₂ → g₂ ∼ g₃
    → g₁ ∼ g₃
  ~-transitive (f₁ , g₁) (f₂ , g₂) = f₂ ∘ f₁ , g₁ ∘ g₂
