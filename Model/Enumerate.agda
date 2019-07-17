open import Model.Base
open import Model.Data
open import Model.Combinators

open import Data.Nat hiding (_⊔_)
open import Data.List

open import Function
open import Level renaming (zero to zeroL ; suc to sucL)

-- Contains an enumerative interpretation of the abstract generator type
module Model.Enumerate where
    
    -- Interpret a generator as a function from recursive depth to List of elements
  enumerate :
    ∀ {ℓ k} {i : Set k} {a : Set ℓ} {t : i → Set ℓ}
    → ((y : i) → Gen (t y) t y) → (x : i) → Gen a t x → ℕ → List a
  enumerate tg x g zero = []
  enumerate tg x (Pure x₁) (suc n) = [ x₁ ]
  enumerate tg x (Ap {y = y} g₁ g₂) (suc n) =
    concatMap (λ f → map f (enumerate tg y g₂ (suc n))) (enumerate tg x g₁ (suc n))
  enumerate tg x (Bind {y = y} g₁ fg) (suc n) =
    concatMap (λ v → enumerate tg x (fg v) (suc n)) (enumerate tg y g₁ (suc n))
  enumerate tg x (Or g₁ g₂) (suc n) =
    merge (enumerate tg x g₁ (suc n)) (enumerate tg x g₂ (suc n))
  enumerate tg x (μ .x) (suc n) = enumerate tg x (tg x) n
  enumerate tg x None (suc n) = []
  enumerate tg x (Call y g) (suc n) = enumerate g y (g y) (suc n)

  -- Interpretation of closed generators
  ⟨_⟩ : ∀ {ℓ k} {i : Set k} {f : i → Set ℓ} → ((x : i) → 𝔾 f x) → (x : i) → ℕ → List (f x)
  ⟨ g ⟩ x = enumerate g x (g x)
