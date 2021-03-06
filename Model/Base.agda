open import Model.Data
open import Level renaming (suc to sucL ; zero to zeroL)

open import Data.Nat hiding (_⊔_)
open import Data.Bool
open import Data.List using (List; map; [_]; concatMap; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Unit
open import Data.Fin hiding (lift; _+_)
open import Data.Maybe using (Maybe; just; nothing)

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Contains the basic generator types necessary to define generators
module Model.Base where

  -- The type of abstract generators 
  data Gen {ℓ k} {i : Set k} : 
    Set ℓ → (i → Set ℓ) → i → Set (sucL k ⊔ sucL ℓ) where

    -- Lifts values into the Genᵢ type
    Pure : ∀ {a : Set ℓ} {t : i → Set ℓ} {x : i} → a → Gen a t x

    -- Aplies the results of one generator to the results of another
    Ap   : ∀ {a b : Set ℓ} {t : i → Set ℓ} {x : i} {y : i} 
          → Gen (b → a) t x → Gen b t y → Gen a t x

    -- Monadic bind for generators
    Bind : ∀ {a b : Set ℓ} {t : i → Set ℓ} {x : i} {y : i}
          → Gen a t y → (a → Gen b t x) → Gen b t x

    -- Choice between generators
    Or  : ∀ {a : Set ℓ} {t : i → Set ℓ} {x : i}
         → Gen a t x → Gen a t x → Gen a t x

    -- Recursive positions
    μ    : ∀ {a : i → Set ℓ} → (x : i) → Gen (a x) a x

    -- Empty generator
    None : ∀ {a : Set ℓ} {t : i → Set ℓ} {x : i} → Gen a t x

    -- Call to external indexed generator
    Call : ∀ {j : Set k} {t : i → Set ℓ} {s : j → Set ℓ} {x : i} → (y : j) → ((y' : j) → Gen (s y') s y') → Gen (s y) t x

  -- The type of closed indexed generators
  𝔾 : ∀ {ℓ k} {i : Set k} → (i → Set ℓ) → i → Set (sucL k ⊔ (sucL ℓ))
  𝔾 f x = Gen (f x) f x

  -- Marks a call to a non-indexed generator
  Call' : ∀ {ℓ k} {I : Set k} {A : I → Set ℓ} {B : (Lift k ⊤) → Set ℓ} {i : I}
        → ((Lift k ⊤) → Gen {ℓ} {k} (B (lift tt)) B (lift tt))
        → Gen (B (lift tt)) A i
  Call' g = Call (lift tt) g

  -- Marks a recursive position in a non-indexed generator
  μ' : ∀ {ℓ k} {T : Lift k ⊤ → Set ℓ} → Gen (T (lift tt)) T (lift tt)
  μ' = μ (lift tt)

  -- Indexed functions
  co𝔾 : ∀ {ℓ k} {i : Set k} → (i → Set ℓ) → i →  Set (sucL k ⊔ (sucL ℓ))
  co𝔾 {ℓ} {k} f x = ∀ {b : ⊤ → Set ℓ} → 𝔾 b tt → 𝔾 (λ x → f x → b tt) x

