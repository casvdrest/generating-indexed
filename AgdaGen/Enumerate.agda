open import AgdaGen.Base
open import AgdaGen.Data

open import Data.Nat hiding (_⊔_)
open import Data.List

open import Function
open import Level renaming (zero to zeroL ; suc to sucL)

module AgdaGen.Enumerate where

  mutual
    -- Interpretation function for generators. Interprets a a value of the Gen type as a
    -- function from `ℕ` to `List a`.
    --
    -- The first parameter is the generator to be interpreted, the second parameter is a
    -- closed generator that is referred to by recursive positions.
    interpret : ∀ {ℓ k} {a t : Set ℓ} → Gen {ℓ} {k} a t → 𝔾 t → ℕ → List a
    interpret (g         ) tg zero = []
    interpret (Or g₁ g₂  ) tg (suc n) =
      merge (interpret g₁ tg (suc n)) (interpret g₂ tg (suc n))
    interpret (Ap g₁ g₂  ) tg (suc n) =
      concatMap (λ f → map f (interpret g₂ tg (suc n)))
        (interpret g₁ tg (suc n))
    interpret (Pure x    ) tg (suc n) = [ x ]
    interpret (Bind g₁ g₂) tg (suc n) =
      (flip concatMap) (interpret g₁ tg (suc n))
        (λ x → interpret (g₂ x) tg (suc n))
    interpret (None      ) tg (suc n) = []
    interpret (μ         ) tg (suc n) =
      interpret tg tg n
    interpret (` g       ) tg (suc n) =
      interpret g g (suc n)
    interpret ⟨ x ` g ⟩ tg (suc n) =
      interpretᵢ g x (g x) (suc n)

    -- Interpret a generator as a function from recursive depth to List of elements
    interpretᵢ :
      ∀ {ℓ k} {i : Set k} {a t : i → Set ℓ}
      → ((y : i) → Genᵢ t t y) → (x : i) → Genᵢ a t x → ℕ → List (a x)
    interpretᵢ tg x g                    zero   = []
    interpretᵢ tg x (Noneᵢ )            (suc n) = []
    interpretᵢ tg x (Pureᵢ v)           (suc n) = [ v ]
    interpretᵢ tg x (Apᵢ {y = y} g₁ g₂) (suc n) =
      concatMap (λ f → map f (interpretᵢ tg y g₂ (suc n) ))
        (interpretᵢ tg x g₁ (suc n))
    interpretᵢ tg x (Bindᵢ {y = y} g f) (suc n) =
      concatMap (λ v → interpretᵢ tg x (f v) (suc n))
        (interpretᵢ tg y g (suc n))
    interpretᵢ tg x (Orᵢ g₁ g₂)         (suc n) =
      merge (interpretᵢ tg x g₁ (suc n))
        (interpretᵢ tg x g₂ (suc n))
    interpretᵢ tg x (μᵢ .x)             (suc n) =
      interpretᵢ tg x (tg x) n
    interpretᵢ tg x (Call g)            (suc n) =
      interpret g g (suc n)
    interpretᵢ tg x (Callᵢ i g)         (suc n) =
      interpretᵢ g i (g i) (suc n)

  -- Interpret a closed generator as a function from `ℕ` to `List a`
  ⟨_⟩ : ∀ {ℓ k} {a : Set ℓ} → Gen {ℓ} {k} a a → ℕ → List a
  ⟨ g ⟩ = interpret g g

  -- Interpretation of closed indexed generators
  ⟨_⟩ᵢ : ∀ {ℓ k} {i : Set k} {f : i → Set ℓ} → ((x : i) → 𝔾ᵢ f x) → (x : i) → ℕ → List (f x)
  ⟨ g ⟩ᵢ x = interpretᵢ g x (g x)

  -- Type of eneumerations
  Enum : ∀ {ℓ} → Set ℓ → Set ℓ
  Enum a = ℕ → List a

  -- Generator interpration as enumerations
  instance
    ⟦⟧≡Enum : ∀ {ℓ k} → ⟦Generator⟧ {ℓ} {k} Enum
    ⟦⟧≡Enum =
      record { ⟦_⟧gen  = ⟨_⟩
             ; ⟦_⟧genᵢ = ⟨_⟩ᵢ
             }
