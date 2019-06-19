open import AgdaGen.Data
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

module AgdaGen.Base where

  data Func {ℓ} (A B : Set ℓ) : Set ℓ where
    Store : (A → B) → Func A B 

  mutual
    -- The generator type. The `a` type parameter marks the output type of the
    -- generator. The resulting family is indexed by a type marking the type
    -- of values produced by recursive positions.
    data Gen {ℓ k} : (a : Set ℓ) → (t : Set ℓ) → Set (sucL k ⊔ sucL ℓ) where
  
      -- Marks choice between generators
      Or   : ∀ {a t : Set ℓ} → Gen {ℓ} {k} a t → Gen {ℓ} {k} a t → Gen a t

      -- Applies the values generated by one generator to another
      Ap    : ∀ {a t b : Set ℓ} → Gen {ℓ} {k} (b → a) t → Gen {ℓ} {k} b t  → Gen a t

      -- Lift a single value into the generator type
      Pure  : ∀ {a t : Set ℓ} → a → Gen a t

      -- Monadic bind for generators
      Bind  : ∀ {a b t : Set ℓ} → Gen {ℓ} {k} b t → (b → Gen {ℓ} {k} a t) → Gen a t 

        -- Generator that produces no elements at all. 
      None  : ∀ {a t : Set ℓ} → Gen a t

      -- Marks a recursive positions
      μ     : ∀ {a : Set ℓ} → Gen a a

      -- Call to an external generator. Using this constructor is
      -- only different from including the generator itself if the
      -- called generator contains one or more recursive
      -- positions. 
      `_    : ∀ {a t : Set ℓ} → Gen {ℓ} {k} a a → Gen a t

      ⟨_`_⟩ : ∀ {i : Set k} {p : i → Set ℓ} {t : Set ℓ} → (x : i) → ((x : i) → Genᵢ (p x) p x) → Gen (p x) t

    data Genᵢ {ℓ k} {i : Set k} : 
      (Set ℓ) → (i → Set ℓ) → i → Set (sucL k ⊔ sucL ℓ) where

      -- Lifts values into the Genᵢ type
      Pureᵢ : ∀ {a : Set ℓ} {t : i → Set ℓ} {x : i} → a → Genᵢ a t x

      -- Aplies the results of one generator to the results of another
      Apᵢ   : ∀ {a b : Set ℓ} {t : i → Set ℓ} {x : i} {y : i} 
            → Genᵢ (b → a) t x → Genᵢ b t y → Genᵢ a t x

      -- Monadic bind for generators
      Bindᵢ : ∀ {a b : Set ℓ} {t : i → Set ℓ} {x : i} {y : i}
            → Genᵢ a t y → (a → Genᵢ b t x) → Genᵢ b t x

      -- Choice between generators
      Orᵢ  : ∀ {a : Set ℓ} {t : i → Set ℓ} {x : i}
             → Genᵢ a t x → Genᵢ a t x → Genᵢ a t x

      -- Recursive positions
      μᵢ    : ∀ {a : i → Set ℓ} → (x : i) → Genᵢ (a x) a x

      -- Empty generator
      Noneᵢ : ∀ {a : Set ℓ} {t : i → Set ℓ} {x : i} → Genᵢ a t x

      -- Call to external non-indexed generator
      Call  : ∀ {t : i → Set ℓ} {x : i} {b : Set ℓ} → Gen {ℓ} {k} b b → Genᵢ b t x

      -- Call to external indexed generator
      Callᵢ : ∀ {j : Set k} {t : i → Set ℓ} {s : j → Set ℓ} {x : i} → (y : j) → ((y' : j) → Genᵢ (s y') s y') → Genᵢ (s y) t x

  -- Type synonym for 'closed' generators, e.g. generators whose recursive
  -- positions refer to the same type as the generator as a whole. 
  𝔾 : ∀ {ℓ k} → Set ℓ → Set (Level.suc ℓ ⊔ sucL k)
  𝔾 {ℓ} {k} a = Gen {ℓ} {k} a a

  -- The type of closed indexed generators
  𝔾ᵢ : ∀ {ℓ k} {i : Set k} → (i → Set ℓ) → i → Set (sucL k ⊔ (sucL ℓ))
  𝔾ᵢ f x = Genᵢ (f x) f x
  
  -- Type synonym for 'closed' generators for function types
  co𝔾 : ∀ {ℓ k} → Set ℓ → Set (sucL ℓ ⊔ sucL k)
  co𝔾 {ℓ} {k} a = ∀ {b : Set ℓ} → 𝔾 {ℓ} {k} b → 𝔾 {ℓ} {k} (a → b)

  -- Indexed functions
  co𝔾ᵢ : ∀ {ℓ k} {i : Set k} → (i → Set ℓ) → i →  Set (sucL k ⊔ (sucL ℓ))
  co𝔾ᵢ {ℓ} {k} f x = ∀ {b : Set ℓ} → 𝔾 {ℓ} {k} b → 𝔾ᵢ (λ x → f x → b) x

  -- Generator interpretations. Map generators to any type, parameterized with
  -- the type of values that are generated
  record ⟦Generator⟧ {ℓ k} (T : Set ℓ → Set ℓ) : Set (sucL k ⊔ sucL ℓ) where
    field
      ⟦_⟧gen  : ∀ {A : Set ℓ} → 𝔾 {ℓ} {k} A → T A
    field
      ⟦_⟧genᵢ : ∀ {I : Set k} {P : I → Set ℓ} → ((i : I) → 𝔾ᵢ P i) → (i : I) → T (P i)

  -- Apply a mapping to a generator
  run :
    ∀ {ℓ k} {A : Set ℓ} {T : Set ℓ → Set ℓ}
      ⦃ it : ⟦Generator⟧ {ℓ} {k} T ⦄
    → 𝔾 {ℓ} {k} A → T A
  run ⦃ it = record { ⟦_⟧gen = ⟦_⟧gen ; ⟦_⟧genᵢ = _} ⦄ g =
    ⟦ g ⟧gen

  -- Apply a mapping to an indexed generator
  runᵢ :
    ∀ {ℓ k} {I : Set k} {T : Set ℓ → Set ℓ}
      ⦃ it : ⟦Generator⟧ {ℓ} {k} T ⦄ {P : I → Set ℓ}
    → ((i : I) → 𝔾ᵢ P i) → (i : I) → T (P i)
  runᵢ ⦃ it = record { ⟦_⟧gen = _ ; ⟦_⟧genᵢ = ⟦_⟧genᵢ } ⦄ g =
    ⟦ g ⟧genᵢ
