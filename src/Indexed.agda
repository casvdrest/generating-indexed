{-# OPTIONS --type-in-type #-}

open import Agda.Builtin.Coinduction

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_; _+_)
open import Data.Vec
open import Data.List hiding (fromMaybe)
open import Data.Maybe hiding (fromMaybe)

open import src.Enumerable
open import src.Colist

module src.Indexed where 

  enumFin' : (n : ℕ) → Colist (Fin n)
  enumFin' zero = []
  enumFin' (suc n) = zero ∷ ♯ comap suc (enumFin' n)

  instance
    enumFin : IEnumerable Fin
    enumFin = record { enumI = enumFin' }

  cons' : ∀ {a : Set} {n : ℕ} → a ⊗ Vec a n → Vec a (suc n)
  cons' (x , xs) = x ∷ xs

  enumVec' : ∀ {a : Set} ⦃ _ : Enumerable a ⦄ → (n : ℕ) → Colist (Vec a n)
  enumVec' zero = [] ∷ ♯ []
  enumVec' {a} (suc n) = comap cons' (inhabitants a × enumVec'{a} n)

  instance
    enumVec : ∀ {a : Set} ⦃ _ : Enumerable a ⦄ → IEnumerable (Vec a)
    enumVec = record { enumI = enumVec' }

  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ} → 0 ≤ n
    n≤m : ∀ {n m : ℕ} → n ≤ m → suc n ≤ suc m

  cong≤ : ∀ {n m : ℕ} → n ≤ m → n ≤ suc m
  cong≤ z≤n = z≤n
  cong≤ (n≤m prf) = n≤m (cong≤ prf)

  yield≤ : (n m : ℕ) → n ≤ (m + n)
  yield≤ zero m = z≤n
  yield≤ (suc n) zero = n≤m (yield≤ n zero)
  yield≤ (suc n) (suc m) = cong≤ (yield≤ (suc n) m

  ≤₊_ : ℕ ⊗ ℕ → Set
  ≤₊ (n , m) = n ≤ (m + n)

  foo : (t : ℕ ⊗ ℕ) → Colist (≤₊ t)
  foo (x , y) = yield≤ x y ∷ ♯ [] 

  instance
    enum≤₊ : IEnumerable (≤₊_)
    enum≤₊ = record { enumI = foo }

  enumIndex : ∀ {a : Set} {P : a → Set} ⦃ _ : IEnumerable P ⦄ → a → Colist (Σ a P)
  enumIndex x = comap (sigma x) (enumI x)
  
  instance
    enumΣ : ∀ {a : Set} ⦃ _ : Enumerable a ⦄ {P : a → Set} ⦃ _ : IEnumerable P ⦄
            → Enumerable (Σ a P)
    enumΣ {a} {P} = record { enum = diagonal (comap enumIndex enum) }

  data Term : ℕ → Set where 
    Var : ∀ {n : ℕ} → Fin (suc n) → Term n
    App : ∀ {n m : ℕ} → Term n → Term m → Term (n ⊔ m)
    Abs : ∀ {n : ℕ} → Term n → Term (suc n)

  data Sorted : List ℕ → Set where
    nil    : Sorted []
    single : ∀ {n : ℕ} → Sorted (n ∷ [])
    step   : ∀ {n m : ℕ} {xs : List ℕ} → n ≤ m → Sorted (m ∷ xs) → Sorted (n ∷ m ∷ xs)

  ≤proof : (n : ℕ) → (m : ℕ) → Maybe (n ≤ m)
  ≤proof zero m = just z≤n
  ≤proof (suc n) zero = nothing
  ≤proof (suc n) (suc m) with ≤proof n m
  ≤proof (suc n) (suc m) | just prf = just (n≤m prf)
  ≤proof (suc n) (suc m) | nothing = nothing

  sortedProofₛ : (xs : List ℕ) → Maybe (Sorted xs)
  sortedProofₛ [] = just nil
  sortedProofₛ (x ∷ []) = just single
  sortedProofₛ (x ∷ y ∷ xss) with ≤proof x y
  sortedProofₛ (x ∷ y ∷ xss) | just prf₁ with sortedProofₛ (y ∷ xss) 
  sortedProofₛ (x ∷ y ∷ xss) | just prf₁ | just prf₂ = just (step prf₁ prf₂)
  sortedProofₛ (x ∷ y ∷ xss) | just prf₁ | nothing = nothing
  sortedProofₛ (x ∷ y ∷ xss) | nothing = nothing

  instance
    enumSortedₛ : IEnumerable Sorted
    enumSortedₛ = record { enumI = λ xs → fromMaybe (sortedProofₛ xs) }

  -- Given some n : ℕ, yield all possible proofs of the form `n≤?`
  n≤? : Colist (Σ (ℕ ⊗ ℕ) ≤₊_)
  n≤? = inhabitants (Σ (ℕ ⊗ ℕ) ≤₊_)

-- ==== TODO ===
-- * fix termination issues with enumeration of pairs & lists (possibly using sized types)
-- * Enumeration for the ≤ datatype and sorted lists
-- * Enumeration of well scoped lambda terms
-- * Investigate the relation between various implementations of `IEnumerable ≤`, and consequently of `IEnumerable Sorted`
-- * Q: How does the work in this thesis tie in with existing work (constrained lambda term generation (claessen et al.), FEAT, smallcheck etc...)

