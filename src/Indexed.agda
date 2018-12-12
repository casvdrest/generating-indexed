{-# OPTIONS --type-in-type #-}

open import Size 

open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_; _+_)
open import Data.Vec hiding (map)
open import Data.List hiding (fromMaybe; map)
open import Data.Maybe hiding (fromMaybe; map)

open import Codata.Colist
open import Codata.Thunk hiding (map)

open import src.Enumerable
open import src.Data
open import src.Product
open import src.Nonempty

module src.Indexed where 

  enumFin' : ∀ {i : Size} → (n : ℕ) → Colist (Fin n) i
  enumFin' zero = []
  enumFin' (suc n) = zero ∷ λ where .force → map suc (enumFin' n)

  instance
    enumFin : IEnumerable Fin
    enumFin = record { enumI = enumFin' }

  cons' : ∀ {a : Set} {n : ℕ} → a ⊗ Vec a n → Vec a (suc n)
  cons' (x , xs) = x ∷ xs

  enumVec' : ∀ {a : Set} {i : Size} ⦃ _ : Enumerable a ⦄ → (n : ℕ) → Colist (Vec a n) i
  enumVec' zero = [] ∷ λ where .force → []
  enumVec' {a} (suc n) = map cons' (inhabitants a × enumVec'{a} n)

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
  yield≤ (suc n) (suc m) = cong≤ (yield≤ (suc n) m)

  ≤₊_ : ℕ ⊗ ℕ → Set
  ≤₊ (n , m) = n ≤ (m + n)

  foo : ∀ {i : Size} → (t : ℕ ⊗ ℕ) → Colist (≤₊ t) ∞
  foo (x , y) = yield≤ x y ∷ λ where .force → [] 

  instance
    enum≤₊ : IEnumerable (≤₊_)
    enum≤₊ = record { enumI = foo }
{-
  enumIndex : ∀ {a : Set} {i : Size} {P : a → Set} ⦃ _ : IEnumerable P ⦄ → a → Colist₊ (Σ a P) i
  enumIndex {P = P} x with inhabitants' P x
  enumIndex {P = P} x | [] = {!!}
  enumIndex {P = P} x | y ∷ ys = map₊ (_,_ x) (toColist₊ y (ys .force))
  
  instance
    enumΣ : ∀ {a : Set} ⦃ _ : Enumerable a ⦄ {P : a → Set} ⦃ _ : IEnumerable P ⦄
            → Enumerable (Σ a P)
    enumΣ {a} {P} = record { enum = diagonal (map enumIndex (inhabitants a)) }
-}
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
{-
  -- Given some n : ℕ, yield all possible proofs of the form `n≤?`
  n≤? : ∀ {i : Size} → Colist (Σ (ℕ ⊗ ℕ) ≤₊_) i
  n≤? = inhabitants (Σ (ℕ ⊗ ℕ) ≤₊_)
-}
-- ==== TODO ===
-- * fix termination issues with enumeration of pairs & lists (possibly using sized types)
-- * Enumeration for the ≤ datatype and sorted lists
-- * Enumeration of well scoped lambda terms
-- * Investigate the relation between various implementations of `IEnumerable ≤`, and consequently of `IEnumerable Sorted`
-- * Q: How does the work in this thesis tie in with existing work (constrained lambda term generation (claessen et al.), FEAT, smallcheck etc...)

