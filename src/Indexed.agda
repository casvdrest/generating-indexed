{-# OPTIONS --type-in-type #-}

open import Size 

open import Data.Nat hiding (_≤_)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _+_)
open import Data.Vec hiding (map; [_])
open import Data.List hiding (fromMaybe; map; [_])
open import Data.Maybe hiding (fromMaybe; map)
open import Data.Empty

open import Codata.Colist
open import Codata.Thunk hiding (map)

import Relation.Binary.PropositionalEquality as Eq'
open Eq' using (_≡_; refl; cong; sym)
open Eq'.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

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
  enumVec' {a} (suc n) = map cons' (inhabitants a × enumVec' {a} n)

  instance
    enumVec : ∀ {a : Set} ⦃ _ : Enumerable a ⦄ → IEnumerable (Vec a)
    enumVec = record { enumI = enumVec' }

  vecToList : ∀ {a : Set} {n : ℕ} → Vec a n → List a
  vecToList [] = []
  vecToList (x ∷ xs) = x ∷ vecToList xs

  listN : ∀ {a : Set} {i : Size} ⦃ _ : Enumerable a ⦄ → Colist₊ a ∞ → ℕ → Thunk (Colist₊ (List a)) i
  listN xs zero = λ where .force → [ [] ]
  listN {a} xs (suc n) with map vecToList (inhabitants' (Vec a) (suc n))
  listN {a} xs (suc n) | [] = λ where .force → [ [] ]
  listN {a} xs (suc n) | y ∷ ys = λ where .force → toColist₊ y (ys .force)

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
  
  lt-right-subst : ∀ {n m k : ℕ} → (m ≡ k) → n ≤ m → n ≤ k
  lt-right-subst refl prf = prf

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

  instance
    enum≤ₛ : ∀ {n : ℕ} → IEnumerable (_≤_ n)
    enum≤ₛ {n} = record { enumI = λ m → fromMaybe (≤proof n m) }

  instance
    enum≤ : ∀ {n : ℕ} → IEnumerable (_≤_ n ∘ _+_ n)
    enum≤ {n} = record { enumI = λ m → lt-right-subst (+-comm m n) (yield≤ n m) ∷ λ where .force → []}

  ≤-conv : ∀ {n m : ℕ} → n ≤ m → Σ ℕ (λ k → (n ≤ (n + k)) ⊗ (m ≡ n + k) )
  ≤-conv {zero} {m} z≤n = m , (z≤n , refl)
  ≤-conv {suc n} {zero} ()
  ≤-conv {suc n} {suc m} (n≤m p) with ≤-conv p
  ≤-conv {suc n} {suc .(n + k)} (n≤m p) | k , (x , refl) = k , (n≤m x , refl)
  
  sortedProofₛ : (xs : List ℕ) → Maybe (Sorted xs)
  sortedProofₛ [] = just nil
  sortedProofₛ (x ∷ []) = just single
  sortedProofₛ (x ∷ y ∷ xss) with ≤proof x y
  sortedProofₛ (x ∷ y ∷ xss) | just prf₁ with sortedProofₛ (y ∷ xss) 
  sortedProofₛ (x ∷ y ∷ xss) | just prf₁ | just prf₂ = just (step prf₁ prf₂)
  sortedProofₛ (x ∷ y ∷ xss) | just prf₁ | nothing = nothing
  sortedProofₛ (x ∷ y ∷ xss) | nothing = nothing

  diffList : ℕ → List ℕ → List ℕ
  diffList n [] = []
  diffList n (x ∷ xs) = n + x ∷ diffList (n + x) xs

  extractList : ∀ {xs : List ℕ} → Sorted xs → List ℕ
  extractList {xs} _ = xs

  asSortedList : (n : ℕ) → (xs : List ℕ) → Sorted (diffList n xs)
  asSortedList _ [] = nil
  asSortedList _ (x ∷ []) = single
  asSortedList n (x ∷ y ∷ xs) with yield≤ (n + x) y   
  ... | prf = step (lt-right-subst (+-comm y (n + x)) prf) (asSortedList (n + x) (y ∷ xs))

  instance
    enumSortedₛ : IEnumerable Sorted
    enumSortedₛ = record { enumI = λ xs → fromMaybe (sortedProofₛ xs) }

  instance
    enumSorted : IEnumerable (Sorted ∘ diffList 0)
    enumSorted = record { enumI = λ xs → asSortedList 0 xs ∷ λ where .force → [] }

