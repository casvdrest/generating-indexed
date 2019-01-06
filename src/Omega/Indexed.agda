open import Size 

open import Data.Nat 
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _+_)
open import Data.Vec hiding (map; [_])
open import Data.Bool
open import Data.List hiding (fromMaybe; map)
open import Data.Maybe hiding (fromMaybe; map)
open import Data.Empty
open import Data.Product

import Relation.Binary.PropositionalEquality as Eq'
open Eq' using (_≡_; refl; cong; sym)
open Eq'.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import src.Data
open import src.Omega.Base
open import src.Omega.Examples using (bools)

open import Function

open import Category.Applicative

module src.Omega.Indexed where 

  open RawApplicative ⦃...⦄
  
  fin : ωᵢ Fin → ωᵢ Fin
  fin _ zero    = uninhabited
  fin μ (suc n) = ⦇ zero      ⦈
                ∥ ⦇ suc (μ n) ⦈

  prop : fixᵢ fin 10 10 ≡
      zero ∷ suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero))
    ∷ suc (suc (suc (suc zero))) ∷ suc (suc (suc (suc (suc zero))))
    ∷ suc (suc (suc (suc (suc (suc zero))))) ∷ suc (suc (suc (suc (suc (suc (suc zero))))))
    ∷ suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    ∷ suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ∷ []
  prop = refl

  ≤m : ωᵢ (uncurry _≤_) →  ωᵢ (uncurry _≤_)
  ≤m μ (zero  , m    ) = ⦇ z≤n ⦈
  ≤m μ (n     , zero ) = uninhabited
  ≤m μ (suc n , suc m) = ⦇ s≤s (μ (n , m)) ⦈

  prop1 : fixᵢ ≤m (1 , 2) 10 ≡ [ s≤s z≤n ]
  prop1 = refl

  prop2 : fixᵢ ≤m (2 , 1) 10 ≡ []
  prop2 = refl

  ≤-suc : ∀ {n m : ℕ} → n ≤ m → n ≤ suc m
  ≤-suc z≤n = z≤n
  ≤-suc (s≤s p) = s≤s (≤-suc p)

  ≤n+k : ωᵢ (λ p → fst p ≤ snd p + fst p) → ωᵢ (λ p → fst p ≤ snd p + fst p)
  ≤n+k μ (n , zero ) = ⦇ (≤-reflexive refl) ⦈
  ≤n+k μ (n , suc k) = ⦇ ≤-suc (μ (n , k))  ⦈

  prop3 : fixᵢ ≤n+k (1 , 1) 10 ≡ [ s≤s z≤n ]
  prop3 = refl

  prop4 : fixᵢ ≤n+k (3 , 0) 10 ≡ [ s≤s (s≤s (s≤s z≤n)) ]
  prop4 = refl

  vec : ∀ {a : Set} → ω a → ωᵢ (Vec a) → ωᵢ (Vec a)
  vec a μ zero    = ⦇ []          ⦈
  vec a μ (suc n) = ⦇ (κ a) ∷ (μ n) ⦈

  prop5 : fixᵢ (vec bools) 2 5 ≡
    (true  ∷ true ∷ []) ∷ (true  ∷ false ∷ []) ∷
    (false ∷ true ∷ []) ∷ (false ∷ false ∷ []) ∷ []
  prop5 = refl

  data Sorted : List ℕ → Set where
    nil    : Sorted []
    single : ∀ {n : ℕ} → Sorted (n ∷ [])
    step   : ∀ {n m : ℕ} {xs : List ℕ} → n ≤ m → Sorted (m ∷ xs) → Sorted (n ∷ m ∷ xs)

  sorted : ωᵢ Sorted → ωᵢ Sorted
  sorted μ []       = ⦇ nil    ⦈
  sorted μ (x ∷ []) = ⦇ single ⦈
  sorted μ (x ∷ y ∷ xs) with fixᵢ ≤m (x , y) 10
  sorted μ (x ∷ y ∷ xs) | [] = uninhabited
  sorted μ (x ∷ y ∷ xs) | p ∷ _ = ⦇ (step p) (μ (y ∷ xs)) ⦈

  prop6 : fixᵢ sorted (1 ∷ 2 ∷ 3 ∷ []) 15 ≡ step (s≤s z≤n) (step (s≤s (s≤s z≤n)) single) ∷ []
  prop6 = refl

  prop7 : fixᵢ sorted (3 ∷ 2 ∷ 1 ∷ []) 15 ≡ []
  prop7 = refl

{-
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
  -}
