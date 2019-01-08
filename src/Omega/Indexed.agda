open import Size 

open import Data.Nat 
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_; _+_)
open import Data.Vec hiding (map; [_])
open import Data.Bool
open import Data.List hiding (fromMaybe)
open import Data.Maybe hiding (fromMaybe; map)
open import Data.Empty
open import Data.Product using (uncurry; _,_; ∃; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq'
open Eq' using (_≡_; refl; cong; sym; trans)
open Eq'.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import src.Data
open import src.Omega.Base
open import src.Omega.Examples using (bools)

open import Function

open import Category.Applicative

module src.Omega.Indexed where 

  open RawApplicative ⦃...⦄ using (_⊛_; pure)
  
  fin : ⟪ ωᵢ Fin ⟫
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

  vec : ∀ {a : Set} → ω a → ⟪ ωᵢ (Vec a) ⟫
  vec a μ zero    = ⦇ []          ⦈
  vec a μ (suc n) = ⦇ (κ a) ∷ (μ n) ⦈

  prop5 : fixᵢ (vec bools) 2 5 ≡
    (true  ∷ true ∷ []) ∷ (true  ∷ false ∷ []) ∷
    (false ∷ true ∷ []) ∷ (false ∷ false ∷ []) ∷ []
  prop5 = refl

  data Sorted {ℓ} : List ℕ → Set ℓ where
    nil    : Sorted []
    single : ∀ {n : ℕ} → Sorted (n ∷ [])
    step   : ∀ {n m : ℕ} {xs : List ℕ} → n ≤ m → Sorted {ℓ} (m ∷ xs) → Sorted {ℓ} (n ∷ m ∷ xs)

  n≤m? : (n m : ℕ) → Maybe (n ≤ m)
  n≤m? zero m          = just z≤n
  n≤m? n zero          = nothing
  n≤m? (suc n) (suc m) = Data.Maybe.map s≤s (n≤m? n m)

  sortedₛ : ⟪ ωᵢ Sorted ⟫
  sortedₛ μ []      = ⦇ nil    ⦈
  sortedₛ μ(x ∷ []) = ⦇ single ⦈
  sortedₛ μ (x ∷ y ∷ xs) with n≤m? x y
  sortedₛ μ (x ∷ y ∷ xs) | nothing = uninhabited
  sortedₛ μ (x ∷ y ∷ xs) | just p = ⦇ (step p) (μ (y ∷ xs)) ⦈

  prop6 : fixᵢ sortedₛ (1 ∷ 2 ∷ 3 ∷ []) 15 ≡ step (s≤s z≤n) (step (s≤s (s≤s z≤n)) single) ∷ []
  prop6 = refl

  prop7 : fixᵢ sortedₛ (3 ∷ 2 ∷ 1 ∷ []) 15 ≡ []
  prop7 = refl

  bump : ℕ → List ℕ → List ℕ
  bump n [] = []
  bump n (x ∷ xs) = x + n ∷ bump (x + n) xs

  Sorted' : ∀ {ℓ} → List ℕ → Set ℓ
  Sorted' = Sorted ∘ (bump 0) 

  n≤k+n : (n k : ℕ) → n ≤ k + n
  n≤k+n n zero = ≤-reflexive refl
  n≤k+n n (suc k) = ≤-suc (n≤k+n n k)

  n≤m→n+k≤m+k : ∀ {n m k : ℕ} → n ≤ m → n + k ≤ m + k
  n≤m→n+k≤m+k {n = n} {m = m} {k = zero} p rewrite +-comm n 0 | +-comm m 0 = p
  n≤m→n+k≤m+k {n = n} {m = m} {k = suc k} p rewrite +-suc n k | +-suc m k = s≤s (n≤m→n+k≤m+k p)

  map-preserves-sorted : ∀ {ℓ} {n : ℕ} {xs : List ℕ}
                         → Sorted {ℓ} xs
                         → Sorted {ℓ} (map (λ x → x + n) xs)
  map-preserves-sorted nil = nil
  map-preserves-sorted single = single
  map-preserves-sorted (step x prf) = step (n≤m→n+k≤m+k x) (map-preserves-sorted prf)

  Sorted-eq : ∀ {ℓ} {xs ys : List ℕ} → xs ≡ ys → Sorted {ℓ} xs → Sorted {ℓ} ys
  Sorted-eq refl sp = sp

  bump-map-eq : ∀ {n m : ℕ} {xs : List ℕ} → map (λ x → x + m) (bump n xs) ≡ bump (n + m) xs
  bump-map-eq {xs = []} = refl
  bump-map-eq {n = n} {m = m} {xs = x ∷ xs} rewrite sym (+-assoc x n m) =
    cong (_∷_ (x + n + m)) (bump-map-eq {n = x + n} {m = m} {xs = xs})

  bump-lemma : ∀ {ℓ} {n m : ℕ} {xs : List ℕ}
               → Sorted {ℓ} (bump n xs)
               → Sorted {ℓ} (bump (n + m) xs)
  bump-lemma {n = n} {m = m} {xs = xs} p  =
    Sorted-eq bump-map-eq (map-preserves-sorted {n = m} {xs = bump n xs} p)
  
  sorted : ⟪ ωᵢ Sorted' ⟫
  sorted μ []           = ⦇ nil ⦈
  sorted μ (x ∷ [])     = ⦇ single ⦈
  sorted μ (x ∷ y ∷ xs) rewrite +-comm x 0 =
    ⦇ (step (n≤k+n x y) ∘ bump-lemma {n = 0}) (μ (y ∷ xs)) ⦈

  ≤-diff : ∀ {n m : ℕ} → n ≤ m → ℕ
  ≤-diff {zero} {m} p = m
  ≤-diff {suc n} {zero} ()
  ≤-diff {suc n} {suc m} (s≤s p) = suc (≤-diff p)

  ≤-equivalence : ∀ {n m} → n ≤ m
                  ----------------------------------------
                  → ∃[ k ] ((n ≤ (n + k)) ⊗ (m ≡ (n + k)))
                  
  ≤-equivalence {zero} {m} p = m , p , refl
  ≤-equivalence {suc n} {m = suc m} (s≤s p) with ≤-equivalence p
  ≤-equivalence {suc n} {suc .(n + k)} (s≤s p) | k , (leq , refl) =
    k , s≤s leq , refl

  bump-eq-lemma : ∀ {x y v : ℕ} {xs ys : List ℕ}
                  → y ∷ xs ≡ bump x (v ∷ ys)
                  → x ∷ y ∷ xs ≡ bump 0 (x ∷ v ∷ ys)
  bump-eq-lemma {x} refl rewrite +-comm x 0 = refl

  minus-0 : ∀ {n : ℕ} → ∣ n - 0 ∣ ≡ n
  minus-0 {zero} = refl
  minus-0 {suc n} = refl

  lemma-minus : ∀ {n m : ℕ} → n ≤ m → ∣ m - n ∣ + n ≡ m
  lemma-minus {.0} {m} z≤n rewrite +-comm ∣ m - 0 ∣ 0 | minus-0 {n = m} = refl
  lemma-minus {(suc n)} {(suc m)} (s≤s p) with lemma-minus p
  ... | res rewrite +-suc ∣ m - n ∣ n = cong suc res

  lemma-sorted-≤ : ∀ {ℓ} {n m : ℕ} {xs : List ℕ} → n ≤ m → Sorted {ℓ} (m ∷ xs) → Sorted {ℓ} (n ∷ xs)
  lemma-sorted-≤ leq single = single
  lemma-sorted-≤ {n = n} {m = m} leq (step x p) = step (≤-trans leq x) p

  dfst : ∀ {ℓ} {a : Set ℓ} {P : a → Set ℓ} → Σ a P → a
  dfst (x , _) = x
  
  {-
  sorted-equivalence : ∀ {ℓ} {xs : List ℕ} → Sorted {ℓ} xs
                       -----------------------------------------
                       → ∃[ ys ] (Sorted' ys ⊗ (xs ≡ bump 0 ys))
  sorted-equivalence {xs = []} nil = [] , nil , refl
  sorted-equivalence {xs = x ∷ []} single rewrite +-comm 0 x = [ x ] , single , refl
  sorted-equivalence {xs = x ∷ y ∷ xs} (step leq p) = {!!}
  -}
  
