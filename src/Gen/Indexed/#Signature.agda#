{-# OPTIONS --type-in-type #-}

import Level as L
open import Data.Nat hiding (_≤_)
open import Data.Fin using (Fin; suc; zero)
open import Data.List

open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Data.Empty

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Function

open import src.Gen.Base

module src.Gen.Indexed.Signature where

  Π : (a : Set) → (a → Set) → Set
  Π a f = (x : a) → f x

  infix 3 Π-syntax

  Π-syntax : (a : Set) → (a → Set) → Set
  Π-syntax = Π

  syntax Π-syntax A B = Π[ A ] B

  record Sig {ℓ} (i : Set ℓ) : Set (L.suc ℓ) where
    constructor _◃_∣_
    field
      Op : i → Set
      Ar : ∀ {x} → Op x → Set
      Ty : ∀ {x} {op : Op x} → Ar op → i

  data Vec {ℓ} (a : Set ℓ) : ℕ → Set ℓ where
    []  : Vec a 0
    _∷_ : ∀ {n : ℕ} → a → Vec a n → Vec a (suc n)

  Op-vec : ∀ {a : Set} → ℕ → Set
  Op-vec zero = ⊤
  Op-vec {a} (suc n) = a

  Ar-vec : ∀ {a : Set} → (n : ℕ) → Op-vec {a} n → Set
  Ar-vec zero tt = ⊥
  Ar-vec (suc n) op = ⊤

  Ty-vec : ∀ {a : Set} → (n : ℕ) → (op : Op-vec {a} n) → Ar-vec n op → ℕ
  Ty-vec zero a ()
  Ty-vec (suc n) a tt = n

  Σ-vec : (a : Set) → Sig ℕ
  Σ-vec a = Op-vec {a} ◃ (λ {n} → Ar-vec n) ∣ λ {n} {a} → Ty-vec n a

  Op-list : ∀ {a : Set} → ⊤ → Set
  Op-list {a} tt = ⊤ ⊎ a

  Ar-list : ∀ {a : Set} → ⊤ → Op-list {a} tt → Set
  Ar-list tt (inj₁ tt) = ⊥
  Ar-list tt (inj₂ y) = ⊤

  Ty-list : ∀ {a : Set} → ⊤ → (op : Op-list {a} tt) → Ar-list tt op → ⊤
  Ty-list tt (inj₁ tt) ()
  Ty-list tt (inj₂ y) tt = tt

  Σ-list : (a : Set) → Sig ⊤
  Σ-list a = Op-list ◃ (λ {tt} → Ar-list {a} tt) ∣ λ {tt} {op} → Ty-list tt op

  ⟦_⟧ : ∀ {i : Set} → Sig i → (x : i → Set) → (i → Set)
  ⟦ Op ◃ Ar ∣ Ty ⟧ x = λ i → Σ[ op ∈ Op i ] Π[ Ar op ] x ∘ Ty

  data μ {i : Set} (Σ : Sig i) (x : i) : Set where
    `μ : ⟦ Σ ⟧ (μ Σ) x → μ Σ x

  Op-nat : ⊤ → Set
  Op-nat tt = ⊤ ⊎ ⊤

  Ar-nat : Op-nat tt → Set
  Ar-nat (inj₁ x) = ⊥
  Ar-nat (inj₂ y) = ⊤

  Ty-nat : (op : Op-nat tt) → Ar-nat op → ⊤
  Ty-nat (inj₁ x) ()
  Ty-nat (inj₂ y) tt = tt
     
  Σ-nat : Sig ⊤
  Σ-nat = Op-nat ◃ Ar-nat ∣ λ {op} {ar} → Ty-nat ar

  ℕF : Set
  ℕF = μ Σ-nat tt

  fromℕ : ℕ → ℕF
  fromℕ zero = `μ (inj₁ tt , λ())
  fromℕ (suc n) = `μ ((inj₂ tt) , (λ { tt → fromℕ n }))

  toℕ : ℕF → ℕ
  toℕ (`μ (inj₁ tt , _)) = zero
  toℕ (`μ (inj₂ tt , snd)) = suc (toℕ (snd tt))

  ℕ-iso₁ : ∀ {n : ℕ} → toℕ (fromℕ n) ≡ n
  ℕ-iso₁ {zero} = refl
  ℕ-iso₁ {suc n} = cong suc ℕ-iso₁

  Op-fin : ℕ → Set
  Op-fin zero = ⊥
  Op-fin (suc t) = ⊤ ⊎ ⊤

  Ar-fin : (n : ℕ) → Op-fin n → Set
  Ar-fin zero ()
  Ar-fin (suc n) (inj₁ tt) = ⊥
  Ar-fin (suc n) (inj₂ tt) = ⊤

  Ty-fin : (n : ℕ) → (op : Op-fin n) → Ar-fin n op → ℕ
  Ty-fin zero () ar
  Ty-fin (suc n) (inj₁ x) ()
  Ty-fin (suc n) (inj₂ tt) tt = n

  Σ-fin : Sig ℕ
  Σ-fin = Op-fin ◃ (λ {n} → Ar-fin n) ∣ λ {n} {op} → Ty-fin n op

  FinF : ℕ → Set
  FinF n = μ Σ-fin n

  fromFin : ∀ {n : ℕ} → Fin n → FinF n
  fromFin zero = `μ (inj₁ tt , λ())
  fromFin (suc f) = `μ (inj₂ tt , λ {tt → fromFin f})

  toFin : ∀ {n : ℕ} → FinF n → Fin n
  toFin {zero} (`μ (() , snd))
  toFin {suc n} (`μ (inj₁ tt , snd)) = zero
  toFin {suc n} (`μ (inj₂ tt , snd)) = suc (toFin (snd tt))

  Fin-iso₁ : ∀ {n : ℕ} {f : Fin n} → toFin (fromFin f) ≡ f
  Fin-iso₁ {zero} {()}
  Fin-iso₁ {suc n} {zero} = refl
  Fin-iso₁ {suc n} {suc f} = cong suc Fin-iso₁

  ListF : Set → Set
  ListF a = μ (Σ-list a) tt

  fromList : ∀ {a : Set} → List a → ListF a
  fromList [] = `μ (inj₁ tt , λ ())
  fromList (x ∷ xs) = `μ (inj₂ x , λ {tt → fromList xs})

  toList : ∀ {a : Set} → ListF a → List a
  toList (`μ (inj₁ tt , snd)) = []
  toList (`μ (inj₂ y , snd)) = y ∷ toList (snd tt)

  List-iso₁ : ∀ {a : Set} {xs : List a}  → toList (fromList xs) ≡ xs
  List-iso₁ {xs = []} = refl
  List-iso₁ {xs = x ∷ xs} = cong (_∷_ x) List-iso₁

  data _≤ : ℕ × ℕ → Set where
    base : ∀ {n : ℕ} → (0 , n) ≤
    step : ∀ {n m : ℕ} → (n , m) ≤ → (suc n , suc m) ≤ 

  Op-≤ : ℕ × ℕ → Set
  Op-≤ (zero , snd) = ⊤
  Op-≤ (suc fst , zero) = ⊥
  Op-≤ (suc fst , suc snd) = ⊤

  Ar-≤ : ∀ {idx : ℕ × ℕ} → Op-≤ idx → Set
  Ar-≤ {zero , snd} tt = ⊥
  Ar-≤ {suc fst , zero} ()
  Ar-≤ {suc fst , suc snd} tt = ⊤

  Ty-≤ : ∀ {idx : ℕ × ℕ} → (op : Op-≤ idx) → Ar-≤ op → ℕ × ℕ
  Ty-≤ {zero , snd} tt ()
  Ty-≤ {suc fst , zero} () ar
  Ty-≤ {suc fst , suc snd} tt tt = fst , snd

  Σ-≤ : Sig (ℕ × ℕ)
  Σ-≤ = Op-≤ ◃ (λ { idx → Ar-≤ idx }) ∣ λ {_} {op} → Ty-≤ op 

  ≤F : ℕ × ℕ → Set
  ≤F idx = μ Σ-≤ idx

  from≤ : ∀ {idx : ℕ × ℕ} → idx ≤ → ≤F idx
  from≤ base = `μ (tt , λ())
  from≤ (step p) = `μ (tt , λ { tt → from≤ p })

  to≤ : ∀ {idx : ℕ × ℕ} → ≤F idx → idx ≤
  to≤ {zero , snd₁} (`μ (tt , snd)) = base
  to≤ {suc fst₁ , zero} (`μ (() , snd))
  to≤ {suc fst₁ , suc snd₁} (`μ (tt , snd)) = step (to≤ (snd tt))
 
  ≤-iso₁ : ∀ {idx : ℕ × ℕ} {p : idx ≤} → to≤ (from≤ p) ≡ p
  ≤-iso₁ {p = base} = refl
  ≤-iso₁ {p = step p} = cong step ≤-iso₁

  data Sorted : List ℕ → Set where
    nil    : Sorted []
    single : ∀ {x : ℕ} → Sorted [ x ]
    step'  : ∀ {x y : ℕ} {xs : List ℕ} → (x , y) ≤ → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)  

  Op-Sorted : List ℕ → Set
  Op-Sorted [] = ⊤
  Op-Sorted (x ∷ []) = ⊤
  Op-Sorted (x ∷ y ∷ xs) = (x , y) ≤

  Ar-Sorted : ∀ {xs : List ℕ} → Op-Sorted xs → Set
  Ar-Sorted {[]} tt = ⊥
  Ar-Sorted {x ∷ []} tt = ⊥
  Ar-Sorted {x ∷ x₁ ∷ xs} op = ⊤

  Ty-Sorted : ∀ {xs : List ℕ} → (op : Op-Sorted xs) → Ar-Sorted op → List ℕ
  Ty-Sorted {[]} tt ()
  Ty-Sorted {x ∷ []} tt ()
  Ty-Sorted {x ∷ y ∷ xs} op tt = y ∷ xs

  Σ-Sorted : Sig (List ℕ)
  Σ-Sorted = Op-Sorted ◃ Ar-Sorted ∣ λ {_} {ar} → Ty-Sorted ar

  SortedF : List ℕ → Set
  SortedF xs = μ Σ-Sorted xs

  fromSorted : ∀ {xs : List ℕ} → Sorted xs → SortedF xs
  fromSorted nil = `μ (tt , λ())
  fromSorted single = `μ (tt , λ())
  fromSorted (step' x₁ p) = `μ (x₁ , λ { tt → fromSorted p } )

  toSorted : ∀ {xs : List ℕ} → SortedF xs → Sorted xs
  toSorted {[]} (`μ (tt , snd)) = nil
  toSorted {x ∷ []} (`μ (tt , snd)) = single
  toSorted {x ∷ x₁ ∷ xs} (`μ (fst , snd)) = step' fst (toSorted (snd tt))

  Sorted-iso₁ : ∀ {xs : List ℕ} {p : Sorted xs} → toSorted (fromSorted p) ≡ p
  Sorted-iso₁ {[]} {nil} = refl
  Sorted-iso₁ {x ∷ []} {single} = refl
  Sorted-iso₁ {x ∷ x₁ ∷ xs} {step' x₂ p} = cong (step' x₂) Sorted-iso₁ 
