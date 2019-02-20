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
open import src.Gen.Regular.Isomorphism using (_≅_)

module src.Gen.Indexed.Signature where

  ------ Syntax for Π Types ------
  
  Π : (a : Set) → (a → Set) → Set
  Π a f = (x : a) → f x

  infix 3 Π-syntax

  Π-syntax : (a : Set) → (a → Set) → Set
  Π-syntax = Π

  syntax Π-syntax A B = Π[ A ] B


  data 𝕌 : Set where
    𝟘   : 𝕌
    𝟙   : 𝕌
    _⊞_ : 𝕌 → 𝕌 → 𝕌
    _⊠_ : 𝕌 → 𝕌 → 𝕌

  ⟦_⟧ᵤ : 𝕌 → Set
  ⟦ 𝟘 ⟧ᵤ       = ⊥
  ⟦ 𝟙 ⟧ᵤ       = ⊤
  ⟦ U₁ ⊞ U₂ ⟧ᵤ = ⟦ U₁ ⟧ᵤ ⊎ ⟦ U₂ ⟧ᵤ
  ⟦ U₁ ⊠ U₂ ⟧ᵤ = ⟦ U₁ ⟧ᵤ × ⟦ U₂ ⟧ᵤ

  ------ Signature definition ------

  record Sig {ℓ} (i : Set ℓ) : Set (L.suc ℓ) where
    constructor _◃_∣_
    field
      Op : i → 𝕌
      Ar : ∀ {x} → ⟦ Op x ⟧ᵤ → 𝕌
      Ty : ∀ {x} {op : ⟦ Op x ⟧ᵤ} → ⟦ Ar op ⟧ᵤ → i

  ⟦_⟧ : ∀ {i : Set} → Sig i → (x : i → Set) → (i → Set)
  ⟦ Op ◃ Ar ∣ Ty ⟧ x = λ i → Σ[ op ∈ ⟦ Op i ⟧ᵤ ] Π[ ⟦ Ar op ⟧ᵤ ] x ∘ Ty

  data μ {i : Set} (Σ : Sig i) (x : i) : Set where
    `μ : ⟦ Σ ⟧ (μ Σ) x → μ Σ x

 {-
  ------ Vec ------

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


  ------ Lists ------

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

-}
  ------ Naturals ------

  Op-nat : ⊤ → 𝕌
  Op-nat tt = 𝟙 ⊞ 𝟙

  Ar-nat : ⟦ Op-nat tt ⟧ᵤ → 𝕌
  Ar-nat (inj₁ tt) = 𝟘
  Ar-nat (inj₂ tt) = 𝟙

  Ty-nat : (op : ⟦ Op-nat tt ⟧ᵤ) → ⟦ Ar-nat op ⟧ᵤ → ⊤
  Ty-nat (inj₁ x) ()
  Ty-nat (inj₂ y) tt = tt
     
  Σ-nat : Sig ⊤
  Σ-nat = Op-nat ◃ Ar-nat ∣ λ {op} {ar} → Ty-nat ar

  ------ Finite Sets ------

  Op-fin : ℕ → 𝕌
  Op-fin zero = 𝟘
  Op-fin (suc t) = 𝟙 ⊞ 𝟙

  Ar-fin : (n : ℕ) → ⟦ Op-fin n ⟧ᵤ → 𝕌
  Ar-fin zero ()
  Ar-fin (suc n) (inj₁ tt) = 𝟘
  Ar-fin (suc n) (inj₂ tt) = 𝟙

  Ty-fin : (n : ℕ) → (op : ⟦ Op-fin n ⟧ᵤ) → ⟦ Ar-fin n op ⟧ᵤ → ℕ
  Ty-fin zero () 
  Ty-fin (suc n) (inj₁ tt) ()
  Ty-fin (suc n) (inj₂ tt) tt = n

  Σ-fin : Sig ℕ
  Σ-fin = Op-fin ◃ (λ {n} → Ar-fin n) ∣ λ {n} {op} → Ty-fin n op

{-
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
-}
