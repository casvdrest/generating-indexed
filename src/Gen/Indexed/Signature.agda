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
    𝕂   : Set → 𝕌

  ⟦_⟧ᵤ : 𝕌 → Set
  ⟦ 𝟘 ⟧ᵤ       = ⊥
  ⟦ 𝟙 ⟧ᵤ       = ⊤
  ⟦ U₁ ⊞ U₂ ⟧ᵤ = ⟦ U₁ ⟧ᵤ ⊎ ⟦ U₂ ⟧ᵤ
  ⟦ U₁ ⊠ U₂ ⟧ᵤ = ⟦ U₁ ⟧ᵤ × ⟦ U₂ ⟧ᵤ
  ⟦ 𝕂 a ⟧ᵤ     = a

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

 
  ------ Vec ------

  Op-vec : ∀ {a : Set} → ℕ → 𝕌
  Op-vec zero = 𝟙
  Op-vec {a} (suc n) = 𝕂 a

  Ar-vec : ∀ {a : Set} → (n : ℕ) → ⟦ Op-vec {a} n ⟧ᵤ → 𝕌
  Ar-vec zero tt = 𝟘
  Ar-vec (suc n) op = 𝟙

  Ty-vec : ∀ {a : Set} → (n : ℕ) → (op : ⟦ Op-vec {a} n ⟧ᵤ) → ⟦ Ar-vec n op ⟧ᵤ → ℕ
  Ty-vec zero tt ()
  Ty-vec (suc n) op tt = n
  
  Σ-vec : (a : Set) → Sig ℕ
  Σ-vec a = Op-vec {a} ◃ (λ {n} → Ar-vec n) ∣ λ {n} {a} → Ty-vec n a 


  ------ Lists ------

  Op-list : ∀ {a : Set} → ⊤ → 𝕌
  Op-list {a} tt = 𝟙 ⊞ 𝕂 a
  
  Ar-list : ∀ {a : Set} → ⊤ → ⟦ Op-list {a} tt ⟧ᵤ → 𝕌
  Ar-list tt (inj₁ tt) = 𝟘
  Ar-list tt (inj₂ y) = 𝟙
  
  Ty-list : ∀ {a : Set} → ⊤ → (op : ⟦ Op-list {a} tt ⟧ᵤ) → ⟦ Ar-list tt op ⟧ᵤ → ⊤
  Ty-list tt (inj₁ tt) ()
  Ty-list tt (inj₂ y) tt = tt

  Σ-list : (a : Set) → Sig ⊤
  Σ-list a = Op-list ◃ (λ {tt} → Ar-list {a} tt) ∣ λ {tt} {op} → Ty-list tt op 


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


  data _≤ : ℕ × ℕ → Set where
    base : ∀ {n : ℕ} → (0 , n) ≤
    step : ∀ {n m : ℕ} → (n , m) ≤ → (suc n , suc m) ≤ 

  Op-≤ : ℕ × ℕ → 𝕌
  Op-≤ (zero , snd) = 𝟙
  Op-≤ (suc fst , zero) = 𝟘
  Op-≤ (suc fst , suc snd) = 𝟙

  
  Ar-≤ : ∀ {idx : ℕ × ℕ} → ⟦ Op-≤ idx ⟧ᵤ → 𝕌
  Ar-≤ {zero , snd} tt = 𝟘
  Ar-≤ {suc fst , zero} ()
  Ar-≤ {suc fst , suc snd} tt = 𝟙
  
  Ty-≤ : ∀ {idx : ℕ × ℕ} → (op : ⟦ Op-≤ idx ⟧ᵤ) → ⟦ Ar-≤ {idx} op ⟧ᵤ → ℕ × ℕ
  Ty-≤ {zero , snd} tt ()
  Ty-≤ {suc fst , zero} () ar
  Ty-≤ {suc fst , suc snd} tt tt = fst , snd
  
  Σ-≤ : Sig (ℕ × ℕ)
  Σ-≤ = Op-≤ ◃ (λ { {idx} op → Ar-≤ {idx} op }) ∣ λ {idx} {op} → Ty-≤ {idx} op 
  

  data Sorted : List ℕ → Set where
    nil    : Sorted []
    single : ∀ {x : ℕ} → Sorted [ x ]
    step'  : ∀ {x y : ℕ} {xs : List ℕ} → (x , y) ≤ → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)  

  Op-Sorted : List ℕ → 𝕌
  Op-Sorted [] = 𝟙
  Op-Sorted (x ∷ []) = 𝟙
  Op-Sorted (x ∷ y ∷ xs) = 𝕂 ((x , y) ≤)


  Ar-Sorted : ∀ {xs : List ℕ} → ⟦ Op-Sorted xs ⟧ᵤ → 𝕌
  Ar-Sorted {[]} tt = 𝟘
  Ar-Sorted {x ∷ []} tt = 𝟘
  Ar-Sorted {x ∷ x₁ ∷ xs} op = 𝟙

  Ty-Sorted : ∀ {xs : List ℕ} → (op : ⟦ Op-Sorted xs ⟧ᵤ) → ⟦ Ar-Sorted {xs} op ⟧ᵤ → List ℕ
  Ty-Sorted {[]} tt ()
  Ty-Sorted {x ∷ []} tt ()
  Ty-Sorted {x ∷ y ∷ xs} op tt = y ∷ xs

  Σ-Sorted : Sig (List ℕ)
  Σ-Sorted = Op-Sorted ◃ (λ {xs} → Ar-Sorted {xs}) ∣ λ {xs} {ar} → Ty-Sorted {xs} ar

  data Term : ℕ → Set where
    Abs : ∀ {n : ℕ} → Term (suc n) → Term n
    App : ∀ {n : ℕ} → Term n → Term n → Term n
    Var : ∀ {n : ℕ} → Fin n → Term n

  Op-Term : ℕ → 𝕌
  Op-Term zero = 𝟙 ⊞ 𝟙
  Op-Term (suc n) = 𝟙 ⊞ (𝟙 ⊞ 𝕂 (Fin (suc n)))

  Ar-Term : (n : ℕ) → ⟦ Op-Term n ⟧ᵤ → 𝕌
  Ar-Term zero (inj₁ tt) = 𝟙 
  Ar-Term zero (inj₂ tt) = 𝟙 ⊞ 𝟙
  Ar-Term (suc n) (inj₁ tt) = 𝟙
  Ar-Term (suc n) (inj₂ (inj₁ tt)) = 𝟙 ⊞ 𝟙
  Ar-Term (suc n) (inj₂ (inj₂ fin)) = 𝟘

  Ty-Term : (n : ℕ) → (op : ⟦ Op-Term n ⟧ᵤ) → ⟦ Ar-Term n op ⟧ᵤ → ℕ
  Ty-Term zero (inj₂ tt) (inj₂ tt) = zero
  Ty-Term zero (inj₂ tt) (inj₁ tt) = zero
  Ty-Term zero (inj₁ tt) tt = suc zero
  Ty-Term (suc n) (inj₁ tt) tt = suc (suc n)
  Ty-Term (suc n) (inj₂ (inj₁ tt)) (inj₁ tt) = suc n
  Ty-Term (suc n) (inj₂ (inj₁ tt)) (inj₂ tt) = suc n
  Ty-Term (suc n) (inj₂ (inj₂ y)) ()

  Σ-Term : Sig ℕ
  Σ-Term = Op-Term ◃ (λ {n} → Ar-Term n) ∣ λ {n} {op} → Ty-Term n op
