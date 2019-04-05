open import Data.Nat hiding (_≤_)
open import Data.Fin using (Fin; suc; zero)
open import Data.List

open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Data.Empty

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Function
import Level as L

open import AgdaGen.Base
open import AgdaGen.Generic.Isomorphism using (_≅_)
open import AgdaGen.Generic.Regular.Universe

module AgdaGen.Generic.Indexed.MultisortedSignatures.Signature where

  ------ Syntax for Π Types ------
  
  Π : (a : Set) → (a → Set) → Set
  Π a f = (x : a) → f x

  infix 3 Π-syntax

  Π-syntax : (a : Set) → (a → Set) → Set
  Π-syntax = Π

  syntax Π-syntax A B = Π[ A ] B

  ------ Signature definition ------

  record Sig {ℓ} (i : Set ℓ) : Set (L.suc ℓ) where
    constructor _◃_∣_
    field
      Op : i → Reg {ℓ}
      Ar : ∀ {x} → Fix (Op x) → Reg {ℓ}
      Ty : ∀ {x} {op : Fix (Op x)} → Fix (Ar op) → i

  ⟦_⟧ₛ : ∀ {i : Set} → Sig i → (x : i → Set) → (i → Set)
  ⟦ Op ◃ Ar ∣ Ty ⟧ₛ x = λ i → Σ[ op ∈ Fix (Op i) ] Π[ Fix (Ar op) ] x ∘ Ty

  data Fixₛ {i : Set} (Σ : Sig i) (x : i) : Set where
    Inₛ : ⟦ Σ ⟧ₛ (Fixₛ Σ) x → Fixₛ Σ x

  Op-vec : ∀ {a : Set} → ℕ → Reg {L.0ℓ} {L.0ℓ}
  Op-vec zero = U
  Op-vec {a} (suc n) = K a

  Ar-vec : ∀ {a : Set} → (n : ℕ) → Fix (Op-vec {a} n) → Reg {L.0ℓ} {L.0ℓ}
  Ar-vec zero x = Z
  Ar-vec (suc n) op = U

  Ty-vec : ∀ {a : Set} → (n : ℕ) → (op : Fix (Op-vec {a} n)) → Fix (Ar-vec n op) → ℕ
  Ty-vec zero (In tt) (In ())
  Ty-vec (suc n) (In x) (In tt) = n
  
  Σ-vec : (a : Set) → Sig ℕ
  Σ-vec a = Op-vec {a} ◃ (λ {n} → Ar-vec n) ∣ λ {n} {a} → Ty-vec n a 


  ------ Lists ------

  Op-list : ∀ {a : Set} → ⊤ → Reg {L.0ℓ} {L.0ℓ}
  Op-list {a} tt = U ⊕ K a
  
  Ar-list : ∀ {a : Set} → ⊤ → Fix (Op-list {a} tt) → Reg {L.0ℓ} {L.0ℓ}
  Ar-list tt (In (inj₁ tt)) = Z
  Ar-list tt (In (inj₂ y))  = U
  
  Ty-list : ∀ {a : Set} → ⊤ → (op : Fix (Op-list {a} tt)) → Fix (Ar-list tt op) → ⊤
  Ty-list tt op ar = tt

  Σ-list : (a : Set) → Sig ⊤
  Σ-list a = Op-list ◃ (λ {tt} → Ar-list {a} tt) ∣ λ {tt} {op} → Ty-list tt op 


  ------ Naturals ------

  Op-nat : ⊤ → Reg {L.0ℓ} {L.0ℓ}
  Op-nat tt = U ⊕ U

  Ar-nat : Fix (Op-nat tt) → Reg {L.0ℓ} {L.0ℓ}
  Ar-nat (In (inj₁ tt)) = Z
  Ar-nat (In (inj₂ tt)) = U

  Ty-nat : (op : Fix (Op-nat tt)) → Fix (Ar-nat op) → ⊤
  Ty-nat (In (inj₁ x)) (In ())
  Ty-nat (In (inj₂ y)) (In tt) = tt
     
  Σ-nat : Sig ⊤
  Σ-nat = Op-nat ◃ Ar-nat ∣ λ {op} {ar} → Ty-nat ar


  ------ Finite Sets ------

  Op-fin : ℕ → Reg {L.0ℓ} {L.0ℓ}
  Op-fin zero = Z
  Op-fin (suc t) = U ⊕ U

  Ar-fin : (n : ℕ) → Fix (Op-fin n) → Reg {L.0ℓ} {L.0ℓ}
  Ar-fin zero (In ())
  Ar-fin (suc n) (In (inj₁ tt)) = Z
  Ar-fin (suc n) (In (inj₂ tt)) = U

  Ty-fin : (n : ℕ) → (op : Fix (Op-fin n)) → Fix (Ar-fin n op) → ℕ
  Ty-fin zero (In ()) 
  Ty-fin (suc n) (In (inj₁ tt)) (In ())
  Ty-fin (suc n) (In (inj₂ tt)) (In tt) = n

  Σ-fin : Sig ℕ
  Σ-fin = Op-fin ◃ (λ {n} → Ar-fin n) ∣ λ {n} {op} → Ty-fin n op


  data _≤ : ℕ × ℕ → Set where
    base : ∀ {n : ℕ} → (0 , n) ≤
    step : ∀ {n m : ℕ} → (n , m) ≤ → (suc n , suc m) ≤ 

  Op-≤ : ℕ × ℕ → Reg {L.0ℓ} {L.0ℓ}
  Op-≤ (zero , snd) = U
  Op-≤ (suc fst , zero) = Z
  Op-≤ (suc fst , suc snd) = U

  
  Ar-≤ : ∀ {idx : ℕ × ℕ} → Fix (Op-≤ idx) → Reg {L.0ℓ} {L.0ℓ}
  Ar-≤ {zero , snd} (In tt) = Z
  Ar-≤ {suc fst , zero} (In ())
  Ar-≤ {suc fst , suc snd} (In tt) = U
  
  Ty-≤ : ∀ {idx : ℕ × ℕ} → (op : Fix (Op-≤ idx)) → Fix (Ar-≤ {idx} op) → ℕ × ℕ
  Ty-≤ {zero , snd} (In tt) (In ())
  Ty-≤ {suc fst , zero} (In ()) 
  Ty-≤ {suc fst , suc snd} (In tt) (In tt) = fst , snd
  
  Σ-≤ : Sig (ℕ × ℕ)
  Σ-≤ = Op-≤ ◃ (λ { {idx} op → Ar-≤ {idx} op }) ∣ λ {idx} {op} → Ty-≤ {idx} op 
  
  data Sorted : List ℕ → Set where
    nil    : Sorted []
    single : ∀ {x : ℕ} → Sorted [ x ]
    step'  : ∀ {x y : ℕ} {xs : List ℕ} → (x , y) ≤ → Sorted (y ∷ xs) → Sorted (x ∷ y ∷ xs)  

  Op-Sorted : List ℕ → Reg {L.0ℓ} {L.0ℓ}
  Op-Sorted [] = U
  Op-Sorted (x ∷ []) = U
  Op-Sorted (x ∷ y ∷ xs) = K ((x , y) ≤)

  Ar-Sorted : ∀ {xs : List ℕ} → Fix (Op-Sorted xs) → Reg {L.0ℓ} {L.0ℓ}
  Ar-Sorted {[]} (In tt) = Z
  Ar-Sorted {x ∷ []} (In tt) = Z
  Ar-Sorted {x ∷ x₁ ∷ xs} op = U

  Ty-Sorted : ∀ {xs : List ℕ} → (op : Fix (Op-Sorted xs)) → Fix (Ar-Sorted {xs} op) → List ℕ
  Ty-Sorted {[]} (In tt) (In ())
  Ty-Sorted {x ∷ []} (In tt) (In ())
  Ty-Sorted {x ∷ y ∷ xs} op (In tt) = y ∷ xs

  Σ-Sorted : Sig (List ℕ)
  Σ-Sorted = Op-Sorted ◃ (λ {xs} → Ar-Sorted {xs}) ∣ λ {xs} {ar} → Ty-Sorted {xs} ar


  data Term : ℕ → Set where
    Abs : ∀ {n : ℕ} → Term (suc n) → Term n
    App : ∀ {n : ℕ} → Term n → Term n → Term n
    Var : ∀ {n : ℕ} → Fin n → Term n

  Op-Term : ℕ → Reg {L.0ℓ} {L.0ℓ}
  Op-Term zero = U ⊕ U
  Op-Term (suc n) = U ⊕ (U ⊕ K (Fin (suc n)))

  Ar-Term : (n : ℕ) → Fix (Op-Term n) → Reg {L.0ℓ} {L.0ℓ}
  Ar-Term zero (In (inj₁ tt)) = U 
  Ar-Term zero (In (inj₂ tt)) = U ⊕ U
  Ar-Term (suc n) (In (inj₁ tt)) = U
  Ar-Term (suc n) (In (inj₂ (inj₁ tt))) = U ⊕ U
  Ar-Term (suc n) (In (inj₂ (inj₂ fin))) = Z

  Ty-Term : (n : ℕ) → (op : Fix (Op-Term n)) → Fix (Ar-Term n op) → ℕ
  Ty-Term zero (In (inj₂ tt)) (In (inj₂ tt)) = zero
  Ty-Term zero (In (inj₂ tt)) (In (inj₁ tt)) = zero
  Ty-Term zero (In (inj₁ tt)) (In tt) = suc zero
  Ty-Term (suc n) (In (inj₁ tt)) (In tt) = suc (suc n)
  Ty-Term (suc n) (In (inj₂ (inj₁ tt))) (In (inj₁ tt)) = suc n
  Ty-Term (suc n) (In (inj₂ (inj₁ tt))) (In (inj₂ tt)) = suc n
  Ty-Term (suc n) (In (inj₂ (inj₂ y))) (In ())

  Σ-Term : Sig ℕ
  Σ-Term = Op-Term ◃ (λ {n} → Ar-Term n) ∣ λ {n} {op} → Ty-Term n op

  ------ Perfect trees ------
  
  data Perfect (a : Set) : ℕ → Set where
    Leaf : Perfect a 0
    Node : ∀ {n : ℕ} → a → Perfect a n → Perfect a n → Perfect a (suc n)

  Op-Perfect : ∀ {a : Set} → ℕ → Reg {L.0ℓ} {L.0ℓ}
  Op-Perfect zero = U
  Op-Perfect {a} (suc n) = K a 

  Ar-Perfect : ∀ {a : Set} → (n : ℕ) → Fix (Op-Perfect {a} n) → Reg {L.0ℓ} {L.0ℓ}
  Ar-Perfect zero (In tt) = Z
  Ar-Perfect (suc n) (In x) = U ⊕ U

  Ty-Perfect : ∀ {a : Set} → (n : ℕ) → (op : Fix (Op-Perfect {a} n)) → Fix (Ar-Perfect n op) → ℕ
  Ty-Perfect zero (In tt) (In ())
  Ty-Perfect (suc n) (In x) (In (inj₁ tt)) = n
  Ty-Perfect (suc n) (In x) (In (inj₂ tt)) = n

  Σ-Perfect : ∀ {a : Set} → Sig ℕ
  Σ-Perfect {a} = Op-Perfect {a} ◃ (λ {n} → Ar-Perfect n) ∣ λ {n} {op} → Ty-Perfect n op

  
