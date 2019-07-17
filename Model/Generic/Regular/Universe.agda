open import Model.Base
open import Model.Combinators

open import Data.Nat hiding (_⊔_)
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.List

open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Sum

open import Function

open import Size
open import Level

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module Model.Generic.Regular.Universe where

  -- The universe of regular types
  data Reg {ℓ} {k} : Set (Level.suc k ⊔ Level.suc ℓ) where
    Z   : Reg
    U   : Reg 
    _⊕_ : Reg {ℓ} {k} → Reg {ℓ} {k} → Reg
    _⊗_ : Reg {ℓ} {k} → Reg {ℓ} {k} → Reg
    I   : Reg
    K   : Set k → Reg

  -- Metadata structure containing extra information about the constant types in
  -- a code of type Reg
  data RegInfo {ℓ} (P : Set ℓ → Set (Level.suc ℓ)) : Reg {ℓ} → Set (Level.suc ℓ) where
    Z~   : RegInfo P Z
    U~   : RegInfo P U
    
    _⊕~_ : ∀ {f₁ f₂ : Reg}
           → RegInfo P f₁ → RegInfo P f₂
           → RegInfo P (f₁ ⊕ f₂)
           
    _⊗~_ : ∀ {f₁ f₂ : Reg}
           → RegInfo P f₁ → RegInfo P f₂
           → RegInfo P (f₁ ⊗ f₂)
           
    I~   : RegInfo P I
    
    K~   : ∀ {a : Set ℓ} → P a → RegInfo P (K a)

  -- Transform the type of data stored in a metadata structure
  map-reginfo :
    ∀ {ℓ} {f : Reg {ℓ}} {P Q : Set ℓ → Set (Level.suc ℓ)}
    → (∀ {a : Set ℓ} → P a → Q a)
    → RegInfo P f → RegInfo Q f
  map-reginfo f U~ = U~
  map-reginfo f (ri ⊕~ ri₁) =
    map-reginfo f ri ⊕~ map-reginfo f ri₁
  map-reginfo f (ri ⊗~ ri₁) =
    map-reginfo f ri ⊗~ map-reginfo f ri₁
  map-reginfo f I~ = I~
  map-reginfo f (K~ x) = K~ (f x)
  map-reginfo f (Z~)   = Z~

  -- Semantics of regular types
  ⟦_⟧ : ∀ {ℓ} → Reg {ℓ} → Set → Set
  ⟦ U           ⟧ r = ⊤
  ⟦ reg₁ ⊕ reg₂ ⟧ r = ⟦ reg₁ ⟧ r ⊎ ⟦ reg₂ ⟧ r
  ⟦ reg₁ ⊗ reg₂ ⟧ r = ⟦ reg₁ ⟧ r × ⟦ reg₂ ⟧ r 
  ⟦ I           ⟧ r = r
  ⟦ K a         ⟧ r = a
  ⟦ Z           ⟧ r = ⊥
  
  data Fix {ℓ} (f : Reg {ℓ}) : Set where
    In : ⟦ f ⟧ (Fix f) → Fix f

  -- Mapping operation for pattern functors
  mapᵣ :
    ∀ {ℓ} {a b : Set}
    → (f : Reg {ℓ}) → (a → b)
    → ⟦ f ⟧ a → ⟦ f ⟧ b
  mapᵣ U f tt = tt
  mapᵣ (pf₁ ⊕ pf₂) f (inj₁ x) =
    inj₁ (mapᵣ pf₁ f x)
  mapᵣ (pf₁ ⊕ pf₂) f (inj₂ y) =
    inj₂ (mapᵣ pf₂ f y)
  mapᵣ (pf₁ ⊗ pf₂) f (fst , snd) =
    mapᵣ pf₁ f fst , mapᵣ pf₂ f snd
  mapᵣ I f i     = f i
  mapᵣ (K x) f i = i
