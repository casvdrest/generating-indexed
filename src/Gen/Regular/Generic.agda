
{-# OPTIONS --type-in-type #-}

open import src.Gen.Base

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.List

open import Category.Monad

open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Sum

open import Function

open import Size

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module src.Gen.Regular.Generic where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  data Reg : Set where
    Z   : Reg
    U   : Reg 
    _⊕_ : Reg → Reg → Reg
    _⊗_ : Reg → Reg → Reg
    I   : Reg
    K   : Set → Reg

  data RegInfo (P : Set → Set) : Reg → Set where
    Z~   : RegInfo P Z
    U~   : RegInfo P U
    
    _⊕~_ : ∀ {f₁ f₂ : Reg}
           → RegInfo P f₁ → RegInfo P f₂
           → RegInfo P (f₁ ⊕ f₂)
           
    _⊗~_ : ∀ {f₁ f₂ : Reg}
           → RegInfo P f₁ → RegInfo P f₂
           → RegInfo P (f₁ ⊗ f₂)
           
    I~   : RegInfo P I
    
    K~   : ∀ {a : Set} → P a → RegInfo P (K a)

  map-reginfo : ∀ {f : Reg} {P Q : Set → Set} → (∀ {a : Set} → P a → Q a) → RegInfo P f → RegInfo Q f
  map-reginfo f U~ = U~
  map-reginfo f (ri ⊕~ ri₁) = map-reginfo f ri ⊕~ map-reginfo f ri₁
  map-reginfo f (ri ⊗~ ri₁) = map-reginfo f ri ⊗~ map-reginfo f ri₁
  map-reginfo f I~ = I~
  map-reginfo f (K~ x) = K~ (f x)
  map-reginfo f (Z~)   = Z~
    
  ⟦_⟧ : Reg → Set → Set
  ⟦ U           ⟧ r = ⊤
  ⟦ reg₁ ⊕ reg₂ ⟧ r = ⟦ reg₁ ⟧ r ⊎ ⟦ reg₂ ⟧ r
  ⟦ reg₁ ⊗ reg₂ ⟧ r = ⟦ reg₁ ⟧ r × ⟦ reg₂ ⟧ r 
  ⟦ I           ⟧ r = r
  ⟦ K a         ⟧ r = a
  ⟦ Z           ⟧ r = ⊥
  
  data Fix (f : Reg) : Set where
    In : ⟦ f ⟧ (Fix f) → Fix f

  mapᵣ : ∀ {a b : Set} → (f : Reg) → (a → b) → ⟦ f ⟧ a → ⟦ f ⟧ b
  mapᵣ U f tt = tt
  mapᵣ (pf₁ ⊕ pf₂) f (inj₁ x) = inj₁ (mapᵣ pf₁ f x)
  mapᵣ (pf₁ ⊕ pf₂) f (inj₂ y) = inj₂ (mapᵣ pf₂ f y)
  mapᵣ (pf₁ ⊗ pf₂) f (fst , snd) = mapᵣ pf₁ f fst , mapᵣ pf₂ f snd
  mapᵣ I f i     = f i
  mapᵣ (K x) f i = i
  
  deriveGen : ∀ {f g : Reg}
              → RegInfo 𝔾 f
              → Gen (⟦ f ⟧ (Fix g)) (⟦ g ⟧ (Fix g))
  deriveGen {U} {g} c = pure tt
  deriveGen {f₁ ⊕ f₂}  {g} (c₁ ⊕~ c₂) =
    ⦇ inj₁ (deriveGen c₁) ⦈ ∥ ⦇ inj₂ (deriveGen c₂) ⦈
  deriveGen {f₁ ⊗ f₂}  {g} (c₁ ⊗~ c₂) =
    ⦇ (deriveGen c₁) , (deriveGen c₂) ⦈
  deriveGen {I} {g} c   = ⦇ In μ ⦈
  deriveGen {K a} {g} (K~ gₖ) = ` gₖ
  deriveGen {Z} Z~ = None
