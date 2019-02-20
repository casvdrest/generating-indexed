open import src.Gen.Base
open import src.Data using (here; there; _∈_; merge)
open import src.Gen.Regular.Isomorphism
open import src.Gen.Regular.Generic
open import src.Gen.Regular.Properties
open import src.Gen.Properties
open import src.Gen.Equivalence

open import Data.Bool
open import Data.Maybe using (just; nothing; Maybe)
open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Sum

open import Category.Applicative
open import Category.Functor

open import Relation.Binary.PropositionalEquality

module src.Gen.Regular.Examples where

  open RawApplicative ⦃...⦄ using (_⊛_; pure)
  

  ------ Bool -----

  bool : ⟪ 𝔾 Bool ⟫
  bool _ = ⦇ true  ⦈
         ∥ ⦇ false ⦈

  bool-Complete : Complete ⟨ bool ⟩
  bool-Complete {false} = 1 , there here
  bool-Complete {true} = 1 , here
  
  bool' : ∀ {n : ℕ} → 𝔾 Bool n
  bool' = isoGen Bool (U~ ⊕~ U~)

  bool∼bool' : ⟨ bool ⟩ ∼ bool'
  bool∼bool' = Complete→eq {g₁ = ⟨ bool ⟩} {g₂ = bool'} bool-Complete (isoGen-Complete (U~ ⊕~ U~))
  
  ------ Maybe ------

  maybe : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 (Maybe a) ⟫
  maybe a _ = ⦇ nothing    ⦈
            ∥ ⦇ just ⟨ a ⟩ ⦈

  
  maybe' : ∀ {n : ℕ} → (a : Set) → ⟪ 𝔾 a ⟫ →  𝔾 (Maybe a) n
  maybe' a gen = isoGen (Maybe a) (K~ gen ⊕~ U~)

  
  ------ Naturals ------

  nat : ⟪ 𝔾 ℕ ⟫
  nat μ = ⦇ zero  ⦈
        ∥ ⦇ suc μ ⦈

  nat' : ∀ {n : ℕ} → 𝔾 ℕ n
  nat' = isoGen ℕ (U~ ⊕~ I~)

  nat-Complete : Complete ⟨ nat ⟩
  nat-Complete {zero} = 1 , here
  nat-Complete {suc n} with nat-Complete {n}
  nat-Complete {suc n} | n' , snd = suc n' , merge-cong {xs = []} (++-elem-left (map-preserves-elem snd))

  nat∼nat' : ⟨ nat ⟩ ∼ nat'
  nat∼nat' = Complete→eq {g₁ = ⟨ nat ⟩} {g₂ = nat'} nat-Complete (isoGen-Complete (U~ ⊕~ I~))

  ------ Lists ------

  list : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 (List a) ⟫
  list a μ = ⦇ [] ⦈
           ∥ ⦇ ⟨ a ⟩ ∷ μ ⦈

  list' : ∀ {n : ℕ} → (a : Set) → ⟪ 𝔾 a ⟫ → 𝔾 (List a) n
  list' a gen = isoGen (List a) (U~ ⊕~ (K~ gen ⊗~ I~))

  
  ------ Pairs ------

  pair : ∀ {a b} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫
         → ⟪ 𝔾 (a × b) ⟫
  pair a b _ = ⦇ ⟨ a ⟩ , ⟨ b ⟩ ⦈

  pair' : ∀ {n : ℕ} → (a b : Set) → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫ → 𝔾 (a × b) n
  pair' a b gen₁ gen₂ = isoGen (a × b) ((K~ gen₁) ⊗~ (K~ gen₂))


  ------ Either ------

  either : ∀ {a b} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫ → ⟪ 𝔾 (a ⊎ b) ⟫
  either a b _ = ⦇ inj₁ ⟨ a ⟩ ⦈
               ∥ ⦇ inj₂ ⟨ b ⟩ ⦈  

  either' : ∀ {n : ℕ} → (a b : Set) → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫ → 𝔾 (a ⊎ b) n
  either' a b gen₁ gen₂ = isoGen (a ⊎ b) ((K~ gen₁) ⊕~ (K~ gen₂))
  
