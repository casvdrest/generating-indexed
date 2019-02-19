open import src.Gen.Base
open import src.Data
open import src.Gen.Regular.Isomorphism
open import src.Gen.Properties

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

  {-
  bool' : ∀ {n : ℕ} → 𝔾 Bool n
  bool' = isoGen Bool
  -}
  
  ------ Maybe ------

  maybe : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 (Maybe a) ⟫
  maybe a _ = ⦇ nothing    ⦈
            ∥ ⦇ just ⟨ a ⟩ ⦈


  maybe-Complete : ∀ {a : Set} {gen : ⟪ 𝔾 a ⟫} → Complete ⟨ gen ⟩ → Complete ⟨ maybe gen ⟩
  maybe-Complete p {x = just x} with p {x}
  maybe-Complete p {just x} | n , elem = {!!} , there (map-preserves-elem {!elem!})
  maybe-Complete _ {x = nothing} = 1 , here

  {-
  maybe' : ∀ {n : ℕ} → (a : Set) ⦃ _ : Regular a ⦄ → 𝔾 (Maybe a) n
  maybe' a = isoGen (Maybe a)


  ------ Naturals ------

  nat : ⟪ 𝔾 ℕ ⟫
  nat μ = ⦇ zero  ⦈
        ∥ ⦇ suc μ ⦈

  nat' : ∀ {n : ℕ} → 𝔾 ℕ n
  nat' = isoGen ℕ


  ------ Lists ------

  list : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 (List a) ⟫
  list a μ = ⦇ [] ⦈
           ∥ ⦇ ⟨ a ⟩ ∷ μ ⦈

  list' : ∀ {n : ℕ} → (a : Set) ⦃ _ : Regular a ⦄ → 𝔾 (List a) n
  list' a = isoGen (List a)


  ------ Pairs ------

  pair : ∀ {a b} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫
         → ⟪ 𝔾 (a × b) ⟫
  pair a b _ = ⦇ ⟨ a ⟩ , ⟨ b ⟩ ⦈

  pair' : ∀ {n : ℕ} → (a b : Set) ⦃ _ : Regular a ⦄ ⦃ _ : Regular b ⦄ → 𝔾 (a × b) n
  pair' a b = isoGen (a × b)


  ------ Either ------

  either : ∀ {a b} → ⟪ 𝔾 a ⟫ → ⟪ 𝔾 b ⟫
           → ⟪ 𝔾 (a ⊎ b) ⟫
  either a b _ = ⦇ inj₁ ⟨ a ⟩ ⦈
               ∥ ⦇ inj₂ ⟨ b ⟩ ⦈  

  either' : ∀ {n : ℕ} → (a b : Set) ⦃ _ : Regular a ⦄ ⦃ _ : Regular b ⦄ → 𝔾 (a ⊎ b) n
  either' a b = isoGen (a ⊎ b)
  -}
