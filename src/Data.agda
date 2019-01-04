open import Level

open import Agda.Builtin.Size
open import Codata.Colist
open import Codata.Thunk hiding (map)
open import Data.Nat hiding (_⊔_)
open import Data.Maybe hiding (map; fromMaybe)
open import Data.List hiding (map; fromMaybe)

module src.Data where

  module Sigma where

    data Σ {ℓ₁ ℓ₂} (a : Set ℓ₁) (P : a → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
      _,_ : (x : a) → P x → Σ a P

  module Pi where

    Π : (a :  Set) → (a → Set) → Set
    Π a P = (x : a) → P x


  module Product where

    data _⊗_ {ℓ} (a b : Set ℓ) : Set ℓ where
      _,_ : a → b → a ⊗ b

    fst : ∀ {ℓ} {a b : Set ℓ} → a ⊗ b → a
    fst (x , _) = x

    snd : ∀ {ℓ} {a b : Set ℓ} → a ⊗ b → b
    snd (_ , y) = y

  module Coproduct where

    data _⊕_ {ℓ} (a b : Set ℓ) : Set ℓ where
      inl : a → a ⊕ b
      inr : b → a ⊕ b

  open Sigma     public
  open Pi        public
  open Product   public
  open Coproduct public

  interleave : ∀ {ℓ} {a : Set ℓ} {i : Size}
               → Colist a i → Thunk (Colist a) (↑ i)
               → Colist a i
  interleave [] ys = ys .force
  interleave (x ∷ xs) ys = x ∷ λ where .force → interleave (ys .force) xs

  wrap : ∀ {a : Set} → a → List a → List a
  wrap x [] = x ∷ []
  wrap x (y ∷ xs) = y ∷ wrap x xs

  interleaveN : ∀ {a : Set} {i : Size} → List (Colist a i) → Colist a i
  interleaveN [] = []
  interleaveN ([] ∷ xs) = interleaveN xs
  interleaveN ((y ∷ ys) ∷ xs) =
    y ∷ λ where .force → interleaveN (wrap (ys .force) xs)

  merge : ∀ {ℓ} {a : Set ℓ} → List a → List a → List a
  merge [] ys = ys
  merge (x ∷ xs) ys = x ∷ merge ys xs

  iterate : ∀ {a : Set} {i : Size} → a → (a → a) → Colist a i
  iterate x f = x ∷ λ where .force → iterate (f x) f

  repeat : ∀ {a : Set} {i : Size} → a → Colist a i
  repeat x = x ∷ λ where .force → repeat x

  fromMaybe : ∀ {a : Set} {i : Size} → Maybe a → Colist a i
  fromMaybe (just x) = x ∷ λ where .force → []
  fromMaybe nothing = []

  prefix : ∀ {a : Set} → ℕ → Colist a ∞ → List a
  prefix zero    xs       = []
  prefix _       []       = []
  prefix (suc n) (x ∷ xs) = x ∷ prefix n (xs .force)


  data _∈_ {ℓ} {a : Set ℓ} : a → List a → Set ℓ where
    here : ∀ {x : a} {xs : List a} → x ∈ (x ∷ xs)
    there : ∀ {x y : a} {xs : List a} → x ∈ xs → x ∈ (y ∷ xs)

  -- Disjoint union of colists
  _⊎_ : ∀ {ℓ} {a b : Set ℓ} {i : Size}
        → Colist a i → Colist b i → Colist (a ⊕ b) i
  xs ⊎ ys = interleave (map inl xs) (λ where .force → map inr ys)

  data ℚ : Set where
    Q : ℕ ⊗ ℕ → ℚ
