open import Agda.Builtin.Size
open import Codata.Colist
open import Codata.Thunk hiding (map)
open import Data.Nat
open import Data.Maybe hiding (map; fromMaybe)
open import Data.List hiding (map; fromMaybe)

module src.Data where

  _∘_ : ∀ {a b c : Set} → (b → c) → (a → b) → (a → c)
  (f ∘ g) x = f (g x)

  module Sigma where

    data Σ (a : Set) (P : a → Set) : Set where
      _,_ : (x : a) → P x → Σ a P

  module Product where

    data _⊗_ (a b : Set) : Set where
      _,_ : a → b → a ⊗ b

    fst : ∀ {a b : Set} → a ⊗ b → a
    fst (x , _) = x

    snd : ∀ {a b : Set} → a ⊗ b → b
    snd (_ , y) = y

  module Coproduct where

    data _⊕_ (a b : Set) : Set where
      inl : a → a ⊕ b
      inr : b → a ⊕ b

  open Sigma     public
  open Product   public
  open Coproduct public

  interleave : ∀ {a : Set} {i : Size}
               → Colist a i → Colist a i
               → Colist a i
  interleave [] ys = ys
  interleave xs [] = xs
  interleave (x ∷ xs) (y ∷ ys) =
    x ∷ λ where .force → y ∷ λ where .force → interleave (xs .force) (ys .force)

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

  -- Disjoint union of colists
  _⊎_ : ∀ {a b : Set} {i : Size}
        → Colist a i → Colist b i → Colist (a ⊕ b) i
  xs ⊎ ys = interleave (map inl xs) (map inr ys)

  data ℚ : Set where
    Q : ℕ ⊗ ℕ → ℚ
