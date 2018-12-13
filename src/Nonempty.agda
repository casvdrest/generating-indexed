open import Agda.Builtin.Size

open import Codata.Thunk hiding (map)
open import Codata.Colist

open import Data.Nat
open import Data.List hiding (_++_; concat; map; zipWith; [_]; take)

module src.Nonempty where

  module NonemptyList where
  
    data List₊ (a : Set) : Set where
       [_] : a → List₊ a
       _∷_ : a → List₊ a → List₊ a

    toList : ∀ {a : Set} → List₊ a → List a
    toList [ x ] = x ∷ []
    toList (x ∷ xs) = x ∷ toList xs

    toList₊ : ∀ {a : Set} → a → List a → List₊ a
    toList₊ y [] = [ y ]
    toList₊ y (x ∷ xs) = y ∷ toList₊ x xs

  module NonemptyColist where
  
    data Colist₊ {a} (A : Set a) (i : Size) : Set a where
      [_]  : A → Colist₊ A i
      _∷_  : A → Thunk (Colist₊ A) i → Colist₊ A i

    toColist : ∀ {a : Set} {i : Size} → Colist₊ a i → Colist a i
    toColist [ x ] = x ∷ λ where .force → []
    toColist (x ∷ xs) = x ∷ λ where .force → toColist (xs .force)

    toColist₊ : ∀ {a : Set} {i : Size} → a → Colist a i → Colist₊ a i
    toColist₊ y [] = [ y ]
    toColist₊ y (x ∷ xs) = y ∷ λ where .force → toColist₊ x (xs .force)

    head₊ : ∀ {a : Set} {i : Size} → Colist₊ a i → a
    head₊ [ x ] = x
    head₊ (x ∷ _) = x

    tail₊ : ∀ {a : Set} {i : Size} → Colist₊ a (↑ i) → Colist a i
    tail₊ [ x ] = []
    tail₊ (x ∷ xs) = toColist (xs .force)

    map₊ : ∀ {a b : Set} {i : Size} → (a → b) → Colist₊ a i → Colist₊ b i
    map₊ f [ x ] = [ f x ]
    map₊ f (x ∷ xs) = f x ∷ λ where .force → map₊ f (xs .force)

    zipWith₊ : ∀ {a b c : Set} {i : Size} → (a → b → c) → Colist₊ a i → Colist₊ b i → Colist₊ c i
    zipWith₊ f (x ∷ xs) (y ∷ ys) = f x y ∷ λ where .force → zipWith₊ f (xs .force) (ys .force) 
    zipWith₊ f xs ys = [ f (head₊ xs) (head₊ ys) ]

    repeat₊ : ∀ {a : Set} {i : Size} → a → Colist₊ a i
    repeat₊ x = x ∷ λ where .force → repeat₊ x

    prefix₊ : ∀ {a : Set} → ℕ → Colist₊ a ∞ → List a
    prefix₊ zero xs = []
    prefix₊ (suc n) [ x ] = x ∷ []
    prefix₊ (suc n) (x ∷ xs) = x ∷ prefix₊ n (xs .force)

  open NonemptyList public
  open NonemptyColist public
