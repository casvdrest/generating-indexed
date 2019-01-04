open import Agda.Builtin.Size

open import Codata.Thunk hiding (map)
open import Codata.Colist

open import Data.Nat
open import Data.Bool
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List hiding (_++_; concat; map; zipWith; [_]; take)

open import src.Data

module src.Nonempty where

  module NonemptyList where
  
    data List₊ {ℓ} (a : Set ℓ) : Set ℓ where
       [_] : a → List₊ a
       _∷_ : a → List₊ a → List₊ a

    toList : ∀ {a : Set} → List₊ a → List a
    toList [ x ] = x ∷ []
    toList (x ∷ xs) = x ∷ toList xs

    toList₊ : ∀ {a : Set} → a → List a → List₊ a
    toList₊ y [] = [ y ]
    toList₊ y (x ∷ xs) = y ∷ toList₊ x xs

    wrap₊ : ∀ {a : Set} → a → List₊ a → List₊ a
    wrap₊ x [ y ] = y ∷ [ x ]
    wrap₊ x (y ∷ xs) = y ∷ wrap₊ x xs

    mapl₊ : ∀ {a b : Set} → (a → b) → List₊ a → List₊ b
    mapl₊ f [ x ] = [ f x ]
    mapl₊ f (x ∷ xs) = f x ∷ mapl₊ f xs

    merge₊ : ∀ {a : Set} → List₊ a → List₊ a → List₊ a
    merge₊ [ x ] ys = x ∷ ys
    merge₊ (x ∷ xs) ys = x ∷ merge₊ ys xs

  open NonemptyList public

  module NonemptyColist where
  
    data Colist₊ {ℓ} (a : Set ℓ) (i : Size) : Set ℓ where
      [_] : a → Colist₊ a i 
      _∷_ : a → Thunk (Colist₊ a) i → Colist₊ a i

    toColist : ∀ {ℓ} {a : Set ℓ} {i : Size} → Colist₊ a i → Colist a i
    toColist [ x ] = x ∷ λ where .force → []
    toColist (x ∷ xs) = x ∷ λ where .force → toColist (xs .force)

    tail₊ : ∀ {ℓ} {a : Set ℓ} {i : Size} → Colist₊ a (↑ i) → Colist a i
    tail₊ [ x ] = []
    tail₊ (x ∷ xs) = toColist (xs .force)

    head₊ : ∀ {ℓ} {a : Set ℓ} {i : Size} → Colist₊ a i → a
    head₊ [ x ] = x
    head₊ (x ∷ _) = x

    toColist₊ : ∀ {ℓ} {a : Set ℓ} {i : Size} → a → Colist a i → Colist₊ a i
    toColist₊ x [] = [ x ]
    toColist₊ x (y ∷ xs) = x ∷ λ where .force → toColist₊ y (xs .force)

    map₊ : ∀ {ℓ} {a b : Set ℓ} {i : Size} → (a → b) → Colist₊ a i → Colist₊ b i
    map₊ f [ x ] = [ f x ]
    map₊ f (x ∷ xs) = f x ∷ λ where .force → map₊ f (xs .force)

    zipWith₊ : ∀ {a b c : Set} {i : Size} → (a → b → c) → Colist₊ a i → Colist₊ b i → Colist₊ c i
    zipWith₊ f (x ∷ xs) (y ∷ ys) = f x y ∷ λ where .force → zipWith₊ f (xs .force) (ys .force) 
    zipWith₊ f xs ys = [ f (head₊ xs) (head₊ ys) ] 

    repeat₊ : ∀ {a : Set} {i : Size} → a → Colist₊ a i
    repeat₊ x = x ∷ λ where .force → repeat₊ x

    concat : ∀ {ℓ} {a : Set ℓ} {i : Size} → Colist (List₊ a) i → Colist a i
    concat [] = []
    concat ([ x ] ∷ xs) = x ∷ λ where .force → concat (xs .force)
    concat ((x ∷ ys) ∷ xs) = x ∷ λ where .force → concat (ys ∷ xs)

    concat₊ : ∀ {ℓ} {a : Set ℓ} {j : Size< ∞} → Colist₊ (List₊ a) j → Colist₊ a j
    concat₊ [ [ x ] ] = [ x ]
    concat₊ [ x ∷ xs ] = x ∷ λ where .force → concat₊ [ xs ]
    concat₊ ([ x ] ∷ xs) = x ∷ λ where .force → concat₊ (xs .force)
    concat₊ ((x ∷ ys) ∷ xs) = x ∷ λ where .force → concat₊ (ys ∷ xs)

    iterate₊ : ∀ {a : Set} {i : Size} → a → (a → a) → Colist₊ a i
    iterate₊ x f = x ∷ λ where .force → iterate₊ (f x) f 

    prefix₊ : ∀ {a : Set} → ℕ → Colist₊ a ∞ → List a
    prefix₊ zero xs = []
    prefix₊ (suc n) [ x ] = x ∷ []
    prefix₊ (suc n) (x ∷ xs) = x ∷ prefix₊ n (xs .force)

    interleave₊ : ∀ {ℓ} {a : Set ℓ} {i : Size} → Colist₊ a i → Thunk (Colist₊ a) i → Colist₊ a i
    interleave₊ [ x ] ys = x ∷ ys
    interleave₊ (x ∷ xs) ys = x ∷ λ where .force → interleave₊ (ys .force) xs
    
    interleaveN₊ : ∀ {a : Set} {i : Size} → NonemptyList.List₊ (Colist₊ a i) → Colist₊ a i
    interleaveN₊ [ x ] = x
    interleaveN₊ ([ x ] ∷ xs) = x ∷ λ where .force → interleaveN₊ xs 
    interleaveN₊ ((x ∷ y) ∷ xs) = x ∷ λ where .force → interleaveN₊ (wrap₊ (y .force) xs) 
  
  open NonemptyColist public
  

