open import Agda.Builtin.Size

open import Data.Bool
open import Data.Nat
open import Data.List hiding (_++_; concat; map; zipWith; [_]; take)
open import Agda.Builtin.Coinduction hiding (∞)

open import Codata.Colist
open import Codata.Thunk hiding (map)

open import Relation.Binary.PropositionalEquality

module src.Sized where

  module List₊ where
  
    data List₊ (a : Set) : Set where
       [_] : a → List₊ a
       _∷_ : a → List₊ a → List₊ a

    toList : ∀ {a : Set} → List₊ a → List a
    toList [ x ] = x ∷ []
    toList (x ∷ xs) = x ∷ toList xs

    toList₊ : ∀ {a : Set} → a → List a → List₊ a
    toList₊ y [] = [ y ]
    toList₊ y (x ∷ xs) = y ∷ toList₊ x xs

  module Colist₊ where
  
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

  open List₊
  open Colist₊

  concat : ∀ {a : Set} {i : Size}
           → (xs : Colist (List₊ a) i)
           → Colist a i
  concat [] = []
  concat ([ x ] ∷ xss) =
    x ∷ λ where .force → concat (xss .force)
  concat ((x ∷ xs) ∷ xss) =
    x ∷ λ where .force → concat (xs ∷ xss)

  data _⊗_ (a b : Set) : Set where
    _,_ : a → b → a ⊗ b

  stripe'₁ : ∀ {a : Set} {i j : Size}  
             → List₊ (Colist₊ a ∞)
             → List₊ a ⊗ List₊ (Colist a j)
  stripe'₁ [ [ x ] ] = [ x ] , [ [] ]
  stripe'₁ [ x ∷ xs ] = [ x ] , [ toColist (xs .force) ]
  stripe'₁ (x ∷ xs) with stripe'₁ xs 
  ... | ys , rs = (head₊ x ∷ ys) , (tail₊ x ∷ rs)

  filterEmpty : ∀ {a : Set} {i : Size} {j : Size< i}
                → List₊ (Colist a i)
                → List (Colist₊ a j)
  filterEmpty [ [] ] = []
  filterEmpty [ x ∷ xss ] = toColist₊ x (xss .force) ∷ []
  filterEmpty ([] ∷ xss) = filterEmpty xss
  filterEmpty ((x ∷ xs) ∷ xss) = toColist₊ x (xs .force) ∷ filterEmpty xss

  stripe' : ∀ {a : Set} {i j : Size} 
            → List₊ (Colist₊ a ∞)
            → Colist (Colist₊ a ∞) ∞
            → Colist₊ (List₊ a) i
  stripe' xs zs with stripe'₁ xs 
  stripe' xs zs | ys , rs with filterEmpty rs
  stripe' xs zs | ys , rs | [] = [ ys ]
  stripe' xs [] | ys , rs | x ∷ xss =
    ys ∷ λ where .force → stripe' (toList₊ x xss) []
  stripe' xs (z ∷ zs) | ys , rs | x ∷ xss =
    ys ∷ λ where .force → stripe' (toList₊ z (x ∷ xss)) (zs .force)
  
  diagonal : ∀ {a : Set} → Colist (Colist₊ a ∞) ∞ → Colist a ∞
  diagonal [] = []
  diagonal (xs ∷ xss) = concat (toColist (stripe' [ xs ] (xss .force)))

  multiply : ∀ {a b : Set} {i j : Size} 
             → Colist a i → Colist₊ b j
             → Colist (Colist₊ (a ⊗ b) j ) i
  multiply []       _  = []
  multiply (x ∷ xs) ys = zipWith₊ _,_ (repeat₊ x) ys ∷ λ where .force → multiply (xs .force) ys

  -- Cartesian product of colists
  _×_ : ∀ {a b : Set} → Colist a ∞ → Colist b ∞ → Colist (a ⊗ b) ∞
  xs × [] = []
  xs × (y ∷ ys) = diagonal (multiply xs (toColist₊ y (ys .force)))

  iterate : ∀ {a : Set} {i : Size} → a → (a → a) → Colist a i
  iterate x f = x ∷ λ where .force → iterate (f x) f

  naturals : Colist ℕ ∞
  naturals = iterate 0 suc

  booleans : Colist Bool ∞
  booleans = true ∷ λ where .force → false ∷ λ where .force → []

  prefix : ∀ {a : Set} → ℕ → Colist a ∞ → List a
  prefix zero xs = []
  prefix (suc n) [] = []
  prefix (suc n) (x ∷ xs) = x ∷ prefix n (xs .force)

  prop : prefix 10 naturals ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  prop = refl

  --   | 0 1 2 3 4 5 
  -- --+------------
  -- 0 | ↗ ↗ ↗ ↗ . . 
  -- 1 | ↗ ➚ ↗ . . .
  -- 2 | ➚ ➚ ↗ . . .
  -- 3 | ➚ ↗ . . . .
  -- 4 | ↗ . . . . .
  -- 5 | . . . . . .
  prop1 : prefix 13 (naturals × naturals)
    ≡  0 , 0 ∷ 1 , 0 ∷ 0 , 1 ∷ 2 , 0 ∷ 1 , 1 ∷
       0 , 2 ∷ 3 , 0 ∷ 2 , 1 ∷ 1 , 2 ∷ 0 , 3 ∷
       4 , 0 ∷ 3 , 1 ∷ 2 , 2 ∷ []
  prop1 = refl

  --   | t f 
  -- --+----
  -- t | ↗ ↗ 
  -- f | ↗ ↗
  prop2 : prefix 4 (booleans × booleans)
    ≡ true , true  ∷ false , true  ∷
      true , false ∷ false , false ∷ []
  prop2 = refl

  --   | 0 1 2 3 4 5 6 7 
  -- --+----------------
  -- t | ↗ ↗ ↗ ↗ ↗ ↗ ↗ .
  -- f | ↗ ➚ ↗ ↗ ↗ ↗ . .
  prop3 : prefix 11 (booleans × naturals)
    ≡ (true , 0) ∷ (false , 0) ∷ (true , 1) ∷ (false , 1) ∷
      (true , 2) ∷ (false , 2) ∷ (true , 3) ∷ (false , 3) ∷
      (true , 4) ∷ (false , 4) ∷ (true , 5) ∷ []
  prop3 = refl

  --   | t f 
  -- --+----
  -- 0 | ↗ ↗ 
  -- 1 | ↗ ↗
  -- 2 | ↗ ↗ 
  -- 3 | ↗ ↗ 
  -- 4 | ↗ ↗ 
  -- 5 | ↗ ↗ 
  -- 6 | ↗ .
  -- 7 | . .
  prop4 : prefix 11 (naturals × booleans)
    ≡ (0 , true)  ∷ (1 , true) ∷ (0 , false) ∷ (2 , true) ∷
      (1 , false) ∷ (3 , true) ∷ (2 , false) ∷ (4 , true) ∷
      (3 , false) ∷ (5 , true) ∷ (4 , false) ∷ []
  prop4 = refl
