{-#  OPTIONS --type-in-type #-}

open import Agda.Builtin.Coinduction
open import Data.List hiding (_++_; zipWith; fromMaybe; [_]; unfold)

open import Relation.Nullary.Decidable
open import Data.Bool 
open import Data.Empty
open import Data.Unit
open import Data.Nat hiding (_+_)
open import Data.Maybe hiding (zipWith; fromMaybe)

open import Relation.Binary.PropositionalEquality hiding ([_]; cong)

module src.Colist where

  -- Function composition
  _∘_ : ∀ {a b c : Set} → (b → c) → (a → b) → a → c
  (g ∘ f) x = g (f x)

  -- Coproducts
  data _⊕_ (a b : Set) : Set where
    inl : a → a ⊕ b
    inr : b → a ⊕ b

  -- Product
  data _⊗_ (a b : Set) : Set where
    _,_ : a → b → a ⊗ b

  fst : ∀ {a b : Set} → a ⊗ b → a
  fst (x , _) = x

  snd : ∀ {a b : Set} → a ⊗ b → b
  snd (_ , y) = y

  curry : ∀ {a b c : Set} → (a ⊗ b → c) → a → b → c
  curry f x y = f (x , y)

  uncurry : ∀ {a b c : Set} → (a → b → c) → a ⊗ b → c
  uncurry f (x , y) = f x y

  data Σ (a : Set) (P : a → Set) : Set where
    sigma : (x : a) → P x → Σ a P

  Π : (a : Set) → (P : a → Set) → Set
  Π a P = (x : a) → P x

  data Coℕ : Set where
    CoZ : Coℕ
    CoS : ∞ Coℕ → Coℕ

  data Colist (A : Set) : Set where
    []   : Colist A
    _∷_  : A → ∞ (Colist A) → Colist A

  [_] : ∀ {a : Set} → a → Colist a
  [ x ] = x ∷ ♯ []

  data Pair (a : Set) (b : Set) : Set where
    MkPair : a → b → Pair a b

  data Either (a : Set) (b : Set) : Set where
    Left : a → Either a b
    Right : b → Either a b

  comap : ∀ {A B : Set}  → (A → B) → Colist A → Colist B
  comap f [] = []
  comap f (x ∷ xs) = f x ∷ (♯ (comap f (♭ xs)))

  _<$>_ : ∀ {A B : Set} → (A → B) → Colist A → Colist B
  _<$>_ = comap

  infixl 5 _<$>_

  fromList' : ∀ {A : Set} → (xs : List A) → Colist A
  fromList' [] = []
  fromList' (x ∷ xs) = x ∷ ♯ fromList' (xs)

  repeat : ∀ {A : Set} → A → Colist A
  repeat x = x ∷ ♯ repeat x

  iterate : ∀ {A : Set} → (A → A) → A → Colist A
  iterate f x = x ∷ ♯ iterate f (f x)

  interleave : ∀ {A : Set} → Colist A → Colist A → Colist A
  interleave [] xs  = xs
  interleave xs  [] = xs
  interleave (x ∷ xs) (y ∷ ys) = x ∷ ♯ (y ∷ ♯ interleave (♭ xs) (♭ ys))

  zipWith : ∀ {A B C : Set} → (A → B → C) → Colist A → Colist B → Colist C
  zipWith f []       _        = []
  zipWith f _        []       = []
  zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ ♯ zipWith f (♭ xs) (♭ ys)

  take' : ∀ {a : Set} → ℕ → Colist a → List a
  take' zero xs = []
  take' (suc n) [] = []
  take' (suc n) (x ∷ xs) = x ∷ take' n (♭ xs)

  data _∈_ {a : Set} : a → (Colist a) → Set where 
    here  : ∀ {x : a} {xs : ∞ (Colist a)} → x ∈ (x ∷ xs)
    there : ∀ {x y : a} {xs : ∞ (Colist a)} → x ∈ (♭ xs) → x ∈ (y ∷ xs) 

  data _∼_ {a : Set} : Colist a → Colist a → Set where
    []∼ : [] ∼ []
    ∷∼_  : ∀ {x : a} {xs ys : ∞ (Colist a)} → ∞ (♭ xs ∼ ♭ ys) → (x ∷ xs) ∼ (x ∷ ys)

  fromMaybe : ∀ {a : Set} → Maybe a → Colist a
  fromMaybe (just x) = [ x ]
  fromMaybe nothing = []

  unfold :  ∀ {a b : Set} → (a → Maybe (a ⊗ b)) → a → Colist b
  unfold next seed with next seed
  ... | nothing          = []
  ... | just (seed' , b) = b ∷ ♯ (unfold next seed')

  
