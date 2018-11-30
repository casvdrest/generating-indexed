{-#  OPTIONS --type-in-type #-}

open import Agda.Builtin.Coinduction
open import Data.List hiding (_++_; zipWith; fromMaybe)
open import Relation.Nullary.Decidable
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Data.Unit
open import Data.Nat hiding (_+_)
open import Data.Maybe hiding (zipWith; fromMaybe)
open import Relation.Binary.PropositionalEquality

open import src.Generic

module src.Enumerable where

  data Coℕ : Set where
    CoZ : Coℕ
    CoS : ∞ Coℕ → Coℕ

  data Colist (A : Set) : Set where
    []   : Colist A
    _∷_  : A → ∞ (Colist A) → Colist A

  data Pair (a : Set) (b : Set) : Set where
    MkPair : a → b → Pair a b

  data Either (a : Set) (b : Set) : Set where
    Left : a → Either a b
    Right : b → Either a b

  data Stream (A : Set) : Set where
    Cons : A → ∞ (Stream A) → Stream A

  inf : Coℕ
  inf = CoS (♯ inf)

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

  zipWith : ∀ {A B C : Set} → (A → B → C) → Colist A → Colist B → Colist C
  zipWith f []       _        = []
  zipWith f _        []       = []
  zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ ♯ zipWith f (♭ xs) (♭ ys)

  interleave : ∀ {A : Set} → Colist A → Colist A → Colist A
  interleave [] _  = []
  interleave _  [] = []
  interleave (x ∷ xs) (y ∷ ys) = x ∷ ♯ (y ∷ ♯ interleave (♭ xs) (♭ ys))

  {-# TERMINATING #-}
  smash : ∀ {a : Set} → Colist (List a) → Colist a
  smash [] = []
  smash ((x ∷ xs) ∷ xss) = x ∷ ♯ smash (xs ∷ xss)
  smash ([] ∷ xss) = smash (♭ xss)

  zipCons : ∀ {a : Set} → Colist a → Colist (List a) → Colist (List a)
  zipCons [] ys = ys
  zipCons xs [] = (λ x → x ∷ []) <$> xs
  zipCons (x ∷ xs) (y ∷ ys) = (x ∷ y) ∷ ♯ (zipCons (♭ xs) (♭ ys)) 

  {-# TERMINATING #-}
  stripe : ∀ {a : Set} → Colist (Colist a) →(Colist (List a))
  stripe [] = []
  stripe ([] ∷ xss) = stripe (♭ xss)
  stripe ((x ∷ xs) ∷ xss) = (x ∷ []) ∷ ♯ (zipCons (♭ xs) (stripe (♭ xss)))

  diagonal : ∀ {a : Set} → Colist (Colist a) → Colist a
  diagonal = smash ∘ stripe

  multiply : ∀ {a b : Set} → Colist a → Colist b → Colist (Colist (Pair a b))
  multiply [] ys = []
  multiply (x ∷ xs) ys = (zipWith MkPair (repeat x) ys) ∷ ♯ (multiply (♭ xs) ys)
  
  _×_ : ∀ {a b : Set} → Colist a → Colist b → Colist (Pair a b)
  xs × ys = diagonal (multiply xs ys)

  record Enumerable (A : Set) : Set where
    field enumerate : Colist A

  open Enumerable ⦃...⦄ public

  inhabitants : (A : Set) ⦃ _ : Enumerable A ⦄ → Colist A
  inhabitants _ = enumerate

  instance
    enumBool : Colist Bool
    enumBool = fromList' (true ∷ (false ∷ []))

  instance
    enumℕ : Colist ℕ
    enumℕ = iterate suc zero

  instance
    enum⊕ : ∀ {r : Set} → {a b : Set → Set}
              ⦃ _ : Enumerable (a r) ⦄ ⦃ _ : Enumerable (b r) ⦄ →
              Colist ((a ⊕ b) r)
    enum⊕ = interleave (inl <$> enumerate) (inr <$> enumerate)

  instance
    enum⊗ : ∀ {r : Set} → {a b : Set → Set}
              ⦃ _ : Enumerable (a r) ⦄ ⦃ _ : Enumerable (b r) ⦄ →
              Colist ((a ⊗ b) r)
    enum⊗ = zipWith _,_ enumerate enumerate

  instance
    enum𝒰 : ∀ {r : Set} → Colist (𝒰 r)
    enum𝒰 = U ∷ ♯ []

  instance
    enumℐ : ∀ {r : Set} ⦃ _ : Enumerable r ⦄ → Colist (ℐ r)
    enumℐ = I <$> enumerate

  instance
    enum𝒦 : ∀ {a : Set} ⦃ _ : Enumerable a ⦄ {r : Set} → Colist (𝒦 a r)
    enum𝒦 = K <$> enumerate
