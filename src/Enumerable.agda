{-#  OPTIONS --type-in-type #-}

open import Agda.Builtin.Coinduction
open import Data.List hiding (_++_; zipWith; fromMaybe; [_]; unfold)
open import Relation.Nullary.Decidable
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Data.Vec hiding (zipWith; [_])
open import Data.Nat hiding (_+_; _≤_)
open import Data.Maybe hiding (zipWith; fromMaybe)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import src.Colist

module src.Enumerable where

  -- Enumerable record; the enumeration of a type is a colist with inhabitants
  record Enumerable (a : Set) : Set where
    field enum : Colist a

  open Enumerable ⦃...⦄ public

  record IEnumerable {I : Set} (a : I → Set) : Set where
    field enumI : (i : I) → Colist (a i)

  open IEnumerable ⦃...⦄ public

  -- Can be used in favor of 'enum' for clarity
  inhabitants : (a : Set) ⦃ _ : Enumerable a ⦄ → Colist a
  inhabitants _ = enum

  inhabitants' : {a : Set} → (P : a → Set) ⦃ _ : IEnumerable P ⦄ → (x : a) → Colist (P x)
  inhabitants' _ = enumI

  {-# TERMINATING #-}
  smash : ∀ {a : Set} → Colist (List a) → (Colist a)
  smash [] = []
  smash ([] ∷ xs) = smash (♭ xs)
  smash ((x ∷ ys) ∷ xs) = x ∷ ♯ smash (ys ∷ xs)
  

  catMaybe : ∀ {a : Set} → Colist (Maybe a) → (Colist a)
  catMaybe [] = []
  catMaybe (just x ∷ xs) = (x ∷ ♯ catMaybe (♭ xs))
  catMaybe (nothing ∷ xs) = catMaybe (♭ xs)
  
  smash' : ∀ {a : Set} → Colist (List a) → Colist a
  smash' = catMaybe ∘ (unfold f)
    where f : ∀ {a : Set} → Colist (List a) → Maybe (Colist (List a) ⊗ Maybe a)
          f [] = nothing
          f ([] ∷ xs) = just (♭ xs , nothing)
          f ((x ∷ xs) ∷ xss) = just ((xs ∷ xss) , just x)

  zipCons : ∀ {a : Set} → Colist a → Colist (List a) → Colist (List a)
  zipCons [] ys = ys
  zipCons xs [] = (λ x → x ∷ []) <$> xs
  zipCons (x ∷ xs) (y ∷ ys) = (x ∷ y) ∷ ♯ (zipCons (♭ xs) (♭ ys)) 

  {-# TERMINATING #-}
  stripe : ∀ {a : Set} → Colist (Colist a) → (Colist (List a))
  stripe [] = []
  stripe ([] ∷ xss) = stripe (♭ xss)
  stripe ((x ∷ xs) ∷ xss) = (x ∷ []) ∷ ♯ (zipCons (♭ xs) (stripe (♭ xss)))

  diagonal : ∀ {a : Set} → Colist (Colist a) → Colist a
  diagonal = smash ∘ stripe

  stripe' : ∀ {a : Set} → List (Colist a) → List a ⊗ List (Colist a)
  stripe' [] = [] , []
  stripe' ([] ∷ xs) with stripe' xs
  ... | (xs' , ys') = xs' , ([] ∷ ys')
  stripe' ((x ∷ xs) ∷ xss) with stripe' xss
  ... | (xs' , ys') = (x ∷ xs') , (♭ xs ∷ ys')

  diagonal' : ∀ {a : Set} → Colist (Colist a) → Colist a
  diagonal' [] = []
  diagonal' (x ∷ xs) = {!!}

  multiply : ∀ {a b : Set} → Colist a → Colist b → Colist (Colist (a ⊗ b))
  multiply [] ys = []
  multiply (x ∷ xs) ys = (zipWith (_,_) (repeat x) ys) ∷ ♯ (multiply (♭ xs) ys)

  -- Cartesian product of colists
  _×_ : ∀ {a b : Set} → Colist a → Colist b → Colist (a ⊗ b)
  xs × ys = diagonal (multiply xs ys)

  -- Disjoint union of colists
  _⊎_ : ∀ {a b : Set} → Colist a → Colist b → Colist (a ⊕ b)
  xs ⊎ ys = interleave (inl <$> xs) (inr <$> ys)

  -- Enumeration of coproducts (= disjoint union)
  instance
    enum⊕ : ∀ {a b : Set} ⦃ _ : Enumerable a ⦄ ⦃ _ : Enumerable b ⦄ → Enumerable (a ⊕ b)
    enum⊕ {a} {b} = record { enum = inhabitants a ⊎ inhabitants b }

  -- Enumeration of products (= cartesian product)
  instance
    enum⊗ : ∀ {a b : Set} ⦃ _ : Enumerable a ⦄ ⦃ _ : Enumerable b ⦄ → Enumerable (a ⊗ b)
    enum⊗ {a} {b} = record { enum = inhabitants a × inhabitants b }

  -- Enumeration of all natural numbers
  instance
    enumℕ : Enumerable ℕ
    enumℕ = record { enum = iterate suc 0 }

  data ℚ : Set where
    Q : ℕ ⊗ ℕ → ℚ

  -- Enumeration of all rationals
  instance
   enumℚ : Enumerable ℚ
   enumℚ = record { enum = Q <$> ((suc <$> inhabitants ℕ) × (suc <$> inhabitants ℕ)) }

  instance
    enumBool : Enumerable Bool
    enumBool = record { enum = false ∷ ♯ [ true ] }

  cons : ∀ {a : Set} → Colist (a ⊗ List a) → Colist (List a)
  cons [] = []
  cons ((x , y) ∷ xs) = (x ∷ y) ∷ ♯ cons (♭ xs)

  instance
    {-# TERMINATING #-}
    enumList : ∀ {a : Set} ⦃ _ : Enumerable a ⦄ → Enumerable (List a)
    enumList {a} = record { enum = [] ∷ ♯ cons (inhabitants (a ⊗ List a))  }



  
