open import Size

open import Codata.Colist
open import Codata.Thunk hiding (map)

open import Data.List hiding (map; zipWith)

open import src.Data

module src.ProductOld where

  {-# TERMINATING #-}
  smash : ∀ {a : Set} → Colist (List a) ∞ → Colist a ∞
  smash [] = []
  smash ([] ∷ xss) = smash (xss .force)
  smash ((x ∷ xs) ∷ xss) = x ∷ λ where .force → smash (xs ∷ xss)

  zipCons : ∀ {a : Set} {i : Size} → Colist a i → Colist (List a) i → Colist (List a) i
  zipCons [] ys = ys
  zipCons xs [] = map (λ x → x ∷ []) xs
  zipCons (x ∷ xs) (y ∷ ys) = (x ∷ y) ∷ λ where .force → (zipCons (xs .force) (ys .force)) 

  {-# TERMINATING #-}
  stripe : ∀ {a : Set} → Colist (Colist a ∞) ∞ → (Colist (List a)) ∞
  stripe [] = []
  stripe ([] ∷ xss) = stripe (xss .force)
  stripe ((x ∷ xs) ∷ xss) = (x ∷ []) ∷ λ where .force → (zipCons (xs .force) (stripe (xss .force)))

  diagonal : ∀ {a : Set} → Colist (Colist a ∞) ∞ → Colist a ∞
  diagonal xs = smash (stripe xs)

  multiply : ∀ {a b : Set} {i : Size} → Colist a i → Colist b ∞ → Colist (Colist (a ⊗ b) ∞) i
  multiply [] ys = []
  multiply (x ∷ xs) ys = (zipWith (_,_) (repeat x) ys) ∷ λ where .force →  (multiply (xs .force) ys)

  -- Cartesian product of colists
  _×_ : ∀ {a b : Set} → Colist a ∞ → Colist b ∞ → Colist (a ⊗ b) ∞
  xs × ys = diagonal (multiply xs ys)

  _⊛_ : ∀ {a b : Set} → Colist (a → b) ∞ → Colist a ∞ → Colist b ∞
  fs ⊛ xs = map (λ p → (fst p) (snd p)) (fs × xs)
