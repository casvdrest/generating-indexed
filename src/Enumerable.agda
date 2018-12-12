open import Size

open import Data.List     hiding (_++_; zipWith; fromMaybe; [_]; unfold; map)
open import Data.Bool  
open import Data.Empty
open import Data.Nat      hiding (_+_; _≤_)
open import Data.Maybe    hiding (zipWith; fromMaybe; map)

open import Codata.Colist
open import Codata.Thunk  hiding (map)

open import src.Data
open import src.Product

open import Relation.Binary.PropositionalEquality

module src.Enumerable where

  -- Enumerable record; the enumeration of a type is a colist with inhabitants
  record Enumerable {i : Size} (a : Set) : Set where
    field enum : Colist a i

  open Enumerable ⦃...⦄ public

  record IEnumerable {I : Set} {j : Size} (a : I → Set) : Set where
    field enumI : (i : I) → Colist (a i) j

  open IEnumerable ⦃...⦄ public

  -- Can be used in favor of 'enum' for clarity
  inhabitants : ∀ {i : Size}
                → (a : Set) ⦃ _ : Enumerable a ⦄
                → Colist a i
  inhabitants _ = enum

  inhabitants' : ∀ {a : Set} {i : Size}
                 → (P : a → Set) ⦃ _ : IEnumerable P ⦄
                 → (x : a) → Colist (P x) i
  inhabitants' _ = enumI

  -- Enumeration of coproducts (= disjoint union)
  instance
    enum⊕ : ∀ {a b : Set}
              ⦃ _ : Enumerable a ⦄
              ⦃ _ : Enumerable b ⦄
            ------------------------
            → Enumerable (a ⊕ b)
            
    enum⊕ {a} {b} = record { enum = inhabitants a ⊎ inhabitants b }

  -- Enumeration of products (= cartesian product)
  instance
    enum⊗ : ∀ {a b : Set}
              ⦃ _ : Enumerable a ⦄
              ⦃ _ : Enumerable b ⦄
            ------------------------
            → Enumerable (a ⊗ b)
    enum⊗ {a} {b} =
      record {
        enum = inhabitants a × inhabitants b }

  -- Enumeration of all natural numbers
  instance
    enumℕ : Enumerable ℕ
    enumℕ = record { enum = iterate 0 suc }

  -- Enumeration of all rationals
  instance
   enumℚ : Enumerable ℚ
   enumℚ =
     record {
       enum = map Q
         ((map suc (inhabitants ℕ)) ×
          (map suc (inhabitants ℕ))) }

  instance
    enumBool : Enumerable Bool
    enumBool =
      record {
        enum = true ∷ λ where .force → false ∷ λ where .force → []}

  cons : ∀ {a : Set} {i : Size< ∞}
         → Colist (a ⊗ List a) i
         → Colist (List a) i
  cons [] = []
  cons ((x , y) ∷ xs) = (x ∷ y) ∷ λ where .force → cons (xs .force)

  instance
    enumList : ∀ {a : Set} ⦃ _ : Enumerable a ⦄ → Enumerable (List a)
    enumList {a} = record { enum = {!!} }



  
