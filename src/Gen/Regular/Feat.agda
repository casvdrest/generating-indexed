module Feat where

  open import Data.Nat
  open import Data.List

  open import Data.Product
  open import Data.Sum

  open import Relation.Binary.PropositionalEquality

  postulate undefined : ∀ {a : Set} → a

  data Finite (a : Set) : Set where
    Nil  : Finite a
    Cons : a → Finite a → Finite a

  mapfin : ∀ {a b : Set} → (a → b) → Finite a → Finite b
  mapfin f Nil = Nil
  mapfin f (Cons x fin) = Cons (f x) (mapfin f fin)

  concatfin : ∀ {a : Set} → Finite a → Finite a → Finite a
  concatfin Nil fin₂ = fin₂
  concatfin (Cons x fin₁) fin₂ = Cons x (concatfin fin₁ fin₂)

  foldfin : ∀ {a b : Set} → (a → b → b) → b → Finite a → b
  foldfin f z Nil = z
  foldfin f z (Cons x fin) = f x (foldfin f z fin)

  card : ∀ {a : Set} → Finite a → ℕ
  card Nil = 0
  card (Cons x fin) = suc (card fin)

  _‼_ : ∀ {a : Set} → Finite a → ℕ → a
  Nil ‼ n = undefined
  Cons x fin ‼ zero = x
  Cons x fin ‼ suc n = fin ‼ n

  values : ∀ {a : Set} → Finite a → List a
  values Nil = []
  values (Cons x fin) = x ∷ values fin

  trans_prop1 : ∀ {a : Set} {fin : Finite a} → card fin ≡ length (values fin)
  trans_prop1 {fin = Nil} = refl
  trans_prop1 {fin = Cons x fin} = cong suc trans_prop1

  E : Set → Set
  E a = ℕ → Finite a

  emptyF : ∀ {a : Set} → Finite a
  emptyF = Nil

  singletonF : ∀ {a : Set} → a → Finite a
  singletonF x = Cons x Nil

  _⊕f_ : ∀ {a b : Set} → Finite a → Finite b → Finite (a ⊎ b)
  Nil ⊕f fin₂ = mapfin inj₂ fin₂
  Cons x fin₁ ⊕f fin₂ = Cons (inj₁ x) (fin₁ ⊕f fin₂)

  _⊗f_ : ∀ {a b : Set} → Finite a → Finite b → Finite (a × b)
  fin₁ ⊗f fin₂ = foldfin (λ x fin → concatfin (mapfin (_,_ x) fin₂) fin) Nil fin₁

  empty : ∀ {a : Set} → E a
  empty _ = emptyF

  singleton : ∀ {a : Set} → a → E a
  singleton x zero    = singletonF x
  singleton _ (suc _) = emptyF

  
