module src.Gen.Combinators where

  open import Size
  open import src.Gen.Base

  open import Data.List
  open import Data.Nat
  open import Data.Fin hiding (_+_)

  open import Codata.Colist
  open import Codata.Thunk

  open import Category.Applicative

  open import Relation.Binary.PropositionalEquality

  open RawApplicative ⦃...⦄ using (_<*>_; pure)

  {-# TERMINATING #-}
  nats : List ℕ
  nats = 1 ∷ Data.List.map suc nats

  prop1 : Data.List.take 10 nats ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []
  prop1 = refl

  nats' : ∀ {i : Size} → Colist ℕ i
  nats' = 1 ∷ λ where .force → Codata.Colist.map suc nats'

  {-
  length' : ∀ {a : Set} → Colist a ∞ →  ℕ
  length' [] = 0
  length' (x ∷ xs) = suc (length' (xs .force)) -}

  data List' (a : Set) : Size → Set where
    []  : ∀ {i} → List' a i
    _∷_ : ∀ {i} → a → List' a i → List' a (↑ i)

  map' : ∀ {i} {a b : Set} → (a → b) → List' a i → List' b i
  map' f [] = []
  map' f (x ∷ xs) = f x ∷ map' f xs

  incpos : ∀ {i} → List' ℕ i → List' ℕ i
  incpos [] = []
  incpos (x ∷ xs) = x ∷ incpos (map' suc xs)

  data Term : ℕ → Set where
    Lam : ∀ {n : ℕ} → Term (suc n) → Term n
    App : ∀ {n : ℕ} → Term n → Term n → Term n
    Var : ∀ {n : ℕ} → Fin n → Term n
