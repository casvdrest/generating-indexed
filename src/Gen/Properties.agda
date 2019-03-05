open import src.Gen.Base
open import src.Gen.Regular.Isomorphism
open import src.Data using (_∈_; here; _⊕_; inl; inr; there; merge)

open import src.Gen.ListProperties
open import src.Gen.Monotonicity

open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum hiding (map)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Category.Functor
open import Category.Applicative
open import Category.Monad

module src.Gen.Properties where

  open RawApplicative ⦃...⦄

  ------ General Properties ------

  -- Generator productivity: we say that a generator produces
  -- Some value 'x' if there is some n ∈ ℕ such that 'x' is in
  -- the list we get by applying 'n' to the generator. 
  _↝_ : ∀ {a : Set} → (∀ {n : ℕ} → 𝔾 a n) → a → Set
  f ↝ x = ∃[ n ] (x ∈ f (n , refl))

  -- Completeness: A generator is complete if we can produce
  -- a productivity proof for all values of its type
  Complete : ∀ {a : Set} → (∀ {n : ℕ} → 𝔾 a n) → Set
  Complete {a} f = ∀ {x : a} → f ↝ x

  ------ Generator Choice ------
  
  -- Choice between two generators produces an element, given that it is
  -- produced by its left option
  ∥-complete-left : ∀ {a : Set} {x : a} {f g : ∀ {n : ℕ} → 𝔾 a n}
                    → f ↝ x
                    ------------------------------------
                    → (f ∥ g) ↝ x
  ∥-complete-left (n , p) = n , merge-complete-left p

  -- Choice between two generators produces an element, given that it is produced
  -- by its right option
  ∥-complete-right : ∀ {a : Set} {x : a} {f g : ∀ {n : ℕ} → 𝔾 a n}
                     → g ↝ x
                     ------------------------------------
                     → (f ∥ g) ↝ x
  ∥-complete-right (n , p) = n , merge-complete-right p

  -- If an element is produced by choice between two generators, it is either
  -- produced by the left option or by the right option
  ∥-sound : ∀ {a : Set} {x : a} {n : ℕ} → {f g : ∀ {n : ℕ} → 𝔾 a n}
            → (f ∥ g) ↝ x
            ------------------------------------
            → (f ↝ x) ⊕ (g ↝ x)
  ∥-sound (n , prf) = ⊕-bimap (λ x → n , x) (λ y → n , y) (merge-sound prf)

  ------ Generator Product ------

  depth : ∀ {a : Set} {n : ℕ} → 𝔾 a n → ℕ
  depth {n = n} _ = n

  -- Applying a constructor to a generator does not affect
  -- its production
  constr-preserves-elem : ∀ {a b : Set} {f : a → b}
                            {g : ∀ {n : ℕ} → 𝔾 a n} {x : a}
                          → g ↝ x
                          ---------------------------
                          → ⦇ f g ⦈ ↝ f x
  constr-preserves-elem {f = f} (p , elem) =
    p , list-ap-complete {fs = f ∷ []} here elem

  max : ℕ → ℕ → ℕ
  max zero m = m
  max (suc n) zero = suc n
  max (suc n) (suc m) = suc (max n m)

  max-zero : ∀ {n : ℕ} → max n 0 ≡ n
  max-zero {zero} = refl
  max-zero {suc n} = refl

  max-zero' : ∀ {n : ℕ} → max 0 n ≡ n
  max-zero' = refl

  max-sym : ∀ {n m} → max n m ≡ max m n
  max-sym {zero} {m} rewrite max-zero {m} = refl
  max-sym {suc n} {zero} = refl
  max-sym {suc n} {suc m} = cong suc (max-sym {n} {m})

  lemma-max₁ : ∀ {n m : ℕ} → n ≤ max n m
  lemma-max₁ {zero} {m} = z≤n
  lemma-max₁ {suc n} {zero} rewrite max-zero {n = n}
    = s≤s ≤-refl
  lemma-max₁ {suc n} {suc m} = s≤s lemma-max₁
  
  lemma-max₂ : ∀ {n m : ℕ} → m ≤ max n m
  lemma-max₂ {n} {m} rewrite max-sym {n} {m} = lemma-max₁ 

  -- If f produces x and g produces y, then ⦇ C f g ⦈, where C is any
  -- 2-arity constructor, produces C x y
  ⊛-complete : ∀ {a b c : Set} {x : a} {y : b}
                 {f : ∀ {n : ℕ} → 𝔾 a n} {g : ∀ {n : ℕ} → 𝔾 b n} {C : a → b → c}
               → (p₁ : f ↝ x) → (p₂ : g ↝ y)
               → Depth-Monotone f x → Depth-Monotone g y
               -------------------------------------
               → ⦇ C f g ⦈ ↝ C x y
  ⊛-complete {a} {b} {c} {f = f} {g = g} {C = C} (n , snd₁) (m , snd₂) mt₁ mt₂  =
    max n m , list-ap-constr {a = a} {b = b} {c = c} {xs = f ((max n m) , refl)}
    (mt₁ (lemma-max₁ {n = n} {m = m}) snd₁)
    (mt₂ (lemma-max₂ {n = n} {m = m}) snd₂)

  ------ Combinator Completeness ------

  -- Completeness of the ∥ combinator, using coproducts to unify
  -- option types
  ∥-Complete : ∀ {a b : Set} {f : ∀ {n : ℕ} → 𝔾 a n} {g : ∀ {n : ℕ} → 𝔾 b n}
               → Complete f → Complete g
               ------------------------------------
               → Complete (⦇ inj₁ f ⦈ ∥ ⦇ inj₂ g ⦈)
  ∥-Complete {f = f} {g = g} p₁ p₂ {inj₁ x} =
    ∥-complete-left {f = ⦇ inj₁ f ⦈} {g = ⦇ inj₂ g ⦈} (constr-preserves-elem {g = f} p₁)
  ∥-Complete {f = f} {g = g} p₁ p₂ {inj₂ y} =
    ∥-complete-right {f = ⦇ inj₁ f ⦈} {g = ⦇ inj₂ g ⦈} (constr-preserves-elem {g = g} p₂)
