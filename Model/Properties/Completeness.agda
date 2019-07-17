open import Model.Base
open import Model.Combinators
open import Model.Enumerate
open import Model.Generic.Isomorphism
open import Model.Data using (_∈_; here; there)
open import Model.Properties.General
open import Model.Properties.Monotonicity

open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum hiding (map)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit hiding (_≤_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Level renaming (zero to zeroL ; suc to sucL)

module Model.Properties.Completeness where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄

  ------ General Properties ------

  -- Productivity property for indexed generators. 
  _∣_↝_ :
    ∀ {I : Set} {a : Set} {t : I → Set} {i : I}
    → Gen a t i → ((i : I) → 𝔾 t i) → a → Set
  _∣_↝_ {i = i} g tg x =
    -- Generator 'g' with top level generator 'tg' will produce 'x'
    -- if there is an 'n ∈ ℕ' such that x is an element of the enumeration
    -- of 'g' under top level generator 'tg' with depth n
    ∃[ n ] (x ∈ enumerate tg i g n)

  -- Completeness for indexed generators. 
  Complete :
    ∀ {I : Set} {a : Set} {t : I → Set} {i : I}
    → Gen a t i  → ((i : I) → 𝔾 t i) → Set
  Complete {a = a} {i = i} g tg =
    -- 'g' is complete iff ∀ x:a . g produces x
    ∀ {x : a} → _∣_↝_ {a = a} g tg x 

  -- Completeness for indexed recursive positions. Complete if the generator the refer
  -- is complete. 
  μ-complete :
    ∀ {I : Set} {a : I → Set}
      {tg : (i : I) → 𝔾 a i} {i : I} {x : a i}
    → _∣_↝_ {a = a i} (tg i) tg x → _∣_↝_ {a = a i} (μ i) tg x
  μ-complete (n , elem)
    -- Elements that occur at depth 'n' in an indexed generator indexed with 'i'
    -- will occur at depth 'suc n' when if 'μ i' refers to that generator
    = (suc n) , elem  

  -- Proof that values lifted into indexed generators will produce 
  pure-complete :
    ∀ {I : Set} {a t : I → Set}
      {i : I} {tg : (i : I) → 𝔾 a i}  {x : a i}
    → _∣_↝_ {a = a i} {i = i} ⦇ x ⦈ tg x
  pure-complete = 1 , here


  ------ Generator Choice ------

  -- Choice between two indexed generators will produce an element if it is produced
  -- by the left generator
  ∥-complete-left :
    ∀ {I : Set} {a t : I → Set} {i : I} {x : a i}
      {f g : Gen (a i) t i} {tg : (i : I) → 𝔾 t i}
    → _∣_↝_ {a = a i} f tg x
    → _∣_↝_ {a = a i} (f ∥ g) tg x
  ∥-complete-left (suc n , p) =
    -- We transform p from x ∈ xs to x ∈ merge xs ys
    (suc n) , merge-complete-left p

  ∥-complete-right :
    ∀ {I : Set} {a t : I → Set} {i : I} {x : a i}
      {f g : Gen (a i) t i} {tg : (i : I) → 𝔾 t i}
    → _∣_↝_ {a = a i} g tg x
    → _∣_↝_ {a = a i} (f ∥ g) tg x
  ∥-complete-right (suc n , p) =
    -- p transformed from y ∈ ys → y ∈ merge xs ys
    (suc n) , merge-complete-right p

  -- Indexed generators, too, are sound
  ∥-sound :
    ∀ {I : Set} {a t : I → Set} {i : I} {x : a i}
      {f g : Gen (a i) t i} {tg : (i : I) → 𝔾 t i}
    → _∣_↝_ {a = a i} (f ∥ g) tg x
    → (_∣_↝_ {a = a i} f tg x) ⊎ (_∣_↝_ {a = a i} g tg x)
  ∥-sound (suc n , p) =
    ⊕-bimap (λ x → suc n , x) (λ y → suc n , y) (merge-sound p)
  
  ------ Generator Product ------

  -- Mapping a bijective function over a complete generator will
  -- result in another bijective generator
  constr-preserves-elem :
    ∀ {I : Set} {a b t : I → Set} {i₁ i₂ : I} {f : a i₁ → b i₂}
      {g : Gen (a i₁) t i₁} {tg : (i : I) → 𝔾 t i} {x : a i₁}
    →  _∣_↝_ {a = a i₁} g tg x
    →  _∣_↝_ {a = b i₂} {i = i₂} ⦇ f g ⦈ tg (f x)
  constr-preserves-elem {f = f} (suc n , elem) = 
    suc n , list-ap-complete {fs = [ f ]} here elem

  -- Calculates the maximum of two natural numbers
  max : ℕ → ℕ → ℕ
  max zero m = m
  max (suc n) zero = suc n
  max (suc n) (suc m) = suc (max n m)

  -- 'max n 0' is 'n' , for all 'n'. 
  max-zero : ∀ {n : ℕ} → max n 0 ≡ n
  max-zero {zero} = refl
  max-zero {suc n} = refl

  -- 'max 0 n' is 'n' for all 'n'. 
  max-zero' : ∀ {n : ℕ} → max 0 n ≡ n
  max-zero' = refl

  -- 'max n m' is equal to 'max m n' 
  max-sym : ∀ {n m} → max n m ≡ max m n
  max-sym {zero} {m} rewrite max-zero {m} = refl
  max-sym {suc n} {zero} = refl
  max-sym {suc n} {suc m} = cong suc (max-sym {n} {m})

  -- Any number is smaller than or equal to the maximum of any
  -- other number and itself
  lemma-max₁ : ∀ {n m : ℕ} → n ≤ max n m
  lemma-max₁ {zero} {m} = z≤n
  lemma-max₁ {suc n} {zero} rewrite max-zero {n = n}
    = s≤s ≤-refl
  lemma-max₁ {suc n} {suc m} = s≤s lemma-max₁

  lemma-max₂ : ∀ {n m : ℕ} → m ≤ max n m
  lemma-max₂ {n} {m} rewrite max-sym {n} {m} = lemma-max₁ 
  
  -- If f produces x and g produces y, then ⦇ C f g ⦈, where C is any
  -- 2-arity constructor, produces C x y
  ⊛-complete :
    ∀ {I : Set} {a b c t : I → Set} {i₁ i₂ i₃ : I}
      {x : a i₁} {y : b i₂} {tg : (i : I) → 𝔾 t i}
      {f : Gen (a i₁) t i₁} {g : Gen (b i₂) t i₂} {C : a i₁ → b i₂ → c i₃}
    → (p₁ : _∣_↝_ {a = a i₁} f tg x) → (p₂ : _∣_↝_ {a = b i₂} g tg y)
    → Depth-Monotone f tg x → Depth-Monotone g tg y 
    → _∣_↝_ {a = c i₃} {i = i₃} ⦇ C f g ⦈ tg (C x y)
  ⊛-complete {a} {b} {c} {f = f} {g = g} {C = C}
    ((suc n) , snd₁) ((suc m) , snd₂) mt₁ mt₂  =  
    max (suc n) (suc m) , list-ap-constr {C = C}
      (mt₁ (lemma-max₁ {n = suc n} {m = suc m}) snd₁)
      (mt₂ (lemma-max₂ {n = suc n} {m = suc m}) snd₂)
  
  ------ Combinator Completeness ------

  -- A choice between two copmlete generator is itself a
  -- complete generator
  ∥-Complete :
    ∀ {I : Set} {a b t : I → Set} {i : I} {f : Gen (a i) t i}
      {g : Gen (b i) t i} {tg : (i : I) → 𝔾 t i}
    → Complete {a = a i} f tg → Complete {a = b i} g tg
    → Complete {a = a i ⊎ b i} (⦇ inj₁ f ⦈ ∥ ⦇ inj₂ g ⦈) tg
  ∥-Complete {a = a} {b = b} {f = f} {g = g} p₁ p₂ {inj₁ x} =
    ∥-complete-left {a = λ i → a i ⊎ b i} {f = ⦇ inj₁ f ⦈} {g = ⦇ inj₂ g ⦈}
    (constr-preserves-elem {a = a} {b = λ i → a i ⊎ b i} {g = f} p₁)
  ∥-Complete {a = a} {b = b} {f = f} {g = g} p₁ p₂ {inj₂ y} =
    ∥-complete-right {a = λ i → a i ⊎ b i} {f = ⦇ inj₁ f ⦈} {g = ⦇ inj₂ g ⦈}
    (constr-preserves-elem {a = b} {b = λ i → a i ⊎ b i} {g = g} p₂)

  
