open import AgdaGen.Base
open import AgdaGen.Combinators
open import AgdaGen.Enumerate
open import AgdaGen.Generic.Isomorphism
open import AgdaGen.Data using (_∈_; here; _⊕_; inl; inr; there; merge)

open import AgdaGen.Properties.General
open import AgdaGen.Properties.Monotonicity

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

module AgdaGen.Properties.Completeness where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄

  ------ General Properties ------

  -- Productivity property for indexed generators. 
  _∣ᵢ_↝_ :
    ∀ {I : Set} {a : Set} {t : I → Set} {i : I}
    → Gen a t i → ((i : I) → 𝔾 t i) → a → Set
  _∣ᵢ_↝_ {i = i} g tg x =
    -- Generator 'g' with top level generator 'tg' will produce 'x'
    -- if there is an 'n ∈ ℕ' such that x is an element of the enumeration
    -- of 'g' under top level generator 'tg' with depth n
    ∃[ n ] (x ∈ enumerate tg i g n)

  -- Completeness for indexed generators. 
  Completeᵢ :
    ∀ {I : Set} {a : Set} {t : I → Set} {i : I}
    → Gen a t i  → ((i : I) → 𝔾 t i) → Set
  Completeᵢ {a = a} {i = i} g tg =
    -- 'g' is complete iff ∀ x:a . g produces x
    ∀ {x : a} → _∣ᵢ_↝_ {a = a} g tg x 

  -- Completeness for indexed recursive positions. Complete if the generator the refer
  -- is complete. 
  μᵢ-complete :
    ∀ {I : Set} {a : I → Set}
      {tg : (i : I) → 𝔾 a i} {i : I} {x : a i}
    → _∣ᵢ_↝_ {a = a i} (tg i) tg x → _∣ᵢ_↝_ {a = a i} (μ i) tg x
  μᵢ-complete (n , elem)
    -- Elements that occur at depth 'n' in an indexed generator indexed with 'i'
    -- will occur at depth 'suc n' when if 'μᵢ i' refers to that generator
    = (suc n) , elem  

  -- Proof that values lifted into indexed generators will produce 
  pureᵢ-complete :
    ∀ {I : Set} {a t : I → Set}
      {i : I} {tg : (i : I) → 𝔾 a i}  {x : a i}
    → _∣ᵢ_↝_ {a = a i} {i = i} ⦇ x ⦈ tg x
  pureᵢ-complete = 1 , here


  ------ Generator Choice ------

  -- Choice between two indexed generators will produce an element if it is produced
  -- by the left generator
  ∥ᵢ-complete-left :
    ∀ {I : Set} {a t : I → Set} {i : I} {x : a i}
      {f g : Gen (a i) t i} {tg : (i : I) → 𝔾 t i}
    → _∣ᵢ_↝_ {a = a i} f tg x
    → _∣ᵢ_↝_ {a = a i} (f ∥ g) tg x
  ∥ᵢ-complete-left (suc n , p) =
    -- Again, we transform p from x ∈ xs to x ∈ merge xs ys
    (suc n) , merge-complete-left p

  ∥ᵢ-complete-right :
    ∀ {I : Set} {a t : I → Set} {i : I} {x : a i}
      {f g : Gen (a i) t i} {tg : (i : I) → 𝔾 t i}
    → _∣ᵢ_↝_ {a = a i} g tg x
    → _∣ᵢ_↝_ {a = a i} (f ∥ g) tg x
  ∥ᵢ-complete-right (suc n , p) =
    -- p transformed from y ∈ ys → y ∈ merge xs ys
    (suc n) , merge-complete-right p

  -- Indexed generators, too, are sound
  ∥ᵢ-sound :
    ∀ {I : Set} {a t : I → Set} {i : I} {x : a i}
      {f g : Gen (a i) t i} {tg : (i : I) → 𝔾 t i}
    → _∣ᵢ_↝_ {a = a i} (f ∥ g) tg x
    → (_∣ᵢ_↝_ {a = a i} f tg x) ⊎ (_∣ᵢ_↝_ {a = a i} g tg x)
  ∥ᵢ-sound (suc n , p) =
    ⊕-bimap (λ x → suc n , x) (λ y → suc n , y) (merge-sound p)
  
  ------ Generator Product ------

  constrᵢ-preserves-elem :
    ∀ {I : Set} {a b t : I → Set} {i₁ i₂ : I} {f : a i₁ → b i₂}
      {g : Gen (a i₁) t i₁} {tg : (i : I) → 𝔾 t i} {x : a i₁}
    →  _∣ᵢ_↝_ {a = a i₁} g tg x
    →  _∣ᵢ_↝_ {a = b i₂} {i = i₂} ⦇ f g ⦈ tg (f x)
  constrᵢ-preserves-elem {f = f} (suc n , elem) = 
    suc n , list-ap-complete {fs = [ f ]} here elem
  
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
  ⊛-completeᵢ :
    ∀ {I : Set} {a b c t : I → Set} {i₁ i₂ i₃ : I}
      {x : a i₁} {y : b i₂} {tg : (i : I) → 𝔾 t i}
      {f : Gen (a i₁) t i₁} {g : Gen (b i₂) t i₂} {C : a i₁ → b i₂ → c i₃}
    → (p₁ : _∣ᵢ_↝_ {a = a i₁} f tg x) → (p₂ : _∣ᵢ_↝_ {a = b i₂} g tg y)
    → Depth-Monotoneᵢ f tg x → Depth-Monotoneᵢ g tg y 
    → _∣ᵢ_↝_ {a = c i₃} {i = i₃} ⦇ C f g ⦈ tg (C x y)
  ⊛-completeᵢ {a} {b} {c} {f = f} {g = g} {C = C}
    ((suc n) , snd₁) ((suc m) , snd₂) mt₁ mt₂  =  
    max (suc n) (suc m) , list-ap-constr {C = C}
      (mt₁ (lemma-max₁ {n = suc n} {m = suc m}) snd₁)
      (mt₂ (lemma-max₂ {n = suc n} {m = suc m}) snd₂)
  
  ------ Combinator Completeness ------

  ∥-Completeᵢ :
    ∀ {I : Set} {a b t : I → Set} {i : I} {f : Gen (a i) t i}
      {g : Gen (b i) t i} {tg : (i : I) → 𝔾 t i}
    → Completeᵢ {a = a i} f tg → Completeᵢ {a = b i} g tg
    → Completeᵢ {a = a i ⊎ b i} (⦇ inj₁ f ⦈ ∥ ⦇ inj₂ g ⦈) tg
  ∥-Completeᵢ {a = a} {b = b} {f = f} {g = g} p₁ p₂ {inj₁ x} =
    ∥ᵢ-complete-left {a = λ i → a i ⊎ b i} {f = ⦇ inj₁ f ⦈} {g = ⦇ inj₂ g ⦈}
    (constrᵢ-preserves-elem {a = a} {b = λ i → a i ⊎ b i} {g = f} p₁)
  ∥-Completeᵢ {a = a} {b = b} {f = f} {g = g} p₁ p₂ {inj₂ y} =
    ∥ᵢ-complete-right {a = λ i → a i ⊎ b i} {f = ⦇ inj₁ f ⦈} {g = ⦇ inj₂ g ⦈}
    (constrᵢ-preserves-elem {a = b} {b = λ i → a i ⊎ b i} {g = g} p₂)

  
