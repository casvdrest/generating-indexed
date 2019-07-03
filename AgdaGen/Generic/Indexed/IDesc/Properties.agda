{-# OPTIONS --type-in-type #-}

open import AgdaGen.Data using (here ; there ; _∈_)
open import AgdaGen.Base hiding (μ)
open import AgdaGen.Combinators
open import AgdaGen.Properties.General
open import AgdaGen.Properties.Completeness
open import AgdaGen.Properties.Monotonicity
open import AgdaGen.Generic.Indexed.IDesc.Generator
open import AgdaGen.Generic.Indexed.IDesc.Universe

open import AgdaGen.Enumerate hiding (⟨_⟩)

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Unit

open import Function
open import Level renaming (zero to zeroL; suc to sucL)

open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary.HeterogeneousEquality

module AgdaGen.Generic.Indexed.IDesc.Properties where

  open GApplicative ⦃...⦄
  open GMonad ⦃...⦄

  postulate
    Σ-bind-Complete :
      ∀ {I : Set} {a : Set} {b : a → Set} {t : I → Set} {x y : I}
        {g : Gen a t x} {g' : (v : a) → Gen (b v) t y}
        {x : Σ a b} {tg : (i : I) → 𝔾 t i}
      → g ∣ᵢ tg ↝ proj₁ x
      → g' (proj₁ x) ∣ᵢ tg ↝ proj₂ x
      → _∣ᵢ_↝_ {i = y} (g >>= λ y → ⦇ (λ v → y , v) (g' y) ⦈) tg x

  -- The selector's generator is complete
  sl-gen-Complete : ∀ {n : ℕ} → Completeᵢ {a = Sl (lift n) } (Sl-gen (lift n)) Sl-gen
  sl-gen-Complete {zero} {()}
  sl-gen-Complete {suc n} {∙} = 1 , here
  sl-gen-Complete {suc n} {▻ x} with sl-gen-Complete {n} {x}
  sl-gen-Complete {suc n} {▻ x} | n' , elem =
    ∥ᵢ-complete-left {a = Sl} (constrᵢ-preserves-elem {a = Sl} {b = Sl} (suc n' , elem))

  ℂ : ∀ {I : Set} {t : I → Set} → ((i : I) → 𝔾 t i) → Set
  ℂ {I} {t} g = ∀ {i : I} → Completeᵢ {a = t i} (g i) g

  callᵢ-Complete :
    ∀ {I J : Set} {a : J → Set} {t : I → Set}
      {g : (j : J) → Gen (a j) a j} {i : I}
      {tg : (i : I) → Gen (t i) t i} {j : J}
    → Completeᵢ (g j) g
    → Completeᵢ {a = a j} {i = i} (Call j g) tg
  callᵢ-Complete p {x} with p {x}
  callᵢ-Complete p {x} | suc n , elem = suc n , elem

  call-Complete :
    ∀ {a : Set} {I : Set} {t : I → Set} {g : Gen a (λ _ → a) tt}
      {tg : (i : I) → Gen (t i) t i} {i : I}
    → Completeᵢ g (λ _ → g)
    → Completeᵢ {a = a} {i = i} (Call tt (λ _ → g)) tg
  call-Complete p {x} with p {x}
  call-Complete p {x} | suc n , elem = suc n , elem

  IDesc-gen-Complete :
    ∀ {I : Set} {ix : I} {δ : IDesc 0ℓ I} {φ  : func 0ℓ I I}
      {x : ⟦ δ ⟧ (μ φ)}
    → (m₁ : IDescM (λ S →
      Σ[ gen ∈ 𝔾 (λ _ → S) tt ]
         (Completeᵢ gen (λ _ → gen) ×
           (∀ {s : S} → Depth-Monotoneᵢ gen (λ _ → gen) s))) δ) 
    → (m₂ : (i : I) →
      IDescM (λ S →
             Σ[ gen ∈ 𝔾 (λ _ → S) tt ]
      (Completeᵢ gen (λ _ → gen) ×
        (∀ {s : S} → Depth-Monotoneᵢ gen (λ _ → gen) s)))
        (func.out φ i))
    → Σ ℕ (λ n → x ∈ enumerate (λ y → IDesc-gen y (mapm proj₁ (m₂ y))) ix (IDesc-gen ix (mapm proj₁ m₁)) n)
  IDesc-gen-Complete {δ = `var i} {φ} {⟨ x ⟩} m₁ m₂
    with IDesc-gen-Complete {ix = i} {δ = func.out φ i} {φ = φ} {x = x} (m₂ i) m₂
  IDesc-gen-Complete {ix = _} {`var i} {φ} {⟨ x ⟩} m₁ m₂ | zero , ()
  IDesc-gen-Complete {ix = _} {`var i} {φ} {⟨ x ⟩} `var~ m₂ | suc fst , snd =
    constrᵢ-preserves-elem {a = λ y → ⟦ func.out φ y ⟧ (μ φ)} ((suc (suc fst)) , snd) 
  IDesc-gen-Complete {δ = `1} {φ} {lift tt} `1~ m₂ = 1 , here
  IDesc-gen-Complete {δ = δₗ `× δᵣ} {φ} {x} (mₗ `×~ mᵣ) m₂ = {!!}
  IDesc-gen-Complete {δ = `σ n T} {φ} {sl , x} (`σ~ mT) m₂ =
    Σ-bind-Complete (callᵢ-Complete sl-gen-Complete) (IDesc-gen-Complete {δ = T sl} (mT sl) m₂)
  IDesc-gen-Complete {δ = `Σ S T} {φ} {s , x} (`Σ~ (g , (cmp , mt)) x₂) m₂ =
    Σ-bind-Complete (call-Complete cmp) (IDesc-gen-Complete (x₂ s) m₂)

