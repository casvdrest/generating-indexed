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
open import Relation.Binary.HeterogeneousEquality

module AgdaGen.Generic.Indexed.IDesc.Properties where

  open GMonad ⦃...⦄

  postulate
   bind-Complete :
     ∀ {I : Set} {a t b : I → Set} {x y : I}
       {g : Genᵢ a t x} {g' : a x → Genᵢ b t y}
       {tg : (i : I) → 𝔾ᵢ t i}
     → Completeᵢ g tg → ((v : a x) → Completeᵢ (g' v) tg)
     → Completeᵢ (g >>= g') tg

  -- The selector's generator is complete
  sl-gen-Complete : ∀ {n : ℕ} → Completeᵢ (Sl-gen (lift n)) Sl-gen
  sl-gen-Complete {suc n} {∙} = 1 , here
  sl-gen-Complete {suc n} {▻ x} with sl-gen-Complete {n} {x}
  ... | depth , elem  =
    ∥ᵢ-complete-left (constrᵢ-preserves-elem ((suc depth) , elem))

  ℂ : ∀ {I : Set} {t : I → Set} → ((i : I) → 𝔾ᵢ t i) → Set
  ℂ {I} g = ∀ {i : I} → Completeᵢ (g i) g

  proofM : ∀ {ℓ} {I : Set} → func ℓ I I → Set
  proofM {I = I} φ =
    (ix : I) →
      IDescM (λ S →
        Σ[ gen ∈ 𝔾 S ]
          (Complete gen gen ×
          (∀ {s : S} → Depth-Monotone gen s gen)))
      (func.out φ ix)
      
  proj₁' :
    ∀ {S : Set}
    → Σ[ gen ∈ 𝔾 S ]
        (Complete gen gen ×
        (∀ {s : S} → Depth-Monotone gen s gen))
    → 𝔾 S
  proj₁' (x , _) = x

  fix-lemma :
    ∀ {I : Set} {t : I → Set} {i : I}
      {g : (i : I) → 𝔾ᵢ t i} {n : ℕ}
    → interpretᵢ g i (g i) n ≡ interpretᵢ g i (μᵢ i) (suc n)
  fix-lemma {n = zero} = refl
  fix-lemma {n = suc n} = refl

  splitφ : ∀ {I} → (φ : func 0ℓ I I) → (i : I) → Σ[ δ ∈ IDesc 0ℓ I ] func.out φ i ≡ δ
  splitφ φ i = (func.out φ i) , refl

  data Cb (a b : Set) : Set where
    comb : a → b → Cb a b

  IDesc-gen-Complete :
    ∀ {I : Set} {ix : I} {φ₁ φ₂  : func 0ℓ I I}
      {x : ⟦ φ₁ ⟧func (μ φ₂) ix}
    → (m₁ : IDescM (λ S →
      Σ[ gen ∈ 𝔾 S ]
         (Complete gen gen ×
           (∀ {s : S} → Depth-Monotone gen s gen))) (func.out φ₁ ix))
    → (m₂ : (i : I) →
      IDescM (λ S →
             Σ[ gen ∈ 𝔾 S ]
      (Complete gen gen ×
        (∀ {s : S} → Depth-Monotone gen s gen)))
        (func.out φ₂ i))
    → Σ ℕ (λ n → x ∈ interpretᵢ (λ y → IDesc-gen {φ₁ = φ₂} y (mapm proj₁ (m₂ y))) ix (IDesc-gen {φ₁ = φ₁} ix (mapm proj₁ m₁)) n)
  IDesc-gen-Complete {ix = ix} {φ₁ = φ₁} {φ₂ = φ₂} {x} m₁ m₂ with comb (func.out φ₁ ix) x
  IDesc-gen-Complete {ix = ix} {φ₁} {φ₂} {x} m₁ m₂ | comb (`var i) x₂ = {!!}
  IDesc-gen-Complete {ix = ix} {φ₁} {φ₂} {x} m₁ m₂ | comb `1 x₂ = {!!}
  IDesc-gen-Complete {ix = ix} {φ₁} {φ₂} {x} m₁ m₂ | comb (x₁ `× x₃) x₂ = {!!}
  IDesc-gen-Complete {ix = ix} {φ₁} {φ₂} {x} m₁ m₂ | comb (`σ n T) x₂ = {!!}
  IDesc-gen-Complete {ix = ix} {φ₁} {φ₂} {x} m₁ m₂ | comb (`Σ S T) x₂ = {!!}
