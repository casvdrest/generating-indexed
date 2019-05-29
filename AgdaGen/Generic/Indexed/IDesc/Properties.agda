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

  open GMonad ⦃...⦄

  postulate
   bind-Complete :
     ∀ {I : Set} {a b : Set} {t : I → Set} {x y : I}
       {g : Genᵢ a t x} {g' : a → Genᵢ b t y}
       {tg : (i : I) → 𝔾ᵢ t i}
     → Completeᵢ {a = a} g tg
     → ((v' : a) → Completeᵢ {a = b} (g' v') tg)
     → Completeᵢ (g >>= g') tg

  -- The selector's generator is complete
  sl-gen-Complete : ∀ {n : ℕ} → Completeᵢ {a = Sl (lift n) } (Sl-gen (lift n)) Sl-gen
  sl-gen-Complete {zero} {()}
  sl-gen-Complete {suc n} {∙} = 1 , here
  sl-gen-Complete {suc n} {▻ x} with sl-gen-Complete {n} {x}
  sl-gen-Complete {suc n} {▻ x} | n' , elem =
    ∥ᵢ-complete-left {a = Sl} (constrᵢ-preserves-elem {a = Sl} {b = Sl} (suc n' , elem))

  ℂ : ∀ {I : Set} {t : I → Set} → ((i : I) → 𝔾ᵢ t i) → Set
  ℂ {I} {t} g = ∀ {i : I} → Completeᵢ {a = t i} (g i) g

  callᵢ-Complete :
    ∀ {I J : Set} {a : J → Set} {t : I → Set}
      {g : (j : J) → Genᵢ (a j) a j} {i : I}
      {tg : (i : I) → Genᵢ (t i) t i} {j : J}
    → Completeᵢ (g j) g
    → Completeᵢ {a = a j} {i = i} (Callᵢ j g) tg

  call-Complete :
    ∀ {a : Set} {I : Set} {t : I → Set} {g : Gen a a}
      {tg : (i : I) → Genᵢ (t i) t i} {i : I}
    → Complete g g
    → Completeᵢ {a = a} {i = i} (Call g) tg

  IDesc-gen-Complete :
    ∀ {I : Set} {ix : I} {δ : IDesc 0ℓ I} {φ  : func 0ℓ I I}
      {x : ⟦ δ ⟧ (μ φ)}
    → (m₁ : IDescM (λ S →
      Σ[ gen ∈ 𝔾 S ]
         (Complete gen gen ×
           (∀ {s : S} → Depth-Monotone gen s gen))) δ) 
    → (m₂ : (i : I) →
      IDescM (λ S →
             Σ[ gen ∈ 𝔾 S ]
      (Complete gen gen ×
        (∀ {s : S} → Depth-Monotone gen s gen)))
        (func.out φ i))
    → Σ ℕ (λ n → x ∈ interpretᵢ (λ y → IDesc-gen y (mapm proj₁ (m₂ y))) ix (IDesc-gen ix (mapm proj₁ m₁)) n)
  IDesc-gen-Complete {δ = `var i} {φ} {⟨ x ⟩} m₁ m₂
    with IDesc-gen-Complete {ix = i} {δ = func.out φ i} {φ = φ} {x = x} (m₂ i) m₂
  IDesc-gen-Complete {ix = _} {`var i} {φ} {⟨ x ⟩} m₁ m₂ | zero , ()
  IDesc-gen-Complete {ix = _} {`var i} {φ} {⟨ x ⟩} m₁ m₂ | suc fst , snd =
    constrᵢ-preserves-elem {a = λ y → ⟦ func.out φ y ⟧ (μ φ)} (suc (suc fst) , snd)
  IDesc-gen-Complete {δ = `1} {φ} {lift tt} `1~ m₂ = 1 , here
  IDesc-gen-Complete {δ = δₗ `× δᵣ} {φ} {x} (mₗ `×~ mᵣ) m₂ = {!!}
  IDesc-gen-Complete {δ = `σ n T} {φ} {x} (`σ~ x₁) m₂ =
    bind-Complete (callᵢ-Complete sl-gen-Complete) λ sl → {!!}
  IDesc-gen-Complete {δ = `Σ S T} {φ} {x} (`Σ~ (g , (cmp , mt)) x₂) m₂ =
    bind-Complete (call-Complete cmp) λ s → {!!}

