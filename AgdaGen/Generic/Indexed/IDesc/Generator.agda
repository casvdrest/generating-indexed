{-# OPTIONS --type-in-type #-}

open import AgdaGen.Base renaming (μ to μBase)
open import AgdaGen.Combinators

open import AgdaGen.Generic.Isomorphism

open import AgdaGen.Generic.Indexed.IDesc.Universe

open import Data.Unit
open import Data.Product
open import Data.Nat hiding (_⊔_)

open import Level renaming (suc to sucL ; zero to zeroL)

open import Relation.Binary.PropositionalEquality

open import Function

module AgdaGen.Generic.Indexed.IDesc.Generator where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
  open GMonad       ⦃...⦄

  -- Generate selectors
  Sl-gen : ∀ {ℓ} (n : Lift ℓ ℕ) → 𝔾ᵢ {ℓ} Sl n
  Sl-gen (lift zero)    = empty
  Sl-gen (lift (suc n)) = ⦇ ▻_ (μᵢ (lift n)) ⦈
                        ∥ ⦇ ∙         ⦈

  ⟦⟧subst :
    ∀ {ℓ} {I : Set} {φ φ' : func ℓ I I} {δ : IDesc ℓ I} {ix : I}
    → func.out φ ix ≡ δ →  ⟦ δ ⟧ (μ φ') → ⟦ func.out φ ix ⟧ (μ φ')
  ⟦⟧subst p rewrite p = λ x → x

  -- Generic generator for the IDesc type
  IDesc-gen :
    ∀ {ℓ} {I : Set}
    
      -- Current description
      {φ₁ : func ℓ I I}

      -- Top level description
      {φ₂ : func ℓ I I}

      -- Selected index
    → (ix : I)

      -- Metadata for the current description
    → IDescM (𝔾 {ℓ} {0ℓ}) (func.out φ₁ ix)

      -- Returns a generator producting values of the fixed point of
      -- the interpreted description
    → Genᵢ {ℓ} (λ x → ⟦ func.out φ₁ x ⟧ (μ φ₂)) (λ x → ⟦ func.out φ₂ x ⟧ (μ φ₂)) ix

  -- `var combinator (recursive positions)
  IDesc-gen {ℓ} {I} {φ₁} {φ₂} ix m with func.out φ₁ ix | inspect (func.out φ₁) ix
  IDesc-gen {ℓ} {I} {φ₁} {φ₂} ix `var~ | `var i | [ φout≡`var ] =
    ⦇ (λ x → ⟦⟧subst {φ = φ₁} {φ' = φ₂} φout≡`var ⟨ x ⟩) (μᵢ i) ⦈
  -- `1 combinator (unit)
  IDesc-gen {ℓ} {I} {φ₁} {φ₂} ix `1~ | `1     | [ φout≡`1 ] =
    ⦇ (⟦⟧subst {φ = φ₁} {φ' = φ₂} {ix = ix} φout≡`1 (lift tt)) ⦈
  -- `× combinator (product)
  IDesc-gen {ℓ} {I} {φ₁} {φ₂} ix (m₁ `×~ m₂) | δ₁ `× δ₂ | [ φout≡`× ] =
    ⦇ (λ l r → ⟦⟧subst {φ = φ₁} {ix = ix}  φout≡`× (l , r))
      (IDesc-gen ix m₁) (IDesc-gen ix m₂) ⦈
  -- `σ combinator (generic coproduct)
  IDesc-gen {ℓ} {I} {φ₁} {φ₂} ix (`σ~ mₛ) | `σ n T | [ φout≡`σ ] =
    do sl ← Callᵢ {x = ix} Sl-gen (lift n)
       r  ← IDesc-gen ix (mₛ sl)
       pure (⟦⟧subst {φ = φ₁} {ix = ix} φout≡`σ (sl , r))
  -- `Σ combinator (dependent pairs)
  IDesc-gen {ℓ} {I} {φ₁} {φ₂} ix (`Σ~ mₛ mₜ) | `Σ S T | [ φout≡`Σ ] =
    do sl ← Call {x = ix} mₛ
       r  ← IDesc-gen ix (mₜ sl) 
       pure (⟦⟧subst {φ = φ₁} {ix = ix} φout≡`Σ (sl , r))
       
  infix 30 _⇑_

  -- Infix notation for 'Lift'
  _⇑_ : ∀ {k} → Set k → (ℓ : Level) → Set (ℓ ⊔ k)
  S ⇑ ℓ = Lift ℓ S

  -- Captures those datatypes that may be described as the fixed point of some φ ∈ func
  record ≅IDesc {ℓ k} {I : Set k} (P : I → Set ℓ) : Set (sucL ℓ ⊔ sucL k) where
    field
      W : Σ[ φ ∈ func ℓ I I ] ∀ {x : I} → P x ⇑ (ℓ ⊔ k) ≅ μ φ x

  -- Extract the description from an isomorphism
  getφ : ∀ {ℓ} {I : Set} {P : I → Set ℓ} → ≅IDesc P → func ℓ I I
  getφ record { W = φ , iso } = φ

  -- Derive a generator for indexed datatypes based on an isomorphism with some description
  IDesc-isoGen :
    ∀ {ℓ} {I : Set} {P : I → Set ℓ} ⦃ p : ≅IDesc P ⦄
    → (ix : I) → ((ix : I) → IDescM 𝔾 (func.out (getφ p) ix))
    → 𝔾ᵢ {ℓ} {0ℓ} (λ x → P x ⇑ ℓ) ix
  IDesc-isoGen {I = I} ⦃ p = record { W = φ , iso  } ⦄ ix m =
    ⦇ (λ v → _≅_.to iso ⟨ v ⟩) (Callᵢ {j = I} {x = ix}
      (λ y → IDesc-gen {φ₁ = φ} {φ₂ = φ} y (m y)) ix) ⦈
