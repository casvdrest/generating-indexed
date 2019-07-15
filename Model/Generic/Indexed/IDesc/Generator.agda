{-# OPTIONS --type-in-type #-}

open import Model.Base renaming (μ to μBase)
open import Model.Combinators

open import Model.Generic.Isomorphism

open import Model.Generic.Indexed.IDesc.Universe

open import Data.Unit
open import Data.Product
open import Data.Nat hiding (_⊔_)

open import Level renaming (suc to sucL ; zero to zeroL)

open import Relation.Binary.PropositionalEquality

open import Function

module Model.Generic.Indexed.IDesc.Generator where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
  open GMonad       ⦃...⦄

  -- Generate selectors
  Sl-gen : ∀ {ℓ} (n : Lift ℓ ℕ) → 𝔾 {ℓ} Sl n
  Sl-gen (lift zero)    = empty 
  Sl-gen (lift (suc n)) = ⦇ ▻_ (μBase (lift n)) ⦈
                        ∥ ⦇ ∙                    ⦈

  ⟦⟧subst :
    ∀ {ℓ} {I : Set} {φ φ' : func ℓ I I} {δ : IDesc ℓ I} {ix : I}
    → func.out φ ix ≡ δ →  ⟦ δ ⟧ (μ φ') → ⟦ func.out φ ix ⟧ (μ φ')
  ⟦⟧subst p rewrite p = λ x → x

  -- Generic generator for the IDesc type
  IDesc-gen :
    ∀ {ℓ} {I : Set}
    
      -- Current description
      {δ : IDesc ℓ I}

      -- Top level description
      {φ : func ℓ I I}

      -- Selected index
    → (ix : I)

      -- Metadata for the current description
    → IDescM (λ S → 𝔾 {ℓ} {0ℓ} (λ _ → S) tt) δ

      -- Returns a generator producting values of the fixed point of
      -- the interpreted description
    → Gen {ℓ} (⟦ δ ⟧ (μ φ)) (λ x → ⟦ func.out φ x ⟧ (μ φ)) ix

  IDesc-gen {ℓ} {I} {`var i} {φ} ix `var~ = ⦇ ⟨ (μBase i) ⟩ ⦈
  IDesc-gen {ℓ} {I} {`1} {φ} ix `1~ = ⦇ (lift tt) ⦈
  IDesc-gen {ℓ} {I} {δₗ `× δᵣ} {φ} ix (mₗ `×~ mᵣ) =
    ⦇ (IDesc-gen ix mₗ) , (IDesc-gen ix mᵣ) ⦈
  IDesc-gen {ℓ} {I} {`σ n T} {φ} ix (`σ~ mT) =
    _>>=_ {i = I} {x = ix} {y = ix} (Call (lift n) (λ n' → Sl-gen n'))
      (λ sl → ⦇ (λ x → (sl , x)) (IDesc-gen ix (mT sl)) ⦈)
  IDesc-gen {ℓ} {I} {`Σ S T} {φ} ix (`Σ~ gS mT) =
    _>>=_ (Call {x = ix} tt (λ _ → gS)) λ s → ⦇ (λ x → s , x) (IDesc-gen ix (mT s)) ⦈
  
  infix 30 _⇑_

  -- Infix notation for 'Lift'
  _⇑_ : ∀ {k} → Set k → (ℓ : Level) → Set (ℓ ⊔ k)
  S ⇑ ℓ = Lift ℓ S

  -- Captures those datatypes that may be described as the fixed point of some φ ∈ func
  record ≅IDesc {ℓ k} {I : Set k} (P : I → Set ℓ) : Set (sucL ℓ ⊔ sucL k) where
    field
      W : Σ[ φ ∈ func ℓ I I ] ((ix : I) → P ix ⇑ (ℓ ⊔ k) ≅ μ φ ix)

  -- Extract the description from an isomorphism
  getφ : ∀ {ℓ} {I : Set} {P : I → Set ℓ} → ≅IDesc P → func ℓ I I
  getφ record { W = φ , iso } = φ

  -- Derive a generator for indexed datatypes based on an isomorphism with some description
  IDesc-isoGen :
    ∀ {ℓ} {I : Set} {P : I → Set ℓ} ⦃ p : ≅IDesc P ⦄
    → (ix : I)
    → ((y : I) → IDescM (λ S → 𝔾 (λ _ → S) tt) (func.out (getφ p) y))
    → 𝔾 {ℓ} {0ℓ} (λ x → P x ⇑ ℓ) ix
  IDesc-isoGen {I = I} {δ} ⦃ p = record { W = φ , iso } ⦄ ix m
    = _>>=_ {y = ix}
      (Call ix (λ y → IDesc-gen {δ = func.out φ y} {φ = φ} y (m y)))
      (λ r → pure (_≅_.to (iso ix) ⟨ r ⟩))
  
