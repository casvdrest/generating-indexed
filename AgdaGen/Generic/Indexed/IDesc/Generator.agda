{-# OPTIONS --type-in-type #-}

open import AgdaGen.Base renaming (μ to μBase; ⟨_⟩ to ⟨_⟩Base)
open import AgdaGen.Combinators

open import AgdaGen.Generic.Isomorphism

open import AgdaGen.Generic.Indexed.IDesc.Universe
open import AgdaGen.Generic.Indexed.IDesc.Instances

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
  open GNullable    ⦃...⦄

  -- Generate selectors
  Sl-gen : ∀ {ℓ} (n : Lift ℓ ℕ) → 𝔾ᵢ {ℓ} Sl n
  Sl-gen (lift zero)    = empty
  Sl-gen (lift (suc n)) = ⦇ ▻_ (μᵢ (lift n)) ⦈
                        ∥ ⦇ ∙         ⦈

  -- Generic generator for the IDesc type
  IDesc-gen :
    ∀ {ℓ} {I : Set}
    
      -- Current description
      {δ : IDesc ℓ I}

      -- Top level description
      {φ : func ℓ I I}

      -- Selected index
    → (x : I)

      -- Metadata for the current description
    → IDescM (𝔾 {ℓ} {0ℓ}) δ

      -- Returns a generator producting values of the fixed point of
      -- the interpreted description
    → Genᵢ {ℓ} (λ ix → ⟦ δ ⟧ (μ φ)) (λ ix → ⟦ func.out φ ix ⟧ (μ φ)) x

  -- For recursive positions, simply return a recursive generator indexed with
  -- the index stored in by the `var constructor, and wrap into the μ type
  IDesc-gen {δ = `var i} {φ} x m = ⦇ ⟨ (μᵢ i) ⟩ ⦈

  -- Return a single value of type ⊤ for `1
  IDesc-gen {δ = `1} {φ} x m = ⦇ (lift tt) ⦈

  -- product (`x). Recurse on left and right subtree and combine
  -- results using product
  IDesc-gen {δ = δₗ `× δᵣ} {d₂} x (Mₗ `×~ Mᵣ) =
    ⦇ (IDesc-gen {δ = δₗ} x Mₗ ) , (IDesc-gen {δ = δᵣ} x Mᵣ ) ⦈

  -- Generalized coproduct. Recurse on selected subtree and
  -- return result in a Σ type
  IDesc-gen {ℓ} {k} {δ = `σ n T  } {φ} x (`σ~ Mₛ) =
    do sl ← Callᵢ {x = x} Sl-gen (lift n)
       r  ← IDesc-gen {δ = T sl} x (Mₛ sl) 
       pure (sl , r)

  -- Dependent pairs. Use metadata structure to generate
  -- the first element of the pair, and recurse accordingly
  -- to find the second element. 
  IDesc-gen {δ = `Σ S T} {φ} x (`Σ~ Mₚ Mₛ) =
    do sl ← Call {x = x} Mₚ
       r  ← IDesc-gen x (Mₛ sl) 
       pure (sl , r)

  
  infix 30 _⇑_

  -- Infix notation for 'Lift'
  _⇑_ : ∀ {k} → Set k → (ℓ : Level) → Set (ℓ ⊔ k)
  S ⇑ ℓ = Lift ℓ S

  -- Captures those datatypes that may be described as the fixed point of some δ ∈ IDesc
  record ≅IDesc {ℓ k} {I : Set k} (P : I → Set ℓ) : Set (sucL ℓ ⊔ sucL k) where
    field
      W : Σ[ φ ∈ func ℓ I I ] ∀ {x : I} → P x ⇑ (ℓ ⊔ k) ≅ μ φ x

  IDesc-isoGen : ∀ {ℓ} {I : Set} {P : I → Set ℓ} ⦃ p : ≅IDesc P ⦄ → (ix : I) → 𝔾ᵢ {ℓ} {0ℓ} (λ ix → P ix ⇑ ℓ) ix
  IDesc-isoGen ⦃ p = record { W = φ , iso } ⦄ ix = ⦇ (λ x → (_≅_.to iso ⟨ x ⟩)) (Callᵢ {x = ix} (λ x → IDesc-gen {δ = func.out ({!φ!}) x} {φ = φ} x {!!}) ix) ⦈ 
