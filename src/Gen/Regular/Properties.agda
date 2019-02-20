{-# OPTIONS --type-in-type #-}

open import src.Gen.Base
open import src.Gen.Properties
open import src.Gen.Regular.Generic
open import src.Gen.Regular.Isomorphism
open import src.Data using (_∈_; here; Π)

open import Data.Unit hiding (_≤_)
open import Data.Product using (proj₁; proj₂; _,_; Σ; Σ-syntax)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.List

open import Function

open import Category.Monad

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

module src.Gen.Regular.Properties where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  ------ U Combinator (Unit) ------

  ugen-complete : ∀ {g : Reg} {gi : RegInfo (λ a → ⟪ 𝔾 a ⟫) g}
                  ----------------------------------------------------------
                  → Complete (deriveGen {f = U} {g = g} U~ ⟨ deriveGen gi ⟩)
  ugen-complete = 1 , here
  
  
  ------ ⊕ combinator (Coproduct) ------

  -- If 'x' is produced by a generator, 'inj₁ x' is produced by generator derived
  -- from the coproduct of that generator with any other generator
  ⊕gen-complete-left : ∀ {a : Set} {f g : Reg}
                         {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                         {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                         {x : ⟦ f ⟧ a} → g₁ ↝ x
                       --------------------------------------
                       → (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) ↝ inj₁ x
  ⊕gen-complete-left {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-left {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₁} p)
      
  
  -- If 'y' is produced by a generator, 'inj₂ y' is produced by the generator
  -- derived from the coproduct of any generator with that generator. 
  ⊕gen-complete-right : ∀ {a : Set} {f g : Reg}
                          {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                          {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                        → {y : ⟦ g ⟧ a} → g₂ ↝ y
                        -------------------------------------
                        → (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) ↝ inj₂ y
  ⊕gen-complete-right {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-right {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₂} p)

  
  -- Given that its operands are complete, the generator derived from
  -- a coproduct is complete
  ⊕gen-Complete : ∀ {a : Set} {f g : Reg}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                  → Complete g₁ → Complete g₂
                  ---------------------------------------
                  → Complete (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈)
  ⊕gen-Complete {f = f} {g = g} {g₁} {g₂} p₁ p₂ {inj₁ x} =
    ⊕gen-complete-left {f = f} {g = g} {g₁ = g₁} {g₂ = g₂} p₁
  ⊕gen-Complete {f = f} {g = g} {g₁} {g₂} p₁ p₂ {inj₂ y} =
    ⊕gen-complete-right {f = f} {g = g} {g₁ = g₁} {g₂ = g₂} p₂


  ------ ⊗ combinator (Product) ------

  -- If both operands are complete, the generator derived from a product
  -- is complete as well. 
  ⊗gen-complete : ∀ {a : Set} {f g : Reg}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                    {x : ⟦ f ⟧ a} {y : ⟦ g ⟧ a}
                  → (p₁ : g₁ ↝ x) → (p₂ : g₂ ↝ y)
                  --------------------------------------
                  → ⦇ g₁ , g₂ ⦈ ↝ (x , y)
  ⊗gen-complete {g₁ = g₁} {g₂ = g₂} p1 p2 = ⊛-complete {f = g₁} {g = g₂} p1 p2

  -- Completeness for product, but now with the quantification over arbitrary values
  -- hidden. 
  ⊗gen-Complete : ∀ {a : Set} {f g : Reg}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                  → (p₁ : Complete g₁) → (p₂ : Complete g₂)
                  -----------------------------------------------------------
                  → Complete ⦇ g₁ , g₂ ⦈
  ⊗gen-Complete {f = f} {g = g} {g₁} {g₂} p₁ p₂  =
    ⊗gen-complete {f = f} {g = g} {g₁ = g₁} {g₂ = g₂} p₁ p₂

  
  {-# TERMINATING #-}
  deriveGen-complete : ∀ {f g : Reg} {x : ⟦ f ⟧ (μ g)}
                       → (info₁ : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ] Complete ⟨ gen ⟩) f)
                       → (info₂ : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ] Complete ⟨ gen ⟩) g)
                       → (deriveGen {f = f} {g = g} (map-reginfo proj₁ info₁)
                           ⟨ deriveGen {f = g} {g = g} (map-reginfo proj₁ info₂) ⟩) ↝ x
  deriveGen-complete {U} {g} _ info₂ = ugen-complete {gi = map-reginfo proj₁ info₂}
  deriveGen-complete {f₁ ⊕ f₂} {g} (iₗ ⊕~ iᵣ) info₂ =
    ⊕gen-Complete {f = f₁} {g = f₂}
      {g₁ = deriveGen {f = f₁} {g = g} (map-reginfo proj₁ iₗ)
        ⟨ deriveGen {f = g} {g = g} (map-reginfo proj₁ info₂) ⟩}
      {g₂ = deriveGen {f = f₂} {g = g} (map-reginfo proj₁ iᵣ)
        ⟨ deriveGen {f = g} {g = g} (map-reginfo proj₁ info₂) ⟩}
      (deriveGen-complete iₗ info₂)
      (deriveGen-complete iᵣ info₂)
  deriveGen-complete {f₁ ⊗ f₂} {g} (iₗ ⊗~ iᵣ) info₂ =
    ⊗gen-Complete {f = f₁} {g = f₂}
      {g₁ = deriveGen {f = f₁} (map-reginfo proj₁ iₗ)
        ⟨ deriveGen {f = g} (map-reginfo proj₁ info₂) ⟩}
      {g₂ = deriveGen {f = f₂} (map-reginfo proj₁ iᵣ)
        ⟨ deriveGen {f = g} (map-reginfo proj₁ info₂) ⟩}
      (deriveGen-complete iₗ info₂)
      (deriveGen-complete iᵣ info₂)
  deriveGen-complete {I} {g} {x = `μ x} I~ info₂  with deriveGen-complete {f = g} {g = g} {x = x} info₂ info₂
  ... | n  , prf = suc n , (∈-rewr (sym ++-right-ident) (map-preserves-elem {f = `μ} prf))
  deriveGen-complete {K x} {g} (K~ info₁) info₂ = proj₂ info₁


  --=====================================================--
  ------ Completeness theorem for derived generators ------
  --=====================================================--
  
  deriveGen-Complete : ∀ {f : Reg}
                       → (info : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ] Complete ⟨ gen ⟩) f)
                       → Complete ⟨ deriveGen {f = f} {g = f} (map-reginfo proj₁ info) ⟩
  deriveGen-Complete {f} info {x}
    with deriveGen-complete {f = f} {g = f} {x = x} info info
  ... | n , p = suc n , p

  `μ⁻¹ : ∀ {f : Reg} → μ f → ⟦ f ⟧ (μ f)
  `μ⁻¹ (`μ x) = x

  μ-iso₂ : ∀ {f : Reg} {y : μ f} → `μ (`μ⁻¹ y) ≡ y
  μ-iso₂ {y = `μ x} = refl

  μ-iso : ∀ {f : Reg} → ⟦ f ⟧ (μ f) ≅ μ f
  μ-iso = record { from = `μ ; to = `μ⁻¹ ; iso₁ = refl ; iso₂ = μ-iso₂ }

  lemma-≅-derive : ∀ {a : Set} {f : Reg} {gen : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ (μ f)) n }
                   → (iso : a ≅ μ f) → Complete gen → Complete ⦇ (_≅_.to iso ∘ `μ) gen ⦈
  lemma-≅-derive {a} {f} {gen} iso p {x} with p {(`μ⁻¹ ∘ _≅_.from iso) x}
  ... | n , snd rewrite sym (_≅_.iso₂ (≅-transitive μ-iso (≅-symmetric iso)) {y = x}) =
    n , ++-elem-left {ys = []}
      (map-preserves-elem (∈-rewr' (_≅_.iso₁ (≅-transitive μ-iso (≅-symmetric iso))) snd))
  
  isoGen-Complete : ∀ {a : Set} ⦃ p : Regular a ⦄
                    → (info : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ] Complete ⟨ gen ⟩) (getPf p))
                    → Complete (isoGen a (map-reginfo proj₁ info))
  isoGen-Complete ⦃ p ⦄ info = lemma-≅-derive {gen = ⟨ deriveGen (map-reginfo proj₁ info) ⟩}
    (proj₂ (Regular.W p)) (deriveGen-Complete info)

  
