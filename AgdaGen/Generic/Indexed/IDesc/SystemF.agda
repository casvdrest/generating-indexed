{-# OPTIONS --type-in-type #-}

open import Data.Nat
open import Data.Char
open import Data.List
open import Data.Product
open import Data.Unit

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Level

open import AgdaGen.Generic.Isomorphism

open import AgdaGen.Generic.Indexed.IDesc.Universe
open import AgdaGen.Generic.Indexed.IDesc.Generator

module AgdaGen.Generic.Indexed.IDesc.SystemF where

  Id : Set
  Id = ℕ

  data λ2 : Set where
    `_   : Id → λ2
    _·_  : λ2 → λ2 → λ2
    ƛ_⇒_ : Id → λ2 → λ2

  data 𝕋 : Set where
    ``_  : Id → 𝕋
    _`→_ : 𝕋 → 𝕋 → 𝕋
    `∀_·_  : Id → 𝕋 → 𝕋
 
  data Ctx : Set where
    ∅ : Ctx
    _,_∶_ : Ctx → Id → 𝕋 → Ctx

  data _∋_ : Ctx → 𝕋 → Set where
  
    [Top] : ∀ {Γ τ α}
          -----------------
          → (Γ , α ∶ τ) ∋ τ
    
    [Pop] : ∀ {Γ σ τ β} → Γ ∋ τ
          ---------------------
          → (Γ , β ∶ σ) ∋ τ

  data _∌ₜ_ : 𝕋 → Id → Set where

   [∌ₜ-var] : ∀ {α β} → ¬ α ≡ β
            ---------------------
            → (`` β) ∌ₜ α

   [∌ₜ-fty] : ∀ {α τ₁ τ₂} → τ₁ ∌ₜ α → τ₂ ∌ₜ α
            ---------------------------------
            → (τ₁ `→ τ₂) ∌ₜ α

   [∌ₜ-∀¬≡] : ∀ {α β τ} → ¬ α ≡ β
            ---------------------
            → (`∀ β · τ) ∌ₜ α

   [∌ₜ-∀≡]  : ∀ {α τ}
            -----------------
            → (`∀ α · τ) ∌ₜ α    
    

  data _∌_ : Ctx → Id → Set where
  
    [∌₁] : ∀ {α}
         -------
         → ∅ ∌ α
    
    [∌₂] : ∀ {Γ α x τ} → Γ ∌ α → τ ∌ₜ α
         ------------------------------
         → (Γ , x ∶ τ) ∌ α 

  data _[_:=_]→_ : 𝕋 → Id → 𝕋 → 𝕋 → Set where
  
    [sub-var] : ∀ {β τ}
              ----------------------
              → (`` β) [ β := τ ]→ τ
    
    [sub-fty] : ∀ {α σ₁ σ₂ τ τ₁ τ₂} → σ₁ [ α := τ ]→ τ₁ → σ₂ [ α := τ ]→ τ₂
              -------------------------------------------------------------
              → (σ₁ `→ σ₂) [ α := τ ]→ (τ₁ `→ τ₂)
              
    [sub-all] : ∀ {α β σ τ τ'} → ¬ α ≡ β → σ [ α := τ ]→ τ'
              ---------------------------------------------
              → (`∀ β · σ) [ α := τ ]→ τ'

  infix 10 _⊢_
  infix 15 _,_∶_

  data _⊢_ : Ctx → 𝕋 → Set where

    [λ2-var] : ∀ {Γ σ} → Γ ∋ σ
             -----------------
             → Γ ⊢ σ

    [λ2-app] : ∀ {Γ σ τ} → Γ ⊢ (σ `→ τ) → Γ ⊢ σ
             ----------------------------------
             → Γ ⊢  τ

    [λ2-abs] : ∀ {Γ x σ τ} → (Γ , x ∶ σ) ⊢ τ
             -------------------------------
             → Γ ⊢ (σ `→ τ)

    [λ2-∀₁]  : ∀ {Γ α σ τ τ'} → Γ ⊢ (`∀ α · σ) → σ [ α := τ ]→ τ' 
             ----------------------------------------------------
             → Γ ⊢ τ'

    [λ2-∀₂]  : ∀ {Γ α σ} → Γ ⊢ σ → Γ ∌ α 
             ---------------------------
             → Γ ⊢ ( `∀ α · σ)


  λ2D : func 0ℓ (Ctx × 𝕋) (Ctx × 𝕋)
  λ2D = func.mk λ
    { (Γ , (`` α)) → `σ 3
        λ { ∙       → λ2-var-desc Γ (`` α)
          ; (▻ ∙)   → λ2-app-desc Γ (`` α)
          ; (▻ ▻ ∙) → λ2-∀₁-desc  Γ (`` α) 
          } 
    ; (Γ , (τ₁ `→ τ₂)) → `σ 4
        λ { ∙         → λ2-var-desc Γ (τ₁ `→ τ₂)
          ; (▻ ∙)     → λ2-app-desc Γ (τ₁ `→ τ₂) 
          ; (▻ ▻ ∙)   → λ2-abs-desc Γ τ₁ τ₂
          ; (▻ ▻ ▻ ∙) → λ2-∀₁-desc Γ (τ₁ `→ τ₂)
          } 
    ; (Γ , (`∀ α · τ)) → `σ 4
        λ { ∙         → λ2-var-desc Γ (`∀ α · τ)
          ; (▻ ∙)     → λ2-app-desc Γ (`∀ α · τ)
          ; (▻ ▻ ∙)   → λ2-∀₁-desc Γ (`∀ α · τ)
          ; (▻ ▻ ▻ ∙) → λ2-∀₂-desc Γ α τ 
          }
    } where -- [λ2-var]
            λ2-var-desc : Ctx → 𝕋 → IDesc 0ℓ (Ctx × 𝕋)
            λ2-var-desc Γ τ = `Σ (Γ ∋ τ) λ _ → `1

            -- [λ2-app]
            λ2-app-desc : Ctx → 𝕋 → IDesc 0ℓ (Ctx × 𝕋)
            λ2-app-desc Γ τ = `Σ 𝕋 λ σ → `var (Γ , (σ `→ τ)) `× `var (Γ , σ)

            -- [λ2-abs]
            λ2-abs-desc : Ctx → 𝕋 → 𝕋 → IDesc 0ℓ (Ctx × 𝕋)
            λ2-abs-desc Γ σ τ = `Σ Id (λ x → `var ((Γ , x ∶ σ) , τ))

            -- [λ2-∀₁]
            λ2-∀₁-desc  : Ctx → 𝕋 → IDesc 0ℓ (Ctx × 𝕋)
            λ2-∀₁-desc Γ τ' = `Σ (Σ (Id × 𝕋 × 𝕋) λ { (α , σ , τ) → σ [ α := τ ]→ τ' })
              λ { ( (α , σ , _) , _) → `var (Γ , `∀ α · σ) }

            -- [λ2-∀₂]
            λ2-∀₂-desc  : Ctx → Id → 𝕋 → IDesc 0ℓ (Ctx × 𝕋)
            λ2-∀₂-desc Γ α σ = `Σ (Γ ∌ α) (λ _ → `var (Γ , σ))

  from⊢ : ∀ {Γ τ} → Γ ⊢ τ → μ λ2D (Γ , τ)
  from⊢ {Γ} {`` x} ([λ2-var] x₁) =
    ⟨ (∙ , x₁ , lift tt) ⟩
  from⊢ {Γ} {`` x} ([λ2-app] {σ = σ} p p₁) =
    ⟨ ((▻ ∙) , σ , from⊢ p , from⊢ p₁) ⟩
  from⊢ {Γ} {`` x} ([λ2-∀₁] {α = α} {σ = σ} {τ = τ}  p x₁) =
    ⟨ ((▻ ▻ ∙) , ((α , σ , τ) , x₁) , from⊢ p) ⟩
  from⊢ {Γ} {τ `→ τ₁} ([λ2-var] x) =
    ⟨ ∙ , (x , lift tt) ⟩
  from⊢ {Γ} {τ `→ τ₁} ([λ2-app] {σ = σ} p p₁) =
    ⟨ (▻ ∙ , σ , from⊢ p , from⊢ p₁) ⟩
  from⊢ {Γ} {τ `→ τ₁} ([λ2-abs] {x = x} p) = ⟨ ((▻ ▻ ∙) , (x , from⊢ p)) ⟩
  from⊢ {Γ} {τ₁ `→ τ₂} ([λ2-∀₁] {α = α} {σ = σ} {τ = τ} p x) =
    ⟨ ((▻ ▻ ▻ ∙) , ((α , σ , τ) , x) , from⊢ p) ⟩
  from⊢ {Γ} {`∀ x · τ} ([λ2-var] x₁) =
    ⟨ (∙ , (x₁ , lift tt)) ⟩
  from⊢ {Γ} {`∀ x · τ} ([λ2-app] {σ = σ} p p₁) =
    ⟨ ((▻ ∙) , (σ , from⊢ p , from⊢ p₁)) ⟩
  from⊢ {Γ} {`∀ x · τ'} ([λ2-∀₁] {α = α} {σ = σ} {τ = τ} p x₁) =
    ⟨ ((▻ ▻ ∙) , ((α , σ , τ) , x₁) , from⊢ p) ⟩
  from⊢ {Γ} {`∀ x · τ} ([λ2-∀₂] p x₁) =
    ⟨ ((▻ ▻ ▻ ∙) , (x₁ , from⊢ p)) ⟩

  to⊢ : ∀ {Γ τ} → μ λ2D (Γ , τ) → Γ ⊢ τ
  to⊢ {Γ} {`` x} ⟨ ∙ , fst , snd ⟩ =
    [λ2-var] fst
  to⊢ {Γ} {`` x} ⟨ ▻ ∙ , fst , fst₁ , snd ⟩ =
    [λ2-app] {σ = fst} (to⊢ fst₁) (to⊢ snd)
  to⊢ {Γ} {`` x} ⟨ ▻ ▻ ∙ , ((α , σ , τ) , snd) , snd₁ ⟩ =
    [λ2-∀₁] {α = α} {σ = σ} {τ = τ} (to⊢ snd₁) snd
  to⊢ {Γ} {τ `→ τ₁} ⟨ ∙ , fst , snd ⟩ =
    [λ2-var] fst
  to⊢ {Γ} {τ `→ τ₁} ⟨ ▻ ∙ , fst , fst₁ , snd ⟩ =
    [λ2-app] {σ = fst} (to⊢ fst₁) (to⊢ snd)
  to⊢ {Γ} {τ `→ τ₁} ⟨ ▻ ▻ ∙ , fst , snd ⟩ =
    [λ2-abs] {x = fst} (to⊢ snd)
  to⊢ {Γ} {τ₁ `→ τ₂} ⟨ ▻ ▻ ▻ ∙ , ((α , σ , τ) , snd) , snd₁ ⟩ =
    [λ2-∀₁] {α = α} {σ = σ} {τ = τ} (to⊢ snd₁) snd
  to⊢ {Γ} {`∀ x · τ} ⟨ ∙ , fst , snd ⟩ =
    [λ2-var] fst
  to⊢ {Γ} {`∀ x · τ} ⟨ ▻ ∙ , fst , fst₁ , snd ⟩ =
    [λ2-app] {σ = fst} (to⊢ fst₁) (to⊢ snd) 
  to⊢ {Γ} {`∀ x · τ'} ⟨ ▻ ▻ ∙ , ((α , σ , τ) , snd) , snd₁ ⟩ =
    [λ2-∀₁] {α = α} {σ = σ} {τ = τ} (to⊢ snd₁) snd
  to⊢ {Γ} {`∀ x · τ} ⟨ ▻ ▻ ▻ ∙ , fst , snd ⟩ =
    [λ2-∀₂] (to⊢ snd) fst

  ⊢-iso₁ : ∀ {Γ τ} {p : Γ ⊢ τ} → to⊢ (from⊢ p) ≡ p
  ⊢-iso₁ {Γ} {`` x} {[λ2-var] x₁} = refl
  ⊢-iso₁ {Γ} {`` x} {[λ2-app] p₁ p₂} =
    cong₂ [λ2-app] ⊢-iso₁ ⊢-iso₁
  ⊢-iso₁ {Γ} {`` x} {[λ2-∀₁] p x₁} =
    cong (λ p → [λ2-∀₁] p x₁) ⊢-iso₁
  ⊢-iso₁ {Γ} {τ `→ τ₁} {[λ2-var] x} = refl
  ⊢-iso₁ {Γ} {τ `→ τ₁} {[λ2-app] p p₁} =
    cong₂ [λ2-app] ⊢-iso₁ ⊢-iso₁
  ⊢-iso₁ {Γ} {τ `→ τ₁} {[λ2-abs] p} =
    cong [λ2-abs] ⊢-iso₁
  ⊢-iso₁ {Γ} {τ `→ τ₁} {[λ2-∀₁] p x} =
    cong (λ p → [λ2-∀₁] p x) ⊢-iso₁
  ⊢-iso₁ {Γ} {`∀ x · τ} {[λ2-var] x₁} = refl
  ⊢-iso₁ {Γ} {`∀ x · τ} {[λ2-app] p p₁} =
    cong₂ [λ2-app] ⊢-iso₁ ⊢-iso₁
  ⊢-iso₁ {Γ} {`∀ x · τ} {[λ2-∀₁] p x₁} =
    cong (λ p → [λ2-∀₁] p x₁) ⊢-iso₁
  ⊢-iso₁ {Γ} {`∀ x · τ} {[λ2-∀₂] p x₁} =
    cong (λ p → [λ2-∀₂] p x₁) ⊢-iso₁

  ⊢-iso₂ : ∀ {Γ τ} {p : μ λ2D (Γ , τ)} → from⊢ (to⊢ p ) ≡ p
  ⊢-iso₂ {Γ} {`` x} {⟨ ∙ , fst , lift tt ⟩} = refl
  ⊢-iso₂ {Γ} {`` x} {⟨ ▻ ∙ , (σ , l , r) ⟩} =
    cong₂ (λ x y → ⟨ ((▻ ∙) , σ , x , y) ⟩) ⊢-iso₂ ⊢-iso₂
  ⊢-iso₂ {Γ} {`` x} {⟨ ▻ ▻ ∙ , ((α , σ , τ) , snd) , snd₁ ⟩} =
    cong (λ x → ⟨ ((▻ ▻ ∙) , ((α , σ , τ) , snd) , x) ⟩) ⊢-iso₂
  ⊢-iso₂ {Γ} {τ `→ τ₁} {⟨ ∙ , fst , lift tt ⟩} = refl
  ⊢-iso₂ {Γ} {τ `→ τ₁} {⟨ ▻ ∙ , σ , fst₁ , snd ⟩} =
    cong₂ (λ x y → ⟨ ((▻ ∙) , (σ , x , y)) ⟩) ⊢-iso₂ ⊢-iso₂
  ⊢-iso₂ {Γ} {τ `→ τ₁} {⟨ ▻ ▻ ∙ , fst , snd ⟩} =
    cong (λ x → ⟨ (▻ ▻ ∙ , fst , x) ⟩) ⊢-iso₂
  ⊢-iso₂ {Γ} {τ₁ `→ τ₂} {⟨ ▻ ▻ ▻ ∙ , ((α , σ , τ) , snd) , snd₁ ⟩} =
    cong (λ x → ⟨ (▻ ▻ ▻ ∙ , ((α , σ , τ) , snd) , x) ⟩) ⊢-iso₂
  ⊢-iso₂ {Γ} {`∀ x · τ} {⟨ ∙ , snd ⟩} = refl
  ⊢-iso₂ {Γ} {`∀ x · τ} {⟨ ▻ ∙ , σ , fst₁ , snd ⟩} =
    cong₂ (λ x y → ⟨ ((▻ ∙) , σ , x , y) ⟩) ⊢-iso₂ ⊢-iso₂
  ⊢-iso₂ {Γ} {`∀ x · τ'} {⟨ ▻ ▻ ∙ , ((α , σ , τ) , snd) , snd₁ ⟩} =
    cong (λ x → ⟨ (▻ ▻ ∙ , ((α , σ , τ) , snd) , x) ⟩) ⊢-iso₂
  ⊢-iso₂ {Γ} {`∀ x · τ} {⟨ ▻ ▻ ▻ ∙ , fst , snd ⟩} =
    cong (λ x → ⟨ ((▻ ▻ ▻ ∙) , fst , x) ⟩) ⊢-iso₂

  instance
    ⊢≅IDesc : ≅IDesc {I = Ctx × 𝕋}  λ { (Γ , τ) → Γ ⊢ τ }
    ⊢≅IDesc = record {
      W = λ2D , ≅-transitive (≅-symmetric ≅lift) (
        record { from = from⊢
               ; to   = to⊢
               ; iso₁ = ⊢-iso₁
               ; iso₂ = ⊢-iso₂
               }) }
