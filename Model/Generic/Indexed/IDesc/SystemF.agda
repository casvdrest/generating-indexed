{-# OPTIONS --type-in-type #-}

open import Data.Nat
open import Data.Char
open import Data.List
open import Data.Product
open import Data.Unit hiding (_≟_)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality 

open import Level renaming (suc to sucL ; zero to zeroL)

open import AgdaGen.Base renaming (μ to μB)
open import AgdaGen.Combinators
open import AgdaGen.Enumerate hiding (⟨_⟩)

open import AgdaGen.Generic.Isomorphism

open import AgdaGen.Generic.Indexed.IDesc.Universe
open import AgdaGen.Generic.Indexed.IDesc.Generator

module AgdaGen.Generic.Indexed.IDesc.SystemF where

  open GFunctor ⦃...⦄
  open GApplicative ⦃...⦄
  open GMonad ⦃...⦄
  open GAlternative ⦃...⦄
  open GNullable ⦃...⦄

  Id : Set
  Id = ℕ

  data 𝕋 : Set where
    ``_  : Id → 𝕋
    _`→_ : 𝕋 → 𝕋 → 𝕋
    `∀_·_  : Id → 𝕋 → 𝕋

  genId : 𝔾 Id
  genId = ⦇ ℕ.zero ⦈ ∥ ⦇ (ℕ.suc ℕ.zero) ⦈

  genId≡ : (α β : Id) → 𝔾 (α ≡ β)
  genId≡ α β with α ≟ β
  ... | yes α≡β = pure α≡β
  ... | no ¬α≡β = empty

  gen𝕋 : 𝔾 𝕋
  gen𝕋 = ⦇ `` (` genId) ⦈
        ∥ ⦇ μB `→ μB ⦈
        ∥ ⦇ `∀ (` genId) · μB ⦈

  𝕋≡ : (τ₁ : 𝕋) → (τ₂ : 𝕋) → 𝔾 (τ₁ ≡ τ₂)
  𝕋≡ (`` x) (`` x₁) = ⦇ (cong ``_) (` genId≡ x x₁) ⦈
  𝕋≡ (`` x) (τ₂ `→ τ₃) = empty
  𝕋≡ (`` x) (`∀ x₁ · τ₂) = empty
  𝕋≡ (τ₁ `→ τ₃) (`` x) = empty
  𝕋≡ (τ₁ `→ τ₃) (τ₂ `→ τ₄) = ⦇ (cong₂ _`→_) (` 𝕋≡ τ₁ τ₂) (` 𝕋≡ τ₃ τ₄) ⦈ 
  𝕋≡ (τ₁ `→ τ₃) (`∀ x · τ₂) = empty
  𝕋≡ (`∀ x · τ₁) (`` x₁) = empty
  𝕋≡ (`∀ x · τ₁) (τ₂ `→ τ₃) = empty
  𝕋≡ (`∀ x · τ₁) (`∀ x₁ · τ₂) = ⦇ (cong₂ `∀_·_) (` genId≡ x x₁) (` 𝕋≡ τ₁ τ₂) ⦈
    
  data λ2 : Set where
    `_   : Id → λ2
    _·_  : λ2 → λ2 → λ2
    ƛ_⇒_ : Id → λ2 → λ2
    _∶∶_ : λ2 → 𝕋 → λ2
 
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

  CtxD : func 0ℓ (Ctx × 𝕋) (Ctx × 𝕋)
  CtxD = func.mk λ
    { (∅ , τ) → `σ 0 λ()
    ; (Γ , x ∶ σ , τ) → `σ 2 λ
        { ∙     → `Σ (σ ≡ τ) λ { refl → `1 } -- top 
        ; (▻ ∙) → `var (Γ , τ)
        }
    }

  CtxM : (ix : Ctx × 𝕋) → IDescM 𝔾 (func.out CtxD ix)
  CtxM (∅ , τ) = `σ~ (λ ())
  CtxM (Γ , x ∶ σ , τ) = `σ~ (
    λ { ∙     → `Σ~ (𝕋≡ σ τ) (λ { refl → `1~ })
      ; (▻ ∙) → `var~
      })

  fromCtx : ∀ {Γ τ} → Γ ∋ τ → μ CtxD (Γ , τ)
  fromCtx {.(_ , _ ∶ τ)} {τ} [Top]     = ⟨ (∙ , refl , lift tt) ⟩
  fromCtx {.(_ , _ ∶ _)} {τ} ([Pop] p) = ⟨ ((▻ ∙) , (fromCtx p)) ⟩

  toCtx : ∀ {Γ τ} → μ CtxD (Γ , τ) → Γ ∋ τ
  toCtx {Γ , x ∶ σ} {.σ} ⟨ ∙ , refl , lift tt ⟩ = [Top]
  toCtx {Γ , x ∶ σ} {τ} ⟨ ▻ ∙ , snd ⟩           = [Pop] (toCtx snd)

  Ctx-iso₁ : ∀ {Γ τ} {p : Γ ∋ τ} → toCtx (fromCtx p) ≡ p
  Ctx-iso₁ {.(_ , _ ∶ τ)} {τ} {[Top]} = refl
  Ctx-iso₁ {.(_ , _ ∶ _)} {τ} {[Pop] p} = cong [Pop] Ctx-iso₁

  Ctx-iso₂ : ∀ {Γ τ} {p : μ CtxD (Γ , τ)} → fromCtx (toCtx p) ≡ p
  Ctx-iso₂ {Γ , x₁ ∶ x₂} {.x₂} {⟨ ∙ , refl , lift tt ⟩} = refl
  Ctx-iso₂ {Γ , x₁ ∶ x₂} {τ} {⟨ ▻ ∙ , snd ⟩}            = cong (λ x → ⟨ (▻ ∙) , x ⟩) Ctx-iso₂

  instance
    Ctx≅IDesc : ≅IDesc {I = Ctx × 𝕋} λ { (Γ , τ) → Γ ∋ τ }
    Ctx≅IDesc = record
      { W = CtxD
      , ≅-transitive (≅-symmetric ≅lift) (record
          { from = fromCtx
          ; to   = toCtx
          ; iso₁ = Ctx-iso₁
          ; iso₂ = Ctx-iso₂
          })
      }

  data _∌ₜ_ : 𝕋 → Id → Set where

   [∌ₜ-var] : ∀ {α β} → ¬ α ≡ β
            ---------------------
            → (`` β) ∌ₜ α

   [∌ₜ-fty] : ∀ {α τ₁ τ₂} → τ₁ ∌ₜ α → τ₂ ∌ₜ α
            ---------------------------------
            → (τ₁ `→ τ₂) ∌ₜ α

   [∌ₜ-∀¬≡] : ∀ {α β τ} → ¬ α ≡ β → τ ∌ₜ α
            ------------------------------
            → (`∀ β · τ) ∌ₜ α

   [∌ₜ-∀≡]  : ∀ {α τ}
            -----------------
            → (`∀ α · τ) ∌ₜ α

  ∌ₜD : func 0ℓ (𝕋 × Id) (𝕋 × Id)
  ∌ₜD = func.mk λ
    { ((`` β) , α) → `Σ (¬ α ≡ β) λ _ → `1
    ; ((τ₁ `→ τ₂) , α) → `var (τ₁ , α) `× `var (τ₂ , α)
    ; ((`∀ β · τ) , α) → `σ 2 λ
        { ∙     → `Σ (¬ α ≡ β) λ _ → `var (τ , α)
        ; (▻ ∙) → `Σ (α ≡ β) λ { refl → `1 }
        }
    }

  Id≡ : (α : Id) → (β : Id) → 𝔾 (α ≡ β)
  Id≡ α β with α ≟ β
  Id≡ α β | yes p = pure p
  Id≡ α β | no ¬p = empty

  Id¬≡ : (α : Id) → (β : Id) → 𝔾 (¬ α ≡ β)
  Id¬≡ α β with α ≟ β
  Id¬≡ α β | yes p = empty
  Id¬≡ α β | no ¬p = pure ¬p

  ∌ₜM : (ix : 𝕋 × Id) → IDescM 𝔾 (func.out ∌ₜD ix)
  ∌ₜM ((`` β) , α) =
    `Σ~ (Id¬≡ α β) λ _ → `1~
  ∌ₜM ((τ₁ `→ τ₂) , α) =
    `var~ `×~ `var~
  ∌ₜM ((`∀ β · τ) , α) =
    `σ~ (λ { ∙     → `Σ~ (Id¬≡ α β) λ _ → `var~
           ; (▻ ∙) → `Σ~ (Id≡ α β) λ { refl → `1~ }
           })

  from∌ₜ : ∀ {τ α} → τ ∌ₜ α → μ ∌ₜD (τ , α)
  from∌ₜ {.(`` _)} {α} ([∌ₜ-var] x) =
    ⟨ x , lift tt ⟩
  from∌ₜ {.(_ `→ _)} {α} ([∌ₜ-fty] p p₁) =
    ⟨ (from∌ₜ p , from∌ₜ p₁) ⟩
  from∌ₜ {.(`∀ _ · _)} {α} ([∌ₜ-∀¬≡] x p) =
    ⟨ (∙ , (x , from∌ₜ p)) ⟩
  from∌ₜ {.(`∀ α · _)} {α} [∌ₜ-∀≡] =
    ⟨ ((▻ ∙) , (refl , lift tt)) ⟩

  to∌ₜ : ∀ {τ α} → μ ∌ₜD (τ , α) → τ ∌ₜ α
  to∌ₜ {`` x₁} {α} ⟨ fst , lift tt ⟩ =
    [∌ₜ-var] fst
  to∌ₜ {τ `→ τ₁} {α} ⟨ fst , snd ⟩ =
    [∌ₜ-fty] (to∌ₜ fst) (to∌ₜ snd)
  to∌ₜ {`∀ x₁ · τ} {α} ⟨ ∙ , fst , snd ⟩ =
    [∌ₜ-∀¬≡] fst (to∌ₜ snd)
  to∌ₜ {`∀ x₁ · τ} {.x₁} ⟨ ▻ ∙ , refl , snd ⟩ =
    [∌ₜ-∀≡]

  ∌ₜ-iso₁ : ∀ {τ α} {p : τ ∌ₜ α} → to∌ₜ (from∌ₜ p) ≡ p
  ∌ₜ-iso₁ {`` x} {α} {[∌ₜ-var] x₁} = refl
  ∌ₜ-iso₁ {τ `→ τ₁} {α} {[∌ₜ-fty] p p₁} =
    cong₂ [∌ₜ-fty] ∌ₜ-iso₁ ∌ₜ-iso₁
  ∌ₜ-iso₁ {`∀ x · τ} {α} {[∌ₜ-∀¬≡] x₁ p} =
    cong ([∌ₜ-∀¬≡] x₁) ∌ₜ-iso₁
  ∌ₜ-iso₁ {`∀ x · τ} {.x} {[∌ₜ-∀≡]} = refl

  ∌ₜ-iso₂ : ∀ {τ α} {p : μ ∌ₜD (τ , α)} → from∌ₜ (to∌ₜ p) ≡ p
  ∌ₜ-iso₂ {`` x} {α} {⟨ fst , lift tt ⟩} = refl
  ∌ₜ-iso₂ {τ `→ τ₁} {α} {⟨ fst , snd ⟩} =
    cong₂ (λ x y → ⟨ x , y ⟩) ∌ₜ-iso₂ ∌ₜ-iso₂
  ∌ₜ-iso₂ {`∀ x · τ} {α} {⟨ ∙ , fst , snd ⟩} =
    cong (λ x → ⟨ (∙ , fst , x) ⟩) ∌ₜ-iso₂
  ∌ₜ-iso₂ {`∀ x · τ} {.x} {⟨ ▻ ∙ , refl , lift tt ⟩} = refl

  instance
    ∌ₜ≅IDesc : ≅IDesc {I = 𝕋 × Id} λ { (τ , α) → τ ∌ₜ α }
    ∌ₜ≅IDesc = record
      { W = ∌ₜD
      , ≅-transitive (≅-symmetric ≅lift) (record
        { from = from∌ₜ
        ; to   = to∌ₜ 
        ; iso₁ = ∌ₜ-iso₁
        ; iso₂ = ∌ₜ-iso₂ }) }

  gen∌ₜ : ((ix : 𝕋 × Id) → IDescM 𝔾 (func.out ∌ₜD ix))
       → (ix : 𝕋 × Id) → 𝔾ᵢ (λ { (τ , α) → Lift 0ℓ (τ ∌ₜ α) }) ix
  gen∌ₜ m (τ , α) = IDesc-isoGen (τ , α) m

  data _∌_ : Ctx → Id → Set where
  
    [∌₁] : ∀ {α}
         -------
         → ∅ ∌ α
    
    [∌₂] : ∀ {Γ α x τ} → Γ ∌ α → τ ∌ₜ α
         ------------------------------
         → (Γ , x ∶ τ) ∌ α 

  ∌D : func 0ℓ (Ctx × Id) (Ctx × Id)
  ∌D = func.mk λ
    { (∅ , α) → `1
    ; ((Γ , x ∶ τ) , α) → `Σ (τ ∌ₜ α) λ _ → `var (Γ , α)
    }

  ∌M : (ix : Ctx × Id) → IDescM 𝔾 (func.out ∌D ix)
  ∌M (∅ , α) = `1~
  ∌M (Γ , x ∶ τ , α) = `Σ~ ⦇ lower ⟨ τ , α ` gen∌ₜ ∌ₜM ⟩ ⦈ λ _ → `var~

  from∌ : ∀ {Γ α} → Γ ∌ α → μ ∌D (Γ , α)
  from∌ {.∅} {α} [∌₁]                 = ⟨ lift tt ⟩
  from∌ {.(_ , _ ∶ _)} {α} ([∌₂] p x) = ⟨ x , from∌ p ⟩

  to∌ : ∀ {Γ α} → μ ∌D (Γ , α) → Γ ∌ α
  to∌ {∅} {α} ⟨ lift tt ⟩             = [∌₁]
  to∌ {Γ , x₁ ∶ x₂} {α} ⟨ fst , snd ⟩ = [∌₂] (to∌ snd) fst

  ∌-iso₁ : ∀ {Γ α} {p : Γ ∌ α} → to∌ (from∌ p) ≡ p
  ∌-iso₁ {.∅} {α} {[∌₁]}               = refl
  ∌-iso₁ {.(_ , _ ∶ _)} {α} {[∌₂] p x} = cong (λ p → [∌₂] p x) ∌-iso₁

  ∌-iso₂ : ∀ {Γ α} {p : μ ∌D (Γ , α)} → from∌ (to∌ p) ≡ p
  ∌-iso₂ {∅} {α} {⟨ lift tt ⟩}           = refl
  ∌-iso₂ {Γ , x ∶ τ} {α} {⟨ fst , snd ⟩} = cong (λ p → ⟨ fst , p ⟩) ∌-iso₂

  instance
    ∌≅IDesc : ≅IDesc {I = Ctx × Id} λ { (Γ , α) → Γ ∌ α }
    ∌≅IDesc = record
      { W = ∌D
      , ≅-transitive (≅-symmetric ≅lift) (record
        { from = from∌
        ; to   = to∌
        ; iso₁ = ∌-iso₁
        ; iso₂ = ∌-iso₂
        }) }

  _[_:=_] : 𝕋 → Id → 𝕋 → 𝕋
  (`` β) [ α := τ ] with α ≟ β
  ... | (yes α≡β) = τ
  ... | (no ¬α≡β) = `` β
  (σ₁ `→ σ₂) [ α := τ ] = (σ₁ [ α := τ ]) `→ (σ₂ [ α := τ ]) 
  (`∀ β · σ) [ α := τ ] with α ≟ β
  ... | (yes α≡β) = `∀ β · σ
  ... | (no ¬α≡β) = `∀ β · (σ [ α := τ ])
 
  infix 10 _⊢_
  infix 15 _,_∶_

  data _⊢_ : Ctx → 𝕋 → Set where

    [λ2-var] : ∀ {Γ σ} → Γ ∋ σ
             -----------------
             → Γ ⊢ σ

    [λ2-app] : ∀ {Γ σ τ} → Γ ⊢ (σ `→ τ) → Γ ⊢ σ
             ----------------------------------
             → Γ ⊢ τ

    [λ2-abs] : ∀ {Γ x σ τ} → (Γ , x ∶ σ) ⊢ τ
             -------------------------------
             → Γ ⊢ (σ `→ τ)

    [λ2-∀₁]  : ∀ {Γ α σ τ} → Γ ⊢ (`∀ α · σ)
             ------------------------------
             → Γ ⊢ (σ [ α := τ ])

    [λ2-∀₂]  : ∀ {Γ α σ} → Γ ⊢ σ → Γ ∌ α 
             ---------------------------
             → Γ ⊢ ( `∀ α · σ)


  λ2D : func 0ℓ (Ctx × 𝕋) (Ctx × 𝕋)
  λ2D = func.mk λ
    { (Γ , τ) → `σ 5
        λ { ∙           → `Σ (Γ ∋ τ) λ _ → `1
          ; (▻ ∙)       → `Σ 𝕋 λ σ → `var (Γ , σ `→ τ) `× `var (Γ , σ)
          ; (▻ ▻ ∙)     → `Σ (Σ (𝕋 × 𝕋) λ { (τ₁ , τ₂) → τ ≡ τ₁ `→ τ₂ })
                            λ { ((τ₁ , τ₂) , refl) → `Σ Id λ α → `var (Γ , α ∶ τ₁ , τ₂) } 
          ; (▻ ▻ ▻ ∙)   → `Σ (Σ (𝕋 × Id × 𝕋) λ { (σ , α , τ') → τ ≡ (σ [ α := τ' ]) })
                            λ { ((σ , α , τ') , refl) → `var (Γ , (`∀ α · σ)) }
          ; (▻ ▻ ▻ ▻ ∙) → `Σ (Σ (Id × 𝕋) λ { (α , σ) → τ ≡ (`∀ α · σ) })
                            λ { ((α , σ) , refl) → `Σ (Γ ∌ α) λ _ → `var (Γ , σ) } 
          } }

  fromλ2 : ∀ {Γ τ} → Γ ⊢ τ → μ λ2D (Γ , τ)
  fromλ2 ([λ2-var] x) =
    ⟨ (∙ , x , lift tt) ⟩
  fromλ2 ([λ2-app] {σ = σ} p p₁) =
    ⟨ ((▻ ∙) , σ , fromλ2 p , fromλ2 p₁) ⟩
  fromλ2 {τ = τ₁ `→ τ₂} ([λ2-abs] {x = x} p) =
    ⟨ ((▻ ▻ ∙) , ((τ₁ , τ₂) , refl) , x , fromλ2 p) ⟩
  fromλ2 {τ = .(σ [ α := τ ])} ([λ2-∀₁] {α = α} {σ = σ} {τ = τ} p) =
    ⟨ (▻ ▻ ▻ ∙ , ((σ , α , τ) , refl) , fromλ2 p) ⟩
  fromλ2 {τ = `∀ α · σ} ([λ2-∀₂] p x) =
    ⟨ ((▻ ▻ ▻ ▻ ∙) , ((α , σ) , refl) , x , fromλ2 p) ⟩

  toλ2 : ∀ {Γ τ} → μ λ2D (Γ , τ) → Γ ⊢ τ
  toλ2 {Γ} {τ} ⟨ ∙ , fst , lift tt ⟩ =
    [λ2-var] fst
  toλ2 {Γ} {τ} ⟨ ▻ ∙ , fst , fst₁ , snd ⟩ =
    [λ2-app] (toλ2 fst₁) (toλ2 snd)
  toλ2 {Γ} {.(τ₁ `→ τ₂)} ⟨ ▻ ▻ ∙ , ((τ₁ , τ₂) , refl) , α , snd ⟩ =
    [λ2-abs] (toλ2 snd)
  toλ2 {Γ} {.(σ [ α := τ' ])} ⟨ ▻ ▻ ▻ ∙ , ((σ , α , τ') , refl) , snd ⟩ =
    [λ2-∀₁] (toλ2 snd)
  toλ2 {Γ} {.(`∀ α · σ)} ⟨ ▻ ▻ ▻ ▻ ∙ , ((α , σ) , refl) , fst , snd ⟩ =
    [λ2-∀₂] (toλ2 snd) fst

  λ2-iso₁ : ∀ {Γ τ} {p : Γ ⊢ τ} → toλ2 (fromλ2 p) ≡ p
  λ2-iso₁ {Γ} {τ} {[λ2-var] x} = refl
  λ2-iso₁ {Γ} {τ} {[λ2-app] p p₁} =
    cong₂ [λ2-app] λ2-iso₁ λ2-iso₁
  λ2-iso₁ {Γ} {(σ `→ τ)} {[λ2-abs] p} =
    cong [λ2-abs] λ2-iso₁
  λ2-iso₁ {Γ} {τ} {[λ2-∀₁] p} =
    cong [λ2-∀₁] λ2-iso₁
  λ2-iso₁ {Γ} {(`∀ α · σ)} {[λ2-∀₂] p x} =
    cong (λ p → [λ2-∀₂] p x) λ2-iso₁

  λ2-iso₂ : ∀ {Γ τ} {p : μ λ2D (Γ , τ)} → fromλ2 (toλ2 p) ≡ p
  λ2-iso₂ {Γ} {τ} {⟨ ∙ , fst , lift tt ⟩} = refl
  λ2-iso₂ {Γ} {τ} {⟨ ▻ ∙ , σ , fst , snd ⟩} =
    cong₂ (λ x y → ⟨ ((▻ ∙) , σ , x , y) ⟩) λ2-iso₂ λ2-iso₂
  λ2-iso₂ {Γ} {.(τ₁ `→ τ₂)} {⟨ ▻ ▻ ∙ , ((τ₁ , τ₂) , refl) , α , snd ⟩} =
    cong (λ x → ⟨ (▻ ▻ ∙ , ((τ₁ , τ₂) , refl) , α , x) ⟩) λ2-iso₂
  λ2-iso₂ {Γ} {.(σ [ α := τ' ])} {⟨ ▻ ▻ ▻ ∙ , ((σ , α , τ') , refl) , snd₁ ⟩} =
    cong (λ x → ⟨ ((▻ ▻ ▻ ∙) , ((σ , α , τ') , refl) , x) ⟩) λ2-iso₂
  λ2-iso₂ {Γ} {.(`∀ α · σ)} {⟨ ▻ ▻ ▻ ▻ ∙ , ((α , σ) , refl) , fst , snd ⟩} =
    cong (λ x → ⟨ ((▻ ▻ ▻ ▻ ∙) , ((α , σ) , refl) , fst , x) ⟩) λ2-iso₂

  instance
   λ2-≅IDesc : ≅IDesc {I = Ctx × 𝕋} (λ { (Γ , τ) → Γ ⊢ τ })
   λ2-≅IDesc = record
     { W = λ2D
     , ≅-transitive (≅-symmetric ≅lift)
       (record { from = fromλ2
               ; to   = toλ2
               ; iso₁ = λ2-iso₁
               ; iso₂ = λ2-iso₂
               })
     }

  gen∋ :
    ((ix : Ctx × 𝕋) → IDescM 𝔾 (func.out CtxD ix))
    → (Γ : Ctx) → (τ : 𝕋)
    → 𝔾ᵢ (λ { ( Γ , τ ) → Lift 0ℓ (Γ ∋ τ) }) (Γ , τ)
  gen∋ m Γ τ = IDesc-isoGen (Γ , τ) m

  gen∌ :
    ((ix : Ctx × Id) → IDescM 𝔾 (func.out ∌D ix))
    → (Γ : Ctx) → (α : Id)
    → 𝔾ᵢ (λ { ( Γ , α ) → Lift 0ℓ (Γ ∌ α) }) (Γ , α)
  gen∌ m Γ τ = IDesc-isoGen (Γ , τ) m

  𝕋-as`→ : (τ : 𝕋) → 𝔾 (Σ (𝕋 × 𝕋) λ { (τ₁ , τ₂) → τ ≡ τ₁ `→ τ₂ })
  𝕋-as`→ (`` x) = empty
  𝕋-as`→ (τ₁ `→ τ₂) = pure ((τ₁ , τ₂) , refl)
  𝕋-as`→ (`∀ x · τ) = empty

  𝕋-as`∀ :(τ : 𝕋) → 𝔾 (Σ (Id × 𝕋) λ { (α , σ) → τ ≡ `∀ α · σ})
  𝕋-as`∀ (`` x) = empty
  𝕋-as`∀ (τ `→ τ₁) = empty
  𝕋-as`∀ (`∀ α · σ) = pure ((α , σ) , refl)
  
  [:=]inv : (τ' : 𝕋) → 𝔾 (Σ (𝕋 × Id × 𝕋) λ { (σ , α , τ) → τ' ≡ σ [ α := τ ] })
  [:=]inv τ' = pure (((`` ℕ.zero) , ℕ.zero , τ') , refl) ∥ pure (((`` 1) , 1 , τ') , refl)

  λ2M : (ix : Ctx × 𝕋) → IDescM 𝔾 (func.out λ2D ix)
  λ2M = λ { (Γ , τ) → `σ~ (
    λ { ∙            → `Σ~ ⦇ lower ⟨ Γ , τ ` uncurry (gen∋ CtxM) ⟩ ⦈ λ s → `1~
       ; (▻ ∙)       → `Σ~ gen𝕋 λ s → `var~ `×~ `var~
       ; (▻ ▻ ∙)     → `Σ~ (𝕋-as`→ τ) λ { (_ , refl) → `Σ~ genId (λ _ → `var~) }
       ; (▻ ▻ ▻ ∙)   → `Σ~ ([:=]inv τ) λ { (_ , refl) → `var~ }
       ; (▻ ▻ ▻ ▻ ∙) → `Σ~ (𝕋-as`∀ τ) λ { ((α , σ) , refl) → `Σ~ (⦇ lower ⟨ Γ , α ` uncurry (gen∌ ∌M) ⟩ ⦈) λ _ → `var~ } 
    })}

  genλ2 : (ix : Ctx × 𝕋) → 𝔾ᵢ (λ { (Γ , τ) → Γ ⊢ τ }) ix
  genλ2 (Γ , τ) = ⦇ lower (Callᵢ {x = Γ , τ} (λ ix → IDesc-isoGen ix λ2M) (Γ , τ)) ⦈ 

  ctx1 : Ctx
  ctx1 = ∅ , 0 ∶ (`` 0)

  ty1 : 𝕋
  ty1 = `∀ 1 · ((`` 1) `→ (`` 1))

  toId : ∀ {Γ τ} → Γ ∋ τ → Id
  toId {(_ , α ∶ _)} [Top] = α
  toId {(Γ , _ ∶ _)} ([Pop] p) = toId p

  toTerm : ∀ {Γ τ} → Γ  ⊢ τ → λ2
  toTerm ([λ2-var] x) = ` toId x
  toTerm ([λ2-app] p₁ p₂) = toTerm p₁ · toTerm p₂
  toTerm ([λ2-abs] {x = x} p) = ƛ x ⇒ toTerm p
  toTerm ([λ2-∀₁] p) = toTerm p
  toTerm ([λ2-∀₂] {α = α} {σ = σ}  p x) = toTerm p ∶∶ (`∀ α · σ)

  prop : (take 1 (⟨ genλ2 ⟩ᵢ (ctx1 , ty1) 4)) ≡ {!!} 
  prop = {!refl!}

  
