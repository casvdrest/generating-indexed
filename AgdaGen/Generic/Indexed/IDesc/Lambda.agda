{-# OPTIONS --type-in-type #-}

open import AgdaGen.Base renaming (μ to gμ)
open import AgdaGen.Combinators
open import AgdaGen.Enumerate hiding (⟨_⟩)
open import AgdaGen.Generic.Isomorphism
open import AgdaGen.Generic.Indexed.IDesc.Universe
open import AgdaGen.Generic.Indexed.IDesc.Generator

open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Fin hiding (lift; _+_)
open import Data.List hiding (fromMaybe)
open import Data.Maybe hiding (fromMaybe)

open import Level 
    renaming ( zero to zeroL 
             ; suc to sucL ) 

open import Relation.Binary.PropositionalEquality

module AgdaGen.Generic.Indexed.IDesc.Lambda where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
  open GMonad       ⦃...⦄
  open GNullable    ⦃...⦄

  data Ty : Set where
    `τ   : Ty
    _`→_ : Ty → Ty → Ty

  Id : Set
  Id = ℕ
  
  data Ctx : Set where
    ∅     : Ctx
    _,_∶_ : Ctx → Id → Ty → Ctx

  infix 10 _∋_

  data _∋_ : Ctx → Ty → Set where

    [Top] : ∀ {Γ α τ}
          ---------------
          → Γ , α ∶ τ ∋ τ

    [Pop] : ∀ {Γ α σ τ}
          → Γ ∋ τ
          ---------------
          → Γ , α ∶ σ ∋ τ

  infix 10 _⊢_

  data _⊢_ : Ctx → Ty → Set where

    [Var] : ∀ {Γ τ} → Γ ∋ τ
            ---------------
            → Γ ⊢ τ

    [Abs] : ∀ {Γ τ σ α} → Γ , α ∶ σ ⊢ τ
          -----------------------------
          → Γ ⊢ σ `→ τ

    [App] : ∀ {Γ τ σ} → Γ ⊢ σ → Γ ⊢ σ `→ τ
          --------------------------------
          → Γ ⊢ τ

  data Tm : Set where
    Abs : Id → Tm → Tm
    Var : Id → Tm
    App : Tm → Tm → Tm

  ∋D : func zeroL (Ctx × Ty) (Ctx × Ty)
  ∋D = func.mk 
    λ { (∅ , τ) → `σ 0 λ()
      ; ((Γ , α ∶ σ) , τ)
        → `σ 2 λ {  ∙    → `Σ (τ ≡ σ) λ { refl → `1 }
                 ; (▻ ∙) → `var (Γ , τ) }
      }

  ⊢D : func zeroL (Ctx × Ty) (Ctx × Ty)
  ⊢D = func.mk
    λ { (Γ , `τ) →
        `σ 2 λ
           {  ∙    → `Σ (Γ ∋ `τ) λ _ → `1
           ; (▻ ∙) → `Σ Ty λ σ → `var (Γ , σ) `× `var (Γ , (σ `→ `τ))
           }
      ; (Γ , (σ `→ τ)) →
        `σ 3 λ
           { (∙)     → `Σ (Γ ∋ σ `→ τ) λ _ → `1
           ; (▻ ∙)   → `Σ Id λ α → `var ((Γ , α ∶ σ) , τ)
           ; (▻ ▻ ∙) → `Σ Ty λ σ' → `var (Γ , σ') `× `var (Γ , (σ' `→ (σ `→ τ)))
           }
      }

  from∋ : ∀ {Γ τ} → uncurry _∋_ (Γ , τ) → μ ∋D (Γ , τ)
  from∋ {Γ , x ∶ σ} {.σ} [Top]    = ⟨ (∙ , refl , lift tt) ⟩
  from∋ {Γ , x ∶ σ} {τ} ([Pop] p) = ⟨ (▻ ∙) , (from∋ p) ⟩

  to∋ : ∀ {Γ τ} → μ ∋D (Γ , τ) → uncurry _∋_ (Γ , τ)
  to∋ {Γ , α ∶ σ} {.σ} ⟨ ∙ , refl , lift tt ⟩ = [Top]
  to∋ {Γ , α ∶ σ} {τ} ⟨ ▻ ∙ , p ⟩ = [Pop] (to∋ p)

  ∋-iso₁ : ∀ {Γ τ} {P : uncurry _∋_ (Γ , τ)} → to∋ (from∋ P) ≡ P
  ∋-iso₁ {Γ , α ∶ σ} {.σ} {[Top]}   = refl
  ∋-iso₁ {Γ , α ∶ σ} {τ}  {[Pop] P} = cong [Pop] ∋-iso₁

  ∋-iso₂ : ∀ {Γ : Ctx} {τ : Ty} {P : μ ∋D (Γ , τ)} → from∋ (to∋ P) ≡ P
  ∋-iso₂ {Γ , α ∶ σ} {.σ} {⟨ ∙ , refl , lift tt ⟩} = refl
  ∋-iso₂ {Γ , α ∶ σ} {τ} {⟨ ▻ ∙ , r ⟩}             = cong (λ x → ⟨ (▻ ∙ , x) ⟩) ∋-iso₂

  type : ∀ {Γ τ} → Γ ⊢ τ → Ty
  type {τ = τ} _ = τ

  ident : ∀ {Γ α σ τ} → Γ , α ∶ σ ⊢ τ → Id
  ident {α = α} _ = α

  from⊢ : ∀ {Γ τ} → uncurry _⊢_ (Γ , τ) → μ ⊢D (Γ , τ)
  from⊢ {Γ} {`τ    } ([Var] α    ) = ⟨ (∙ , α , lift tt) ⟩
  from⊢ {Γ} {`τ    } ([App] t₁ t₂) = ⟨ (▻ ∙ , type t₁ , from⊢ t₁ , from⊢ t₂) ⟩
  from⊢ {Γ} {τ `→ σ} ([Var] α    ) = ⟨ (∙ , (α , (lift tt))) ⟩
  from⊢ {Γ} {τ `→ σ} ([Abs] t    ) = ⟨ (▻ ∙ , ident t , from⊢ t) ⟩
  from⊢ {Γ} {τ `→ σ} ([App] t₁ t₂) = ⟨ (▻ ▻ ∙ , type t₁ , (from⊢ t₁) , (from⊢ t₂)) ⟩

  to⊢ : ∀ {Γ τ} → μ ⊢D (Γ , τ) → uncurry _⊢_ (Γ , τ)
  to⊢ {Γ} {`τ     } ⟨ ∙ , ∋Γ , lift tt    ⟩ = [Var] ∋Γ
  to⊢ {Γ} {`τ     } ⟨ ▻ ∙ , σ , t₁ , t₂   ⟩ = [App] (to⊢ t₁) (to⊢ t₂)
  to⊢ {Γ} {τ `→ τ₁} ⟨ ∙ , ∋Γ , lift tt    ⟩ = [Var] ∋Γ
  to⊢ {Γ} {τ `→ τ₁} ⟨ ▻ ∙ , α , snd       ⟩ = [Abs] (to⊢ snd)
  to⊢ {Γ} {τ `→ τ₁} ⟨ ▻ ▻ ∙ , σ , t₁ , t₂ ⟩ = [App] (to⊢ t₁) (to⊢ t₂)

  ⊢-iso₁ : ∀ {Γ τ P} → to⊢ {Γ} {τ} (from⊢ P) ≡ P
  ⊢-iso₁ {Γ} {`τ     } {[Var] ∋Γ   } = refl
  ⊢-iso₁ {Γ} {`τ     } {[App] t₁ t₂} = cong₂ [App] ⊢-iso₁ ⊢-iso₁
  ⊢-iso₁ {Γ} {τ `→ τ₁} {[Var] ∋Γ   } = refl
  ⊢-iso₁ {Γ} {τ `→ τ₁} {[Abs] t    } = cong [Abs] ⊢-iso₁
  ⊢-iso₁ {Γ} {τ `→ τ₁} {[App] t₁ t₂} = cong₂ [App] ⊢-iso₁ ⊢-iso₁

  ⊢-iso₂ : ∀ {Γ τ P} → from⊢ {Γ} {τ} (to⊢ P) ≡ P
  ⊢-iso₂ {Γ} {`τ     } {⟨ ∙   , ∋Γ , lift tt ⟩ } = refl
  ⊢-iso₂ {Γ} {`τ     } {⟨ ▻ ∙ , σ , t₁ , t₂ ⟩  } =
    cong₂ (λ r₁ r₂ → ⟨ ((▻ ∙) , (σ , (r₁ , r₂))) ⟩) ⊢-iso₂ ⊢-iso₂
  ⊢-iso₂ {Γ} {τ `→ τ₁} {⟨ ∙   , ∋Γ , lift tt ⟩ } = refl
  ⊢-iso₂ {Γ} {τ `→ τ₁} {⟨ ▻ ∙ , α , t ⟩        } =
    cong (λ r → ⟨ ▻ ∙ , α , r ⟩) ⊢-iso₂
  ⊢-iso₂ {Γ} {τ `→ τ₁} {⟨ ▻ ▻ ∙ , σ , t₁ , t₂ ⟩} =
    cong₂ (λ r₁ r₂ → ⟨ ((▻ ▻ ∙) , σ , (r₁ , r₂)) ⟩) ⊢-iso₂ ⊢-iso₂

  instance
    ∋-≅IDesc : ≅IDesc (uncurry _∋_)
    ∋-≅IDesc = record { W = ∋D , ≅-transitive (≅-symmetric ≅lift) (record { from = from∋ ; to = to∋ ; iso₁ = ∋-iso₁ ; iso₂ = ∋-iso₂ }) }

  gen∋ : ((ix : Ctx × Ty) → IDescM 𝔾 (func.out ∋D ix)) → (Γ : Ctx) → (τ : Ty) → 𝔾ᵢ (λ { ( Γ , τ ) → Lift 0ℓ (Γ ∋ τ) }) (Γ , τ)
  gen∋ m Γ τ = IDesc-isoGen (Γ , τ) m

  Ty≡ : (σ τ : Ty) → 𝔾 (σ ≡ τ)
  Ty≡ `τ `τ = pure refl
  Ty≡ `τ (τ `→ τ₁) = empty
  Ty≡ (σ `→ σ₁) `τ = empty
  Ty≡ (σ₁ `→ σ₂) (τ₁ `→ τ₂) = ⦇ (cong₂ _`→_) (` Ty≡ σ₁ τ₁) (` Ty≡ σ₂ τ₂) ⦈

  ∋M : (ix : Ctx × Ty) → IDescM 𝔾 (func.out ∋D ix)
  ∋M (∅ , τ) = `σ~ λ()
  ∋M ((Γ , α ∶ σ) , τ) = `σ~ λ { ∙ → `Σ~ (Ty≡ τ σ) λ { refl → `1~ } ; (▻ ∙) → `var~ }

  test : ⟨ uncurry (gen∋ ∋M) ⟩ᵢ ((∅ , 0 ∶ `τ) , 1 ∶ `τ , `τ) 10 ≡ lift ([Pop] [Top]) ∷ lift [Top]  ∷ []
  test = refl

  instance
    ⊢-≅IDesc : ≅IDesc (uncurry _⊢_)
    ⊢-≅IDesc = record { W = ⊢D , ≅-transitive (≅-symmetric ≅lift) (record { from = from⊢ ; to = to⊢ ; iso₁ = ⊢-iso₁ ; iso₂ = ⊢-iso₂ }) }

  genTy : 𝔾 Ty
  genTy = ⦇ `τ ⦈ ∥ ⦇ gμ `→ gμ ⦈

  genId : 𝔾 Id
  genId = ⦇ 0 ⦈ ∥ ⦇ suc gμ ⦈

  gen⊢ : ((ix : Ctx × Ty) → IDescM 𝔾 (func.out ⊢D ix)) → (Γ : Ctx) → (τ : Ty) → 𝔾ᵢ (λ { ( Γ , τ ) → Lift 0ℓ (Γ ⊢ τ) }) (Γ , τ)
  gen⊢ m Γ τ = IDesc-isoGen (Γ , τ) m

  gen∋' : (Γ : Ctx) → (τ : Ty) → 𝔾 (Γ ∋ τ)
  gen∋' Γ τ = ⦇ lower ⟨ Γ , τ ` (uncurry (gen∋ ∋M)) ⟩ ⦈

  ⊢M : (ix : Ctx × Ty) → IDescM 𝔾 (func.out ⊢D ix)
  ⊢M (Γ , `τ)       = `σ~ (λ { ∙ → `Σ~ (gen∋' Γ `τ)  λ s → `1~ ; (▻ ∙) → `Σ~ genTy (λ s → `var~ `×~ `var~) })
  ⊢M (Γ , (σ `→ τ)) = `σ~ (λ { ∙ → `Σ~ (gen∋' Γ (σ `→ τ)) λ s → `1~ ; (▻ ∙) → `Σ~ genId (λ s → `var~) ; (▻ ▻ ∙) → `Σ~ genTy (λ s → `var~ `×~ `var~) })

  ∋-toId : ∀ {Γ τ} → Γ ∋ τ → Id
  ∋-toId {(_ , α ∶ _)} [Top] = α
  ∋-toId {.(_ , _ ∶ _)} ([Pop] mem) = ∋-toId mem

  ⊢-toTerm : ∀ {Γ τ} → Γ ⊢ τ → Tm
  ⊢-toTerm ([Var] x) = Var (∋-toId x)
  ⊢-toTerm ([Abs] tm) = Abs (ident tm) (⊢-toTerm tm)
  ⊢-toTerm ([App] tm₁ tm₂) = App (⊢-toTerm tm₁) (⊢-toTerm tm₂)

  open import Function

  test' : Data.List.map (⊢-toTerm ∘ lower) (⟨ uncurry (gen⊢ ⊢M) ⟩ᵢ (∅ , `τ `→ `τ) 3) ≡
    App (Abs 0 (Var 0)) (Abs 0 (Var 0)) ∷
    App (Abs 0 (Var 0)) (Abs 1 (Var 1)) ∷
    App (Abs 1 (Var 1)) (Abs 0 (Var 0)) ∷
    App (Abs 1 (Var 1)) (Abs 1 (Var 1)) ∷
    Abs 0 (Var 0) ∷ Abs 1 (Var 1) ∷ Abs 2 (Var 2) ∷ []
  test' = refl
