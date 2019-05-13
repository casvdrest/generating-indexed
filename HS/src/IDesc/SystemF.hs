{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module IDesc.SystemF where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Data.Singletons
  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics

  import IDesc.IDesc
  import IDesc.Instances

  ----------------------------------------------------------------------------
  -- Polymorphic well typed terms  

  type Id = String

  data Ty = TyVar Id | Ty :->: Ty | Forall Id Ty deriving (Show , Eq)

  data Ctx = CtxEmpty | CtxCons Id Ty Ctx deriving (Show , Eq)

  ctxFromList :: [(Id , Ty)] -> Ctx
  ctxFromList []           = CtxEmpty
  ctxFromList ((id,ty):xs) = CtxCons id ty (ctxFromList xs)

  {-
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

  -}

  l2Func :: Func (Term String) (Ctx , Ty)
  l2Func (ctx , ty) = SSuc (SSuc (SSuc (SSuc (SSuc SZero)))) :+>
    (   undefined
    ::: undefined
    ::: undefined
    ::: undefined
    ::: undefined
    ::: VNil
    )
