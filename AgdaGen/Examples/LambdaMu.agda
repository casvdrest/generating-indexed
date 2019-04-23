open import Data.Nat

open import AgdaGen.Base
open import AgdaGen.Combinators
open import Data.Product

open import AgdaGen.Generic.Indexed.IDesc.Universe

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Level renaming (zero to zeroL ; suc to sucL)

module AgdaGen.Examples.LambdaMu where

  Id : Set
  Id = ℕ

  data Ty : Set where
    `τ   : Ty
    _`→_ : Ty → Ty → Ty

  data Ctx : Set where
    ∅ : Ctx
    _,_∶_ : Ctx → Id → Ty → Ctx

  mutual
    data M : Set where
      var  : Id → M
      abs  : Id → M → M
      app  : M → M → M
      μ_▸_ : Id → C → M
  
    data C : Set where
      [_]_ : Id → M → C

  mutual
    data _⊢_∣_ : Ctx → Ty → Ctx → Set where
    
      [Var]   : ∀ {Γ x τ Δ}
                ---------------------
                → (Γ , x ∶ τ) ⊢ τ ∣ Δ

      [App]   : ∀ {Γ τ σ Δ} → Γ ⊢ σ `→ τ ∣ Δ → Γ ⊢ σ ∣ Δ
                -----------------------------------------
                → Γ ⊢ τ ∣ Δ

      [Abs]   : ∀ {Γ x σ τ Δ} → (Γ , x ∶ σ) ⊢ τ ∣ Δ
                -----------------------------------
                → Γ ⊢ σ `→ τ ∣ Δ

      [Deref] : ∀ {Γ c β τ Δ} → c ∶ Γ ⊢ (Δ , β ∶ τ)
                ------------------------------------
                → Γ ⊢ τ ∣ Δ

    data _∶_⊢_ : C → Ctx → Ctx → Set where
    
      [Ref] : ∀ {Γ t τ α Δ} → Γ ⊢ τ ∣ Δ
              -----------------------------
              → ([ α ] t) ∶ Γ ⊢ (Δ , α ∶ τ) 

  
  MDesc : func 0ℓ (Ctx × Ty × Ctx) (Ctx × Ty × Ctx)
  MDesc = func.mk λ
    { (Γ , `τ , Δ) →
         `σ 3 λ {
            ∙      → `1
         ; (▻ ∙)   → `Σ Ty λ { σ → `var (Γ , (σ `→ `τ) , Δ) `× `var (Γ , σ , Δ) }
         ; (▻ ▻ ∙) → `Σ Id (λ β → `Σ C (λ c → `Σ (c ∶ Γ ⊢ (Δ , β ∶ `τ)) λ _ → `1))
         }
    ; (Γ , (τ `→ σ) , Δ) →
         `σ 4 λ {
            ∙        → `1
         ; (▻ ∙)     → `Σ Ty λ { σ → `var (Γ , (σ `→ `τ) , Δ) `× `var (Γ , σ , Δ) }
         ; (▻ ▻ ∙)   → `Σ Id λ x → `var ((Γ , x ∶ σ) , τ , Δ)
         ; (▻ ▻ ▻ ∙) → `Σ Id (λ β → `Σ C (λ c → `Σ (c ∶ Γ ⊢ (Δ , β ∶ `τ)) λ _ → `1)) 
         }
    }

  CDesc : func 0ℓ (C × Ctx × Ctx) (C × Ctx × Ctx)
  CDesc = func.mk λ
    { ([ α ] t , Γ , (Δ , β ∶ τ)) → `Σ (α ≡ β) (λ { refl → `Σ (Γ ⊢ τ ∣ Δ) λ _ → `1 })
    ; ([ α ] t , Γ , ∅) → `σ 0 λ()
    } 
