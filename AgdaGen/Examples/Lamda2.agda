module AgdaGen.Examples.Lamda2 where

  open import Data.Nat hiding (_+_; _≤_)
  open import Data.Product renaming (_,_ to _,,_)

  open import Level renaming (zero to zeroL ; suc to sucL)
  open import Relation.Binary.PropositionalEquality

  open import AgdaGen.Generic.Indexed.IDesc.Universe

  data Term : Set 0ℓ where
    tvar : ℕ → Term
    tabs : Term → Term
    tapp : Term → Term → Term

  data Type {ℓ} (A : Set ℓ) : Set ℓ where
    `_   : A → Type A
    _`→_ : Type A → Type A → Type A

  infix 30 _`→_

  data Ctx {ℓ} (A : Set ℓ) : Set ℓ where
    ∅ : Ctx A 
    _,_ : Ctx A → Type A → Ctx A

  infix 20 _,_ 

  data _∋_ {ℓ} {A : Set ℓ} : (Γ : Ctx A) → (τ : Type A) → Set ℓ where

    [Top] : ∀ {Γ τ}
            ---------- 
          → Γ , τ ∋ τ

    [Pop] : ∀ {Γ σ τ}
          → Γ ∋ τ
            ---------
          → Γ , σ ∋ τ

  infix 10 _∋_
  
  data _⊢_ {A : Set} : (Γ : Ctx A) → (τ : Type A) → Set where

    [Var] : ∀ {Γ τ}
          → Γ ∋ τ
            -------
          → Γ ⊢ τ

    [Abs] : ∀ {Γ σ τ}
          → Γ , σ ⊢ τ
            -----------
          → Γ ⊢ σ `→ τ

    [App] : ∀ {Γ σ τ}
          → Γ ⊢ σ `→ τ
            --------------
          → Γ ⊢ σ → Γ ⊢ τ
  
  infix 10 _⊢_

  ∋→ℕ : ∀ {ℓ} {A : Set ℓ} {τ} {Γ : Ctx A} → Γ ∋ τ → ℕ
  ∋→ℕ [Top]        = 0
  ∋→ℕ ([Pop] Γ∋τ)  = suc (∋→ℕ Γ∋τ)

  ⊢→Term : ∀ {A τ} {Γ : Ctx A} → Γ ⊢ τ → Term
  ⊢→Term ([Var] Γ∋τ)        = tvar (∋→ℕ Γ∋τ)
  ⊢→Term ([Abs] Γ⊢τ)        = tabs (⊢→Term Γ⊢τ)
  ⊢→Term ([App] Γ⊢τ₁ Γ⊢τ₂)  = tapp (⊢→Term Γ⊢τ₁) (⊢→Term Γ⊢τ₂)

  ⊢-Desc : ∀ {ℓ} {A : Set ℓ} → (Ctx A × Type A) → IDesc ℓ (Ctx A × Type A)
  ⊢-Desc {A = A} (Γ ,, τ) = `σ 3 λ
    { ∙       → `Σ (Γ ∋ τ) λ _ → `1 
    ; (▻ ∙)   → `Σ (Σ[ ts ∈ (Type A × Type A) ] τ ≡ proj₁ ts `→ proj₂ ts)
                   λ { ((σ ,, τ') ,, refl) → `var (Γ , σ ,, τ') }
    ; (▻ ▻ ∙) → `Σ (Type A) λ σ → `var (Γ ,, σ `→ τ) `× `var (Γ ,, σ)
    }

  open import Data.Bool hiding (_∧_; _∨_; if_then_else_)

  module _ where
  
    data Ty : Set where
      bool : Ty
      nat  : Ty

    ⟦_⟧ty : Ty → Set
    ⟦ bool ⟧ty = Bool 
    ⟦ nat  ⟧ty = ℕ
  
    data Ex : Ty → Set 0ℓ where
      _∧_           : Ex bool → Ex bool → Ex bool
      _∨_           : Ex bool → Ex bool → Ex bool
      if_then_else_ : ∀ {A} → Ex bool → Ex A → Ex A → Ex A
      val           : ∀ {A} → ⟦ A ⟧ty → Ex A
      _+_           : Ex nat → Ex nat → Ex nat
      _≤_           : Ex nat → Ex nat → Ex bool

    and : Bool → Bool → Bool
    and true true = true
    and _    _    = false

    or  : Bool → Bool → Bool
    or false false = false
    or _     _     = true

    add : ℕ → ℕ → ℕ
    add zero m = m
    add (suc n) m = suc (add n m)

    leq : ℕ → ℕ → Bool
    leq zero m = true
    leq (suc n) zero = false
    leq (suc n) (suc m) = leq n m

    eval : ∀ {ty} → Ex ty → ⟦ ty ⟧ty 
    eval (e₁ ∧ e₂) = and (eval e₁) (eval e₂)
    eval (e₁ ∨ e₂) = or (eval e₁) (eval e₂)
    eval (if g then t else e) with eval g
    ... | true  = eval t 
    ... | false = eval e
    eval (val x) = x
    eval (e₁ + e₂) = add (eval e₁) (eval e₂)
    eval (e₁ ≤ e₂) = leq (eval e₁) (eval e₂)
    
    ExD : Ty → IDesc 0ℓ Ty
    ExD ty = `σ 6 λ
      { ∙             → `Σ (ty ≡ bool) λ { refl → `var bool `× `var bool }
      ; (▻ ∙)         → `Σ (ty ≡ bool) λ { refl → `var bool `× `var bool }
      ; (▻ ▻ ∙)       → `var bool `× `var ty `× `var ty
      ; (▻ ▻ ▻ ∙)     → `Σ ⟦ ty ⟧ty λ _ → `1
      ; (▻ ▻ ▻ ▻ ∙)   → `Σ (ty ≡ nat) λ { refl → `var nat `× `var nat }
      ; (▻ ▻ ▻ ▻ ▻ ∙) → `Σ (ty ≡ nat) λ { refl → `var nat `× `var nat }
      }

   
    
    
