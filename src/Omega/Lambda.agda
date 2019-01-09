open import src.Data hiding (_∈_; Σ)
open import src.Omega.Base
open import src.Omega.Indexed
open import src.Omega.Examples

open import Data.Nat hiding (_≟_)
open import Data.List
open import Data.Fin hiding (_≟_)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Relation.Nullary
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Function

module src.Omega.Lambda where

  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawMonad ⦃...⦄ using (_>>_; _>>=_; return; pure)

  data Tmᵤ : Set where
    varᵤ : ℕ → Tmᵤ
    absᵤ : Tmᵤ → Tmᵤ 
    appᵤ : Tmᵤ → Tmᵤ → Tmᵤ 

  Tmu : ω ℕ → ⟪ ω Tmᵤ ⟫
  Tmu n μ = ⦇ varᵤ n   ⦈
          ∥ ⦇ absᵤ μ   ⦈
          ∥ ⦇ appᵤ μ μ ⦈

  Tmᵤ-prop : fix (Tmu (κ (fix nats))) 4
    ≡ varᵤ zero ∷ absᵤ (varᵤ zero) ∷ varᵤ 1 ∷ appᵤ (varᵤ zero) (varᵤ zero) ∷ []
  Tmᵤ-prop = refl

  data Tmₛ : ℕ → Set where
    varₛ : ∀ {n : ℕ} → Fin n → Tmₛ n
    absₛ : ∀ {n : ℕ} → Tmₛ (suc n) → Tmₛ n
    appₛ : ∀ {n : ℕ} → Tmₛ n → Tmₛ n → Tmₛ n

  Tms : ωᵢ Fin → ⟪ ωᵢ Tmₛ ⟫
  Tms fin μ d = ⦇ varₛ (κ (fin d)) ⦈
              ∥ ⦇ absₛ (μ (suc d)) ⦈
              ∥ ⦇ appₛ (μ d) (μ d) ⦈

  Tmₛ-prop : fixᵢ (Tms (fixᵢ fin)) 0 5
    ≡ absₛ (varₛ zero) ∷
      appₛ (absₛ (varₛ zero)) (absₛ (varₛ zero)) ∷
      absₛ (absₛ (varₛ zero)) ∷
      absₛ (appₛ (varₛ zero) (varₛ zero)) ∷ []
  Tmₛ-prop = refl

  Id : Set
  Id = ℕ
  
  data Ty : Set where
    `ℕ    : Ty
    _`→_  : Ty → Ty → Ty

  type : ⟪ ω Ty ⟫
  type μ = ⦇ `ℕ ⦈ ∥ ⦇ μ `→ μ ⦈

  →-left-neq : ∀ {τ₁ τ₂ τ₃ τ₄ : Ty} → ¬ τ₁ ≡ τ₂
               --------------------------------
               → ¬ τ₁ `→ τ₃ ≡ τ₂ `→ τ₄
  →-left-neq contra refl = contra refl

  →-right-neq : ∀ {τ₁ τ₂ τ₃ τ₄ : Ty} → ¬ τ₃ ≡ τ₄
                --------------------------------
                → ¬ τ₁ `→ τ₃ ≡ τ₂ `→ τ₄
  →-right-neq contra refl = contra refl

  _≟_ : Decidable {A = Ty} _≡_
  `ℕ ≟ `ℕ = yes refl
  `ℕ ≟ (τ₂ `→ τ₃) = no λ()
  (τ₁ `→ τ₃) ≟ `ℕ = no λ()
  (τ₁ `→ τ₃) ≟ (τ₂ `→ τ₄) with τ₁ ≟ τ₂
  ((τ₁ `→ τ₃) ≟ (τ₂ `→ τ₄)) | yes p with τ₃ ≟ τ₄
  ((τ₁ `→ τ₃) ≟ (.τ₁ `→ .τ₃)) | yes refl | yes refl = yes refl
  ((τ₁ `→ τ₃) ≟ (τ₂ `→ τ₄)) | yes p | no ¬p = no (→-right-neq ¬p)
  ((τ₁ `→ τ₃) ≟ (τ₂ `→ τ₄)) | no ¬p = no (→-left-neq ¬p)

  data Env : Set where
    ∅     : Env
    _↦_∷_ : Id → Ty → Env → Env

  data _[_↦_] : Env → Id → Ty → Set where
  
    TOP : ∀ {Γ α τ}
          -----------------------------
          → (α ↦ τ ∷ Γ) [ α ↦ τ ] 

    POP :   ∀ {Γ α β τ σ} → Γ [ α ↦ τ ]
          → ---------------------------------                              
            (β ↦ σ ∷ Γ) [ α ↦ τ ] 

  _⋈_ : Env → Env → Env
  ∅ ⋈ Γ₂ = Γ₂
  (α ↦ τ ∷ Γ₁) ⋈ Γ₂ = α ↦ τ ∷ (Γ₁ ⋈ Γ₂)

  data Tm : Set where
    $_  : Id → Tm
    Λ_⇒_ : Id → Tm → Tm
    _∙_  : Tm → Tm → Tm
    let`_:=_in`_ : Id → Tm → Tm → Tm

  data _⊢_∶_ (Γ : Env) : Tm → Ty → Set where

    VAR : ∀ {α τ} → Γ [ α ↦ τ ]
          -----------------------
          → Γ ⊢ $ α ∶ τ

    
    ABS : ∀ {α τ σ t} → (α ↦ σ ∷ Γ) ⊢ t ∶ τ
          ----------------------------------
          → Γ ⊢ Λ α ⇒ t ∶ (σ `→ τ)

    
    APP : ∀ {t₁ t₂ τ σ} → Γ ⊢ t₁ ∶ (σ `→ τ) → Γ ⊢ t₂ ∶ σ
          ------------------------------------------------
          → Γ ⊢ t₁ ∙ t₂ ∶ τ

    {-
    LET : ∀ {t₁ t₂ α τ σ} → Γ ⊢ t₁ ∶ τ → (α ↦ τ ∷ Γ) ⊢ t₂ ∶ σ
          -----------------------------------------------------
          → Γ ⊢ let` α := t₁ in` t₂ ∶ σ
    -}

  Γ-match : (τ : Ty) → ⟪ ( ωᵢ λ Γ → (Σ[ α ∈ Id ] Γ [ α ↦ τ ]) ) ⟫
  Γ-match τ μ ∅ = uninhabited
  Γ-match τ μ (α ↦ σ ∷ Γ) with τ ≟ σ
  Γ-match τ μ (α ↦ τ ∷ Γ) | yes refl = ⦇ (α , TOP)         ⦈
                                     ∥ ⦇ (Σ-map POP) (μ Γ) ⦈
  Γ-match τ μ (α ↦ σ ∷ Γ) | no ¬p    = ⦇ (Σ-map POP) (μ Γ) ⦈

  fresh : Id → Env → Id
  fresh α ∅ = suc α
  fresh α (β ↦ τ ∷ Γ) = fresh (α ⊔ β) Γ

  λ-calculus : ⟪ ( ωᵢ λ p → Σ[ t ∈ Tm ] (snd p) ⊢ t ∶ (fst p) ) ⟫
  
  λ-calculus μ (`ℕ , Γ') = ⦇ (Σ-bimap $_ VAR) ( ⟨ Γ-match `ℕ ⟩ᵢ Γ') ⦈ ∥ 
    do σ ← ⟨ type ⟩
       t₁ ← μ (σ `→ `ℕ , Γ')
       t₂ ← μ (σ , Γ')
       return (Σ₁ t₁ ∙ Σ₁ t₂ , APP (Σ₂ t₁) (Σ₂ t₂)) 
  
  λ-calculus μ (τ `→ τ₁ , Γ') = 
    do let α = fresh 0 Γ'
       t ← (μ (τ₁ , (α ↦ τ ∷ Γ')))
       return (Λ α ⇒ Σ₁ t , ABS (Σ₂ t))

  λ-test : ⟨ λ-calculus ⟩ᵢ (`ℕ `→ `ℕ , 0 ↦ `ℕ ∷ ∅) 5 ≡
    ((Λ 1 ⇒ $ 1) , ABS (VAR TOP)) ∷                                                     -- [n ↦ ℕ] ⊢ λ x → x : ℕ → ℕ
    (Λ 1 ⇒ ((Λ 2 ⇒ ($ 2)) ∙ ($ 1)) , ABS (APP (ABS (VAR TOP)) (VAR TOP))) ∷             -- [n ↦ ℕ] ⊢ λ x → (λ y → y) x : ℕ → ℕ
    ((Λ 1 ⇒ $ 0) , ABS (VAR (POP TOP))) ∷                                               -- [n ↦ ℕ] ⊢ λ x → n : ℕ → ℕ
    ((Λ 1 ⇒ ((Λ 2 ⇒ ($ 2)) ∙ ($ 0))) , ABS (APP (ABS (VAR TOP)) (VAR (POP TOP) ))) ∷ [] -- [n ↦ ℕ] ⊢ λ x → (λ y → y) n : ℕ → ℕ
  λ-test = refl

