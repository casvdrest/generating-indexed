open import src.Data hiding (_∈_; Σ)
open import src.Gen.Base
open import src.Gen.Indexed.Examples
open import src.Gen.Regular.Examples

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

module src.Gen.Indexed.Lambda where

  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawMonad ⦃...⦄ using (_>>_; _>>=_; return; pure)

  Id : Set
  Id = ℕ
  
  data Ty : Set where
    `ℕ    : Ty
    _`→_  : Ty → Ty → Ty

  type : ⟪ 𝔾 Ty ⟫
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
    _,_∶_ : Env → Id → Ty → Env

  data _[_↦_] : Env → Id → Ty → Set where
  
    TOP : ∀ {Γ α τ}
          -----------------------------
        →  (Γ , α ∶ τ) [ α ↦ τ ] 

    POP : ∀ {Γ α β τ σ} → Γ [ α ↦ τ ]
          ---------------------------------                              
        → (Γ , β ∶ σ) [ α ↦ τ ] 


  data Tm : Set where
    $_  : Id → Tm
    Λ_⇒_ : Id → Tm → Tm
    _∙_  : Tm → Tm → Tm
    let`_:=_in`_ : Id → Tm → Tm → Tm

  data _⊢_∶_ (Γ : Env) : Tm → Ty → Set where

    VAR : ∀ {α τ} → Γ [ α ↦ τ ]
          ---------------------
        → Γ ⊢ $ α ∶ τ

    
    ABS : ∀ {α τ σ t} → (Γ , α ∶ σ) ⊢ t ∶ τ
          ----------------------------------
        → Γ ⊢ Λ α ⇒ t ∶ (σ `→ τ)

    
    APP : ∀ {t₁ t₂ τ σ} → Γ ⊢ t₁ ∶ (σ `→ τ) → Γ ⊢ t₂ ∶ σ
          ------------------------------------------------
        → Γ ⊢ t₁ ∙ t₂ ∶ τ

    
    LET : ∀ {t₁ t₂ α τ σ} → Γ ⊢ t₁ ∶ τ → (Γ , α ∶ τ) ⊢ t₂ ∶ σ
          -----------------------------------------------------
        → Γ ⊢ let` α := t₁ in` t₂ ∶ σ
          

  Γ-match : (τ : Ty) → ⟪ 𝔾ᵢ (λ Γ → Σ[ α ∈ Id ] Γ [ α ↦ τ ]) ⟫
  Γ-match τ μ ∅ = uninhabited
  Γ-match τ μ (Γ , α ∶ σ) with τ ≟ σ
  Γ-match τ μ (Γ , α ∶ τ) | yes refl = ⦇ (α , TOP)         ⦈
                                     ∥ ⦇ (Σ-map POP) (μ Γ) ⦈
  Γ-match τ μ (Γ , α ∶ σ) | no ¬p    = ⦇ (Σ-map POP) (μ Γ) ⦈

  Γ-lookup : (α : Id) → ⟪ 𝔾ᵢ (λ Γ → Σ[ τ ∈ Ty ] Γ [ α ↦ τ ]) ⟫
  Γ-lookup α μ ∅ = uninhabited
  Γ-lookup α μ (Γ , β ∶ τ) with Data.Nat._≟_ α β
  Γ-lookup α μ (Γ , .α ∶ τ) | yes refl = ⦇ (τ , TOP) ⦈
  Γ-lookup α μ (Γ , β ∶ τ) | no ¬p = ⦇ (Σ-map POP) (μ Γ) ⦈

  fresh : Id → Env → Id
  fresh α ∅ = suc α
  fresh α (Γ , β ∶ τ) = fresh (α ⊔ β) Γ

  λ-calculus : ⟪ 𝔾ᵢ (λ p → Σ[ t ∈ Tm ] (snd p) ⊢ t ∶ (fst p) ) ⟫
  
  λ-calculus μ (`ℕ , Γ') = ⦇ (Σ-bimap $_ VAR) ( ⟨ Γ-match `ℕ ⟩ᵢ Γ') ⦈
                         ∥ ( do σ ← ⟨ type ⟩
                                t₁ ← μ (σ `→ `ℕ , Γ')
                                t₂ ← μ (σ , Γ')
                                return (Σ₁ t₁ ∙ Σ₁ t₂ , APP (Σ₂ t₁) (Σ₂ t₂)))
                         ∥ ( do let α = fresh 0 Γ'
                                σ ← ⟨ type ⟩
                                lt ← μ (σ , Γ')
                                bd ← μ (`ℕ , (Γ' , α ∶ σ))
                                return ((let` α := Σ₁ lt in` Σ₁ bd) , LET (Σ₂ lt) (Σ₂ bd)) )
  
  λ-calculus μ (τ `→ τ₁ , Γ') = ( do let α = fresh 0 Γ'
                                     t ← (μ (τ₁ , (Γ' , α ∶ τ)))
                                     return (Λ α ⇒ Σ₁ t , ABS (Σ₂ t)) )
                              ∥ ( do let α = fresh 0 Γ'
                                     σ ← ⟨ type ⟩
                                     lt ← μ (σ , Γ')
                                     bd ← μ (τ `→ τ₁ , (Γ' , α ∶ σ))
                                     return ((let` α := Σ₁ lt in` Σ₁ bd) , LET (Σ₂ lt) (Σ₂ bd)) )
  

  λ-calculus' : ⟪ 𝔾ᵢ (λ p → Σ[ τ ∈ Ty ] (snd p ⊢ fst p ∶ τ)) ⟫
  λ-calculus' = 〖 `VAR ⋎ `ABS ⋎ `APP ⋎ `LET 〗
    
    where `VAR : ⟪ 𝔾ᵢ (λ i → Σ[ τ ∈ Ty ] (snd i ⊢ fst i ∶ τ)) ⟫
          `VAR μ (($ x) , Γ) = ⦇ (Σ-map VAR) (⟨ Γ-lookup x ⟩ᵢ Γ) ⦈
          `VAR μ _ = uninhabited

          `ABS : ⟪ 𝔾ᵢ (λ i → Σ[ τ ∈ Ty ] (snd i ⊢ fst i ∶ τ)) ⟫
          `ABS μ (Λ α ⇒ t , Γ) = do σ  ← ⟨ type ⟩
                                    bd ← μ (t , (Γ , α ∶ σ)) 
                                    return ((σ `→ Σ₁ bd) , ABS (Σ₂ bd))
          `ABS μ _ = uninhabited 

          `APP : ⟪ 𝔾ᵢ (λ i → Σ[ τ ∈ Ty ] (snd i ⊢ fst i ∶ τ)) ⟫
          `APP μ (t₁ ∙ t₂ , Γ) = do f ← μ (t₁ , Γ)
                                    x ← μ (t₂ , Γ)
                                    app-match f x
            where app-match : ∀ {n : ℕ} → Σ[ τ₁ ∈ Ty ] (Γ ⊢ t₁ ∶ τ₁) → Σ[ τ₂ ∈ Ty ] (Γ ⊢ t₂ ∶ τ₂) → 𝔾 (Σ[ τ ∈ Ty ] Γ ⊢ t₁ ∙ t₂ ∶ τ) n
                  app-match (`ℕ , prf₁) (τ₂ , prf₂) = uninhabited
                  app-match ((τ₁ `→ τ₃) , prf₁) (τ₂ , prf₂) with τ₁ ≟ τ₂
                  app-match ((τ₁ `→ τ₃) , prf₁) (.τ₁ , prf₂) | yes refl = ⦇ (τ₃ , APP prf₁ prf₂) ⦈
                  app-match ((τ₁ `→ τ₃) , prf₁) (τ₂ , prf₂) | no ¬p = uninhabited
          `APP μ _ = uninhabited

          `LET : ⟪ 𝔾ᵢ (λ i → Σ[ τ ∈ Ty ] (snd i ⊢ fst i ∶ τ)) ⟫
          `LET μ (let` α := t₁ in` t₂ , Γ) = do bn ← μ (t₁ , Γ)
                                                bd ← μ (t₂ , (Γ , α ∶ (Σ₁ bn)))
                                                return (Σ₁ bd , LET (Σ₂ bn) (Σ₂ bd))
          `LET μ _ = uninhabited
 

