open import src.Data hiding (_∈_; Σ)
open import src.Gen.Base
open import src.Gen.Indexed
open import src.Gen.Examples

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

module src.Gen.Lambda where

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
    _↦_∷_ : Id → Ty → Env → Env

  data _[_↦_] : Env → Id → Ty → Set where
  
    TOP : ∀ {Γ α τ}
          -----------------------------
        → (α ↦ τ ∷ Γ) [ α ↦ τ ] 

    POP : ∀ {Γ α β τ σ} → Γ [ α ↦ τ ]
          ---------------------------------                              
        → (β ↦ σ ∷ Γ) [ α ↦ τ ] 

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
          ---------------------
        → Γ ⊢ $ α ∶ τ

    
    ABS : ∀ {α τ σ t} → (α ↦ σ ∷ Γ) ⊢ t ∶ τ
          ----------------------------------
        → Γ ⊢ Λ α ⇒ t ∶ (σ `→ τ)

    
    APP : ∀ {t₁ t₂ τ σ} → Γ ⊢ t₁ ∶ (σ `→ τ) → Γ ⊢ t₂ ∶ σ
          ------------------------------------------------
        → Γ ⊢ t₁ ∙ t₂ ∶ τ

    
    LET : ∀ {t₁ t₂ α τ σ} → Γ ⊢ t₁ ∶ τ → (α ↦ τ ∷ Γ) ⊢ t₂ ∶ σ
          -----------------------------------------------------
        → Γ ⊢ let` α := t₁ in` t₂ ∶ σ
          

  Γ-match : (τ : Ty) → ⟪ 𝔾ᵢ (λ Γ → Σ[ α ∈ Id ] Γ [ α ↦ τ ]) ⟫
  Γ-match τ μ ∅ = uninhabited
  Γ-match τ μ (α ↦ σ ∷ Γ) with τ ≟ σ
  Γ-match τ μ (α ↦ τ ∷ Γ) | yes refl = ⦇ (α , TOP)         ⦈
                                     ∥ ⦇ (Σ-map POP) (μ Γ) ⦈
  Γ-match τ μ (α ↦ σ ∷ Γ) | no ¬p    = ⦇ (Σ-map POP) (μ Γ) ⦈

  Γ-lookup : (α : Id) → ⟪ 𝔾ᵢ (λ Γ → Σ[ τ ∈ Ty ] Γ [ α ↦ τ ]) ⟫
  Γ-lookup α μ ∅ = uninhabited
  Γ-lookup α μ (β ↦ τ ∷ Γ) with Data.Nat._≟_ α β
  Γ-lookup α μ (.α ↦ τ ∷ Γ) | yes refl = ⦇ (τ , TOP) ⦈
  Γ-lookup α μ (β ↦ τ ∷ Γ) | no ¬p = ⦇ (Σ-map POP) (μ Γ) ⦈

  fresh : Id → Env → Id
  fresh α ∅ = suc α
  fresh α (β ↦ τ ∷ Γ) = fresh (α ⊔ β) Γ

  λ-calculus : ⟪ 𝔾ᵢ (λ p → Σ[ t ∈ Tm ] (snd p) ⊢ t ∶ (fst p) ) ⟫
  
  λ-calculus μ (`ℕ , Γ') = ⦇ (Σ-bimap $_ VAR) ( ⟨ Γ-match `ℕ ⟩ᵢ Γ') ⦈
                         ∥ ( do σ ← ⟨ type ⟩
                                t₁ ← μ (σ `→ `ℕ , Γ')
                                t₂ ← μ (σ , Γ')
                                return (Σ₁ t₁ ∙ Σ₁ t₂ , APP (Σ₂ t₁) (Σ₂ t₂)))
                         ∥ ( do let α = fresh 0 Γ'
                                σ ← ⟨ type ⟩
                                lt ← μ (σ , Γ')
                                bd ← μ (`ℕ , (α ↦ σ ∷ Γ'))
                                return ((let` α := Σ₁ lt in` Σ₁ bd) , LET (Σ₂ lt) (Σ₂ bd)) )
  
  λ-calculus μ (τ `→ τ₁ , Γ') = ( do let α = fresh 0 Γ'
                                     t ← (μ (τ₁ , (α ↦ τ ∷ Γ')))
                                     return (Λ α ⇒ Σ₁ t , ABS (Σ₂ t)) )
                              ∥ ( do let α = fresh 0 Γ'
                                     σ ← ⟨ type ⟩
                                     lt ← μ (σ , Γ')
                                     bd ← μ (τ `→ τ₁ , (α ↦ σ ∷ Γ'))
                                     return ((let` α := Σ₁ lt in` Σ₁ bd) , LET (Σ₂ lt) (Σ₂ bd)) )
  

  λ-calculus' : ⟪ 𝔾ᵢ (λ p → Σ[ τ ∈ Ty ] (snd p ⊢ fst p ∶ τ)) ⟫
  λ-calculus' = 〖 `VAR ⋎ `ABS ⋎ `APP ⋎ `LET 〗
    
    where `VAR : ⟪ 𝔾ᵢ (λ i → Σ[ τ ∈ Ty ] (snd i ⊢ fst i ∶ τ)) ⟫
          `VAR μ (($ x) , Γ) = ⦇ (Σ-map VAR) (⟨ Γ-lookup x ⟩ᵢ Γ) ⦈
          `VAR μ _ = uninhabited

          `ABS : ⟪ 𝔾ᵢ (λ i → Σ[ τ ∈ Ty ] (snd i ⊢ fst i ∶ τ)) ⟫
          `ABS μ (Λ α ⇒ t , Γ) = do σ  ← ⟨ type ⟩
                                    bd ← μ (t , (α ↦ σ ∷ Γ)) 
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
                                                bd ← μ (t₂ , (α ↦ Σ₁ bn ∷ Γ))
                                                return (Σ₁ bd , LET (Σ₂ bn) (Σ₂ bd))
          `LET μ _ = uninhabited

  λ-test1 : 𝔾-runᵢ λ-calculus (`ℕ `→ `ℕ , 0 ↦ `ℕ ∷ ∅) 4
    ≡ (Λ 1 ⇒ $ 1 , ABS (VAR TOP)) ∷
      (let` 1 := $ 0 in` Λ 2 ⇒ $ 2 , LET (VAR TOP) (ABS (VAR TOP))) ∷
      (Λ 1 ⇒ let` 2 := $ 1 in` $ 2 , ABS (LET (VAR TOP) (VAR TOP))) ∷
      (let` 1 := (let` 1 := $ 0 in` $ 1) in` Λ 2 ⇒ $ 2 , LET (LET (VAR TOP) (VAR TOP)) (ABS (VAR TOP))) ∷
      (Λ 1 ⇒ $ 0 , ABS (VAR (POP TOP))) ∷
      (let` 1 := (Λ 1 ⇒ $ 1) in` (Λ 2 ⇒ $ 2) , LET (ABS (VAR TOP)) (ABS (VAR TOP))) ∷ []
  λ-test1 = refl
  
  λ-test'1 : 𝔾-runᵢ λ-calculus' ($ 0 , 0 ↦ `ℕ ∷ ∅) 2 ≡ ((`ℕ , VAR TOP) ∷ [])
  λ-test'1 = refl

  λ-test'2 : 𝔾-runᵢ λ-calculus' ((Λ 0 ⇒ $ 0) ∙ ($ 0) , 0 ↦ `ℕ ∷ ∅) 4 ≡ (`ℕ , APP (ABS (VAR TOP)) (VAR TOP)) ∷ []
  λ-test'2 = refl

  λ-test'3 : take 5 (𝔾-runᵢ λ-calculus' (Λ 0 ⇒ (Λ 1 ⇒ (($ 0) ∙ ($ 1))) , ∅) 6)
    ≡ (((`ℕ `→ `ℕ) `→ (`ℕ `→ `ℕ)) , ABS (ABS (APP (VAR (POP TOP)) (VAR TOP)))) ∷
      (((`ℕ `→ (`ℕ `→ `ℕ)) `→ (`ℕ `→ (`ℕ `→ `ℕ))) , (ABS (ABS (APP (VAR (POP TOP)) (VAR TOP))))) ∷
      (((`ℕ `→ (`ℕ `→ (`ℕ `→ `ℕ))) `→ (`ℕ `→ (`ℕ `→ (`ℕ `→ `ℕ)))) , (ABS (ABS (APP (VAR (POP TOP)) (VAR TOP))))) ∷
      (((`ℕ `→ (`ℕ `→ (`ℕ `→ (`ℕ `→ `ℕ)))) `→ (`ℕ `→ (`ℕ `→ (`ℕ `→ (`ℕ `→ `ℕ))))) , (ABS (ABS (APP (VAR (POP TOP)) (VAR TOP))))) ∷
      (((`ℕ `→ (`ℕ `→ ((`ℕ `→ `ℕ) `→ `ℕ))) `→ (`ℕ `→ (`ℕ `→ ((`ℕ `→ `ℕ) `→ `ℕ)))) , (ABS (ABS (APP (VAR (POP TOP)) (VAR TOP))))) ∷ []
  λ-test'3 = refl
 
