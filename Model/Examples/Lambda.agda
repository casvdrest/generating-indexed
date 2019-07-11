open import AgdaGen.Base
open import AgdaGen.Data hiding (_∈_; Σ)
open import AgdaGen.Combinators

open import Data.Nat hiding (_≟_)
open import Data.List
open import Data.Fin hiding (_≟_)
open import Data.Product
open import Data.Unit hiding (_≟_)

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Relation.Nullary
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Function hiding (_∋_)
open import Level hiding (suc; zero)

module AgdaGen.Examples.Lambda where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
  open GMonad       ⦃...⦄

  -- Variable names are natural numbers
  Id : Set
  Id = ℕ

  -- Type of types in SLC 
  data Ty : Set where
    `ℕ    : Ty
    _`→_  : Ty → Ty → Ty

  -- Generator for types
  type : ⊤ → 𝔾ᵢ (λ { tt → Ty }) tt
  type tt = ⦇ `ℕ ⦈ ∥ ⦇ (μᵢ tt) `→ (μᵢ tt) ⦈

  -- Generator for identifiers
  ident : ⊤ → 𝔾ᵢ (λ { tt → Id }) tt
  ident tt = ⦇ zero ⦈
           ∥ (⦇ suc (μᵢ tt) ⦈)

  -- Decidable equality for types
  _≟_ : Decidable {A = Ty} _≡_
  `ℕ ≟ `ℕ = yes refl
  `ℕ ≟ (τ₂ `→ τ₃) = no λ()
  (τ₁ `→ τ₃) ≟ `ℕ = no λ()
  (τ₁ `→ τ₃) ≟ (τ₂ `→ τ₄) with τ₁ ≟ τ₂
  ((τ₁ `→ τ₃) ≟ (τ₂ `→ τ₄))
    | yes p with τ₃ ≟ τ₄
  ((τ₁ `→ τ₃) ≟ (.τ₁ `→ .τ₃))
    | yes refl | yes refl = yes refl
  ((τ₁ `→ τ₃) ≟ (τ₂ `→ τ₄))
    | yes p | no ¬p = no λ { refl → ¬p refl }
  ((τ₁ `→ τ₃) ≟ (τ₂ `→ τ₄))
    | no ¬p = no λ { refl → ¬p refl }

  -- λ-term context
  data Ctx : Set where
    ∅     : Ctx
    _,_∶_ : Ctx → Id → Ty → Ctx

  infix 2 _∋_

  -- Context membership
  data _∋_ : Ctx → Ty → Set where
  
    [Top] : ∀ {Γ τ α}
          ---------------
          → Γ , α ∶ τ ∋ τ
          
    [Pop] : ∀ {Γ τ σ β} → Γ ∋ τ
            -------------------
            → Γ , β ∶ σ ∋ τ

  -- Generates all proofs of some input context
  -- having a member of some input type.
  ∋-gen : (ix : Ctx × Ty)
        → 𝔾ᵢ (λ { ( Γ , τ ) → Γ ∋ τ }) ix
  ∋-gen (∅ , τ) = Noneᵢ
  ∋-gen ((Γ , α ∶ σ) , τ) with τ ≟ σ
  ∋-gen ((Γ , α ∶ σ) , .σ) | yes refl =
      ⦇ [Top] ⦈
    ∥ ⦇ [Pop] (μᵢ (Γ , σ)) ⦈
  ∋-gen ((Γ , α ∶ σ) , τ)  | no ¬p    =
    ⦇ [Pop] (μᵢ (Γ , τ)) ⦈

  ∋→Id : ∀ {Γ : Ctx} {τ : Ty} → Γ ∋ τ → Id
  ∋→Id {(_ , α ∶ _)} [Top]     = α
  ∋→Id {(Γ , β ∶ σ)} ([Pop] p) = ∋→Id p

  -- Type of λ-terms
  data Tm : Set where
    $_  : Id → Tm
    Λ_⇒_ : Id → Tm → Tm
    _⊚_  : Tm → Tm → Tm

  infix 1 _⊢_

  -- Typing judgements
  data _⊢_ (Γ : Ctx) : Ty → Set where
  
    [Var] : ∀ {τ} → Γ ∋ τ
            -------------
            → Γ ⊢ τ
            
    [Abs] : ∀ {α τ σ} → Γ , α ∶ σ ⊢ τ
            -------------------------
            → Γ ⊢ σ `→ τ
            
    [App] : ∀ {τ σ} → Γ ⊢ σ `→ τ → Γ ⊢ σ
            ----------------------------
            → Γ ⊢ τ 

  -- Generates all type correct terms for a given 
  -- input context and type
  ⊢-gen : (ix : Ctx × Ty)
        → 𝔾ᵢ (λ { ( Γ , τ ) → Γ ⊢ τ }) ix 
  ⊢-gen (Γ , `ℕ) =
       ⦇ [Var] (Callᵢ {x = Γ , `ℕ} ∋-gen (Γ , `ℕ)) ⦈
    ∥ ( do σ ← Callᵢ {x = Γ , `ℕ} type tt
           t₁ ← μᵢ (Γ , (σ `→ `ℕ))
           t₂ ← μᵢ (Γ , σ)
           pure ([App] t₁ t₂) )
  ⊢-gen (Γ , (τ `→ τ₁)) =
    ( do α ← Callᵢ {x = Γ , (τ `→ τ₁)} ident tt
         t ← μᵢ ((Γ , α ∶ τ) , τ₁)
         pure ([Abs] t)
    ) ∥
    ( ⦇ [Var] (Callᵢ {x = Γ , τ `→ τ₁ } ∋-gen (Γ , (τ `→ τ₁))) ⦈ )

  -- Convert a typing judgement to its corresponding term
  ⊢→Tm : ∀ {Γ : Ctx} {τ : Ty} → Γ ⊢ τ → Tm
  ⊢→Tm ([Var] x)     = $ ∋→Id x
  ⊢→Tm ([Abs] {α} p) = Λ α ⇒ ⊢→Tm p
  ⊢→Tm ([App] p₁ p₂) = ⊢→Tm p₁ ⊚ ⊢→Tm p₂ 

  nat : 𝔾 ℕ
  nat = ⦇ zero  ⦈
      ∥ ⦇ suc μ ⦈
