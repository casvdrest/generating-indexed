\begin{code}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import AgdaGen.Base
open import AgdaGen.Combinators
open import AgdaGen.Generic.Isomorphism renaming (_≅_ to _≃_) 
open import Level renaming (zero to zeroL ; suc to sucL)

open import Data.Product
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Fin

open import Function hiding (_∋_)

open import Relation.Binary.PropositionalEquality

open GAlternative ⦃...⦄
open GApplicative ⦃...⦄
open GMonad       ⦃...⦄
\end{code}

%<*sl>
\begin{code}
data Sl : ℕ → Set where
    ∙  : ∀ {n} → Sl (suc n)
    ▻_ : ∀ {n} → Sl n → Sl (suc n)
\end{code}
%</sl>


%<*idesc>
\begin{code}
data IDesc (I : Set) : Set where
    `var  : (i : I) → IDesc I
    `1    : IDesc I
    _`×_  : (A B : IDesc I) → IDesc I
    `σ    : (n : ℕ)  → (T : Sl n → IDesc I) → IDesc I
    `Σ    : (S : Set) → (T : S → IDesc I) → IDesc I
\end{code}
%</idesc>

%<*idescsem>
\begin{code}
⟦_⟧ : ∀ {I} → IDesc I → (I → Set) → Set
⟦ `var i    ⟧ r = r i
⟦ `1        ⟧ r = ⊤
⟦ dₗ `× dᵣ  ⟧ r = ⟦ dₗ ⟧ r × ⟦ dᵣ ⟧ r
⟦ `σ n T    ⟧ r = Σ[ sl ∈ Sl n ] ⟦ T sl ⟧ r
⟦ `Σ S T    ⟧ r = Σ[ s ∈ S ] ⟦ T s ⟧ r
\end{code}
%</idescsem>

%<*idescfix>
\begin{code}
data Fix {I : Set} (φ : I → IDesc I) (i : I) : Set where
  In : ⟦ φ i ⟧ (Fix φ) → Fix φ i
\end{code}
%</idescfix>

\begin{code}
module A where
\end{code}

%<*idescfin>
\begin{code}
  finD : ℕ → IDesc ℕ
  finD zero     = `σ 0 λ()
  finD (suc n)  = `σ 2 λ
    { ∙      → `1
    ; (▻ ∙)  → `var n
    }
\end{code}
%</idescfin>

\begin{code}
module B where
\end{code}

%<*idescfin2>
\begin{code}
  finD : ℕ → IDesc ℕ
  finD = λ n → `Σ ℕ λ m → `Σ (n ≡ suc m) λ { refl →
    `σ 2 λ { ∙      → `1
           ; (▻ ∙)  → `var n
           }}
\end{code}
%</idescfin2>

\begin{code}
open A
\end{code}

%<*idescfiniso>
\begin{code}
fromFin : ∀ {n} → Fin n → Fix finD n
fromFin {suc _} zero      = In (∙    , tt)
fromFin {suc _} (suc fn)  = In (▻ ∙  , fromFin fn)

toFin : ∀ {n} → Fix finD n → Fin n
toFin {suc _} (In (∙    , _))  = zero
toFin {suc _} (In (▻ ∙  , r))  = suc (toFin r)

isoFin₁ : ∀ {n fn} → toFin {n} (fromFin fn) ≡ fn
isoFin₁ {suc _} {zero}   = refl
isoFin₁ {suc _} {suc _}  = cong suc isoFin₁

isoFin₂ : ∀ {n fn} → fromFin {n} (toFin fn) ≡ fn
isoFin₂ {suc _} {In (∙    , _)}  = refl
isoFin₂ {suc _} {In (▻ ∙  , _)}  = cong (λ x → In (▻ ∙ , x)) isoFin₂
\end{code}
%</idescfiniso>

\begin{code}
data RT : Set where
  tvar : ℕ → RT
  tlam : RT → RT
  tapp : RT → RT → RT

data Ty : Set where
  `τ    : Ty
  _`→_  : Ty → Ty → Ty

data Ctx : Set where
  ∅      : Ctx
  _,_∶_  : Ctx → ℕ → Ty → Ctx

infix 30 _,_∶_
infix 20 _∋_
\end{code}

%<*ctxmembership>
\begin{code}
data _∋_ : Ctx → Ty → Set where
  [Pop]  :  ∀ {Γ α τ}
            -------------
         →  Γ , α ∶ τ ∋ τ

  [Top]  :  ∀ {Γ α τ σ} → Γ ∋ τ
            --------------------
         →  Γ , α ∶ σ ∋ τ
\end{code}
%</ctxmembership>

%<*typejudgement>
\begin{code}
data _⊢_ : Ctx → Ty → Set where
  [Var]  :  ∀ {Γ τ} → Γ ∋ τ
            ----------------
         →  Γ ⊢ τ

  [Abs]  :  ∀ {Γ α σ τ} → Γ , α ∶ σ ⊢ τ
            ---------------------------
         →  Γ ⊢ (σ `→ τ)

  [App]  :  ∀ {Γ σ τ} → Γ ⊢ (σ `→ τ) → Γ ⊢ σ
            --------------------------------
         →  Γ ⊢ τ
\end{code}
%</typejudgement>

%<*toterm>
\begin{code}
toTerm : ∀ {Γ τ} → Γ ⊢ τ → RT
\end{code}
%</toterm>

\begin{code}
toTerm = {!!}

module Inductive where 
\end{code}

%<*slcdescinductive>
\begin{code}
  wt : Ctx × Ty → IDesc (Ctx × Ty)
  wt (Γ , τ) =
    case τ of λ { `τ →
        `σ 2 λ { ∙      → varDesc (Γ , τ)
               ; (▻ ∙)  → appDesc (Γ , τ) }
      ; (τ₁ `→ τ₂) →
        `σ 3 λ { ∙        → varDesc (Γ , τ)
               ; (▻ ∙)    → absDesc (Γ , τ₁ , τ₂)
               ; (▻ ▻ ∙)  → appDesc (Γ , τ) } } 
    where varDesc : Ctx × Ty → IDesc (Ctx × Ty)
          varDesc (Γ , τ) = `Σ (Γ ∋ τ) λ _ → `1
          absDesc : Ctx × Ty × Ty  → IDesc (Ctx × Ty)
          absDesc (Γ , σ , τ) = `Σ ℕ (λ α → `var (Γ , α ∶ σ , τ))
          appDesc : Ctx × Ty → IDesc (Ctx × Ty)
          appDesc (Γ , τ) = `Σ Ty (λ σ → `var (Γ , σ `→ τ) `× `var (Γ , σ))
\end{code}
%</slcdescinductive>

\begin{code}
module Constrained where
\end{code}

%<*slcdescconstrained>
\begin{code}
  wt : Ctx × Ty → IDesc (Ctx × Ty)
  wt (Γ , τ) =
    `σ 3 λ  { ∙          → `Σ (Γ ∋ τ) λ _ → `1
            ; (▻ ∙)      → `Σ (Σ (Ty × Ty) λ { (σ , τ') → τ ≡ σ `→ τ' })
                             λ { ((σ , τ') , refl)
                                 → `Σ ℕ (λ α → `var (Γ , α ∶ σ , τ')) }
            ; (▻ (▻ ∙))  → `Σ Ty λ {σ → `var (Γ , σ `→ τ) `× `var (Γ , σ) }
            }
\end{code}
%</slcdescconstrained>

\begin{code}
module E where
  open Constrained
  open Inductive
\end{code}

\begin{code}
  fromInductive : ∀ {Γ τ} → Fix Inductive.wt (Γ , τ) → Fix Constrained.wt (Γ , τ)
  fromInductive {Γ} {`τ}      (In (∙ , Γ∋ , tt))               =
    In (∙ , Γ∋ , tt)
  fromInductive {Γ} {`τ}      (In ((▻ ∙) , τ , (r₁ , r₂)))     =
    In (▻ ▻ ∙ , τ , fromInductive r₁ , fromInductive r₂)
  fromInductive {Γ} {σ `→ τ}  (In (∙ , Γ∋ , tt))               =
    In (∙ , Γ∋ , tt )
  fromInductive {Γ} {σ `→ τ}  (In ((▻ ∙) , α , r))             =
    In (▻ ∙ , ((σ , τ) , refl) , α , fromInductive r)
  fromInductive {Γ} {σ `→ τ}  (In ((▻ (▻ ∙)) , σ' , r₁ , r₂))  =
    In (▻ ▻ ∙ , σ' , fromInductive r₁ , fromInductive r₂)

  toInductive : ∀ {Γ τ} → Fix Constrained.wt (Γ , τ) → Fix Inductive.wt (Γ , τ)
  toInductive {Γ} {`τ}       (In (∙ , Γ∋ , tt))                         =
    In (∙ , Γ∋ , tt)
  toInductive {Γ} {τ `→ τ₁}  (In (∙ , Γ∋ , tt))                         =
    In (∙ , Γ∋ , tt)
  toInductive {Γ} {`τ}       (In ((▻ ∙) , ((τ₁ , τ₂) , ()) , r))
  toInductive {Γ} {σ `→ τ}   (In ((▻ ∙) , ((.σ , .τ) , refl) , α , r))  =
    In ((▻ ∙) , α , toInductive r)
  toInductive {Γ} {`τ}       (In ((▻ (▻ ∙)) , σ' , r₁ , r₂))            =
    In (▻ ∙ , σ' , toInductive r₁ , toInductive r₂)
  toInductive {Γ} {σ `→ τ}   (In ((▻ (▻ ∙)) , σ' , r₁ , r₂))            =
    In (▻ ▻ ∙ , σ' , toInductive r₁ , toInductive r₂)

  wtIso₁ : ∀ {Γ τ} {wt : Fix Inductive.wt (Γ , τ)} → toInductive (fromInductive wt) ≡ wt
  wtIso₁ {Γ} {`τ}       {In (∙ , _)}                  = refl
  wtIso₁ {Γ} {`τ}       {In ((▻ ∙) , σ , _ , _)}      =
    cong₂ (λ x y → In ((▻ ∙) , σ , x , y)) wtIso₁ wtIso₁
  wtIso₁ {Γ} {τ `→ τ₁}  {In (∙ , _)}                  = refl
  wtIso₁ {Γ} {τ `→ τ₁}  {In ((▻ ∙) , α , _)}          =
    cong (λ x → In ((▻ ∙) , α , x)) wtIso₁
  wtIso₁ {Γ} {τ `→ τ₁}  {In ((▻ (▻ ∙)) , σ , _ , _)}  =
    cong₂ (λ x y → In (▻ ▻ ∙ , σ , x , y )) wtIso₁ wtIso₁

  wtIso₂ : ∀ {Γ τ} {wt : Fix Constrained.wt (Γ , τ)} → fromInductive (toInductive wt) ≡ wt
  wtIso₂ {Γ} {`τ} {In (∙ , _ , tt)}                                = refl
  wtIso₂ {Γ} {`τ} {In ((▻ ∙) , (_ , ()) , _)}
  wtIso₂ {Γ} {`τ} {In ((▻ (▻ ∙)) , σ , _ , _)}                     =
    cong₂ (λ x y → In ((▻ ▻ ∙) , σ , x , y)) wtIso₂ wtIso₂
  wtIso₂ {Γ} {σ `→ τ} {In (∙ , _ , tt)}                            = refl
  wtIso₂ {Γ} {σ `→ τ} {In ((▻ ∙) , (((.σ , .τ) , refl) , α , _))}  =
    cong (λ x → In (▻ ∙ , ((σ , τ) , refl) , α , x)) wtIso₂
  wtIso₂ {Γ} {σ `→ τ} {In ((▻ (▻ ∙)) , σ' , _ , _)}                =
    cong₂ (λ x y → In (▻ ▻ ∙ , σ' , x , y)) wtIso₂ wtIso₂

\end{code}

%<*desciso>
\begin{code}
  desc≃ : ∀ {Γ τ} → Fix Inductive.wt (Γ , τ) ≃ Fix Constrained.wt (Γ , τ)
\end{code}
  %</desciso>

\begin{code}
  desc≃ = record { from = fromInductive ; to = toInductive ; iso₁ = wtIso₁ ; iso₂ = wtIso₂ }
\end{code}

%<*constrainediso>
\begin{code}
  wt≃ : ∀ {Γ τ} → Fix Constrained.wt (Γ , τ) → Γ ⊢ τ 
\end{code}
%</constrainediso>

\begin{code}
  wt≃ = {!!}
\end{code}
`Σ : (S : Set) → (S → Description) → Description
