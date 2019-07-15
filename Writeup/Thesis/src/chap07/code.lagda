\begin{code}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Model.Base
open import Model.Combinators
open import Model.Enumerate
open import Model.Generic.Isomorphism renaming (_≅_ to _≃_)
open import Model.Data using (_∈_ ; here ; there)
open import Level renaming (zero to zeroL ; suc to sucL)

open import Data.Product
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Fin hiding (_+_)

open import Function hiding (_∋_)

open import Relation.Binary.PropositionalEquality

open GAlternative ⦃...⦄
open GApplicative ⦃...⦄
open GMonad       ⦃...⦄
\end{code}

%<*sl>
\begin{code}
data Sl : ℕ → Set where
    ∙   : ∀ {n} → Sl (suc n)
    ▻_  : ∀ {n} → Sl n → Sl (suc n)
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
    {   ∙     → `1
    ;  (▻ ∙)  → `var n
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
    `σ 2 λ {   ∙     → `1
           ;  (▻ ∙)  → `var n
           }}
\end{code}
%</idescfin2>

\begin{code}
open A
\end{code}

%<*lambdadatatypes>
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
  _,'_   : Ctx → Ty → Ctx
\end{code}
%</lambdadatatypes>

\begin{code}
infix 30 _,'_
infix 20 _∋_
\end{code}

%<*ctxmembership>
\begin{code}
data _∋_ : Ctx → Ty → Set where

  [Pop]  :  ∀ {Γ τ}
         →  Γ ,' τ ∋ τ

  [Top]  :  ∀ {Γ τ σ} →  Γ ∋ τ 
         →  Γ ,' σ ∋ τ
\end{code}
%</ctxmembership>

%<*typejudgement>
\begin{code}
data _⊢_ : Ctx → Ty → Set where

  [Var]  :  ∀ {Γ τ} → Γ ∋ τ
         →  Γ ⊢ τ

  [Abs]  :  ∀ {Γ σ τ} → Γ ,' σ ⊢ τ
         →  Γ ⊢ (σ `→ τ)

  [App]  :  ∀ {Γ σ τ} → Γ ⊢ (σ `→ τ) → Γ ⊢ σ
         →  Γ ⊢ τ
\end{code}
%</typejudgement>

%<*toterm>
\begin{code}
toVar : ∀ {Γ τ} → Γ ∋ τ → ℕ
toVar [Pop]        = zero
toVar ([Top] Γ∋τ)  = suc (toVar Γ∋τ)

toTerm : ∀ {Γ τ} → Γ ⊢ τ → RT
toTerm ([Var] Γ∋τ)    = tvar (toVar Γ∋τ)
toTerm ([Abs] t)      = tlam (toTerm t)
toTerm ([App] tₗ tᵣ)  = tapp (toTerm tₗ) (toTerm tᵣ)
\end{code}
%</toterm>

\begin{code}

module Inductive where 
\end{code}

\begin{code}
  varDesc : Ctx × Ty → IDesc (Ctx × Ty)
  varDesc (Γ , τ) = `Σ (Γ ∋ τ) λ _ → `1

  absDesc : Ctx × Ty × Ty  → IDesc (Ctx × Ty)
  absDesc (Γ , σ , τ) = `var (Γ ,' σ , τ)

  appDesc : Ctx × Ty → IDesc (Ctx × Ty)
  appDesc (Γ , τ) = `Σ Ty (λ σ  →  `var (Γ , σ `→ τ)
                                `× `var (Γ , σ))
\end{code}

%<*slcdescinductive>
\begin{code}
  wt : Ctx × Ty → IDesc (Ctx × Ty)
  wt (Γ , τ) =
    case τ of λ { `τ →
        `σ 2 λ {   ∙     → varDesc (Γ , τ)
               ;  (▻ ∙)  → appDesc (Γ , τ) }
      ; (τ₁ `→ τ₂) →
        `σ 3 λ {   ∙       → varDesc (Γ , τ)
               ;  (▻ ∙)    → absDesc (Γ , τ₁ , τ₂)
               ;  (▻ ▻ ∙)  → appDesc (Γ , τ) } }
\end{code}
%</slcdescinductive>

\begin{code}
module Constrained where
\end{code}

%<*sltcconstructordesc>
\begin{code}
  varDesc : Ctx × Ty → IDesc (Ctx × Ty)
  varDesc (Γ , τ) = `Σ (Γ ∋ τ) λ _ → `1

  absDesc : Ctx × Ty × Ty  → IDesc (Ctx × Ty)
  absDesc (Γ , σ , τ) = `Σ ℕ (λ α → `var (Γ ,' σ , τ))

  appDesc : Ctx × Ty → IDesc (Ctx × Ty)
  appDesc (Γ , τ) = `Σ Ty (λ σ  →   `var (Γ , σ `→ τ)
                                `×  `var (Γ , σ))
\end{code}
%</sltcconstructordesc>

%<*slcdescconstrained>
\begin{code}
  wt : Ctx × Ty → IDesc (Ctx × Ty)
  wt (Γ , τ) =
    `σ 3 λ  {  ∙         → varDesc (Γ , τ)
            ; (▻ ∙)      →
              `Σ  (Σ (Ty × Ty) λ { (σ , τ') → τ ≡ σ `→ τ' })
                  λ { ((σ , τ') , _) → absDesc (Γ , (σ , τ')) }
            ; (▻ ▻ ∙)  → appDesc (Γ , τ)
            }
\end{code}
%</slcdescconstrained>

\begin{code}
module E where
  open Constrained
  open Inductive
\end{code}

%<*desciso>
\begin{code}
  desc≃ : ∀ {Γ τ}  →  Fix Inductive.wt (Γ , τ)
                   ≃  Fix Constrained.wt (Γ , τ)
\end{code}
%</desciso>

%<*constrainediso>
\begin{code}
  wt≃ : ∀ {Γ τ} → Fix Constrained.wt (Γ , τ) → Γ ⊢ τ 
\end{code}
%</constrainediso>

\begin{code}
  wt≃ = {!!}
  desc≃ = {!!}
\end{code}

%<*idescm>
\begin{code}
data IDescM {I : Set} (P : Set → Set) : IDesc I → Set where
\end{code}
%</idescm>

\begin{code}
  `var~ : ∀ {i : I} → IDescM P (`var i)
    
  `1~ : IDescM P `1
    
  _`×~_ : ∀ {d₁ d₂ : IDesc I} → IDescM P d₁
          → IDescM P d₂ → IDescM P (d₁ `× d₂)
          
  `σ~ :  ∀ {n : ℕ} {T : Sl n → IDesc I} → ((fn : Sl n) → IDescM P (T fn))
      →  IDescM P (`σ n T)
\end{code}



%<*idescmsigma>
\begin{code}
  `Σ~  :  ∀ {S : Set} {T : S → IDesc I} → P S
       → ((s : S) → IDescM P (T s)) →  IDescM P (`Σ S T)
\end{code}
%</idescmsigma>

\begin{code}
Sl-gen : (n : ℕ) → Gen (Sl n) Sl n
Sl-gen zero = empty
Sl-gen (suc n) = ⦇ ∙ ⦈ ∥ ⦇ ▻ (μ n) ⦈

mapm : ∀ {ℓ k} {I : Set k} {δ : IDesc I} {P Q : Set ℓ → Set (sucL ℓ)}
       → (∀ {s : Set ℓ} → P s → Q s) → IDescM P δ → IDescM Q δ
mapm f `var~ = `var~
mapm f `1~ = `1~
mapm f (dₗ `×~ dᵣ) = (mapm f dₗ) `×~ mapm f dᵣ
mapm f (`σ~ fd) = `σ~ (mapm f ∘ fd)
mapm f (`Σ~ s fd) = `Σ~ (f s) (mapm f ∘ fd) 

module C where
\end{code}

%<*idescgen>
\begin{code}
  IDesc-gen :  ∀ {I} {i : I} → (δ : IDesc I) → (φ : I → IDesc I)
            →  Gen (⟦ δ ⟧ (Fix φ)) (λ i → ⟦ φ i ⟧ (Fix φ)) i
\end{code} 
%</idescgen>

%<*idescgentrivial>
\begin{code}
  IDesc-gen (`var i)    φ = ⦇ In (μ i) ⦈
  IDesc-gen `1          φ = ⦇ tt ⦈
  IDesc-gen (δₗ `× δᵣ)  φ = ⦇ (IDesc-gen δₗ φ) , (IDesc-gen δᵣ φ) ⦈
\end{code}
%</idescgentrivial>

\begin{code}
  IDesc-gen (`Σ S T) φ = {!!}
\end{code}

%<*idescgencop>
\begin{code}
  IDesc-gen {i = i} (`σ n T) φ = do
    sl ← Call {x = i} n Sl-gen
    t  ← IDesc-gen (T sl) φ
    pure (_,_ {B = λ sl → ⟦ T sl ⟧ (Fix φ)} sl t)
\end{code}
%</idescgencop>

\begin{code}
module D where

  IDesc-gen : ∀ {I} {i : I} → (δ : IDesc I) → (φ : I → IDesc I) → IDescM (λ a → Gen a (λ { tt → a}) tt) δ → Gen (⟦ δ ⟧ (Fix φ)) (λ i → ⟦ φ i ⟧ (Fix φ)) i
  IDesc-gen (`var i) φ m = {!!}
  IDesc-gen `1 φ m = {!!}
  IDesc-gen (δ `× δ₁) φ m = {!!}
  IDesc-gen (`σ n T) φ m = {!!}
\end{code}

%<*idescgensigma>
\begin{code}
  IDesc-gen (`Σ S T) φ (`Σ~ S~ T~) = do
    s ← Call tt (λ { tt → S~ })
    t ← IDesc-gen (T s) φ (T~ s)
    pure (_,_ {B = λ s → ⟦ T s ⟧ (Fix φ ) } s t)
\end{code}
%</idescgensigma>

%<*describe>
\begin{code}
record Describe {I} (A : I → Set) : Set where
  field φ : I → IDesc I
  field iso : (i : I) → A i ≃ Fix φ i
\end{code}
%</describe>

%<*completeness>
\begin{code}
Complete :  ∀ {I} {P : I → Set} → (i : I)
            → ((i : I) → Gen (P i) P i) → Set
Complete {I} {P} i gen =
  ∀ {x : P i} → ∃[ n ] (x ∈ enumerate gen i (gen i) n)
\end{code}
%</completeness>

%<*productivity>
\begin{code}
_∣ᵢ_↝_ :  ∀ {I} {A : Set} {P : I → Set} {i : I}
          → Gen A P i → ((i : I) → Gen (P i) P i) → A → Set
\end{code}
%</productivity>
\begin{code}
_∣ᵢ_↝_ = {!!}
\end{code}

%<*bindcomplete>
\begin{code}
>>=-Complete :
  ∀ {I A} {P : A → Set} {T : I → Set} {x y}
    {g : Gen A T x} {g' : (v : A) → Gen (P v) T y}
    {x : Σ A P} {tg : (i : I) → Gen (T i) T i}
  → g ∣ᵢ tg ↝ proj₁ x
  → g' (proj₁ x) ∣ᵢ tg ↝ proj₂ x
  → (g >>= λ y → ⦇ (λ v → y , v) (g' y) ⦈) ∣ᵢ tg ↝ x 
\end{code}
%</bindcomplete>
\begin{code} ∣ 
>>=-Complete = {!!}


module Bar where

  open D

  Sl-gen-Complete : (n : ℕ) → Complete n Sl-gen
  Sl-gen-Complete = {!!}

  IDesc-gen-Complete : ∀ {I} {δ φ} {x : ⟦ δ ⟧ (Fix φ)} {i}
                         {m' : (i : I) → IDescM ((λ S → Σ[ g ∈ Gen S (λ _ → S) tt ] Complete tt λ _ → g)) (φ i)} → (m : IDescM {I = I} (λ S → Σ[ g ∈ Gen S (λ _ → S) tt ] Complete tt λ _ → g) δ)
                     → _∣ᵢ_↝_ {i = i} (IDesc-gen δ φ (mapm proj₁ m)) (λ i → IDesc-gen (φ i) φ (mapm proj₁ (m' i))) x
\end{code}

\begin{code}
  IDesc-gen-Complete {δ = `var i} {φ} {x} m = {!!}
  IDesc-gen-Complete {δ = `1} {φ} {x} m = {!!}
  IDesc-gen-Complete {δ = δ `× δ₁} {φ} {x} m = {!!}
  IDesc-gen-Complete {δ = `σ n T} {φ} {fn , x} (`σ~ mT) =
    >>=-Complete Sl-gen-Complete (IDesc-gen-Complete {δ = T fn} (mT fn))
  IDesc-gen-Complete {δ = `Σ S T} {φ} {s , x} (`Σ~ (g , prf) mT) =
    >>=-Complete prf (IDesc-gen-Complete {δ = T s} (mT s))
\end{code}

\begin{code}
module Foo where

  open C
\end{code}

%<*incompletetype>
\begin{code}
  In-Complete : ∀ {g g' x}
    → g ∣ᵢ g' ↝ x → (⦇ In g ⦈) ∣ᵢ g' ↝ In x

  `×-Complete : ∀ {g₁ g₂ g' x y}
    → g₁ ∣ᵢ g' ↝ x → g₂ ∣ᵢ g' ↝ y
    → ⦇ g₁ , g₂ ⦈ ∣ᵢ g' ↝ (x , y)
\end{code}
%</incompletetype>

\begin{code}
  In-Complete = {!!}
\end{code}
\begin{code}
  `×-Complete = {!!}

\end{code}

%<*idesccompletetype>
\begin{code}
  IDesc-gen-Complete :
    ∀ {δ φ x} → IDesc-gen δ φ ∣ᵢ (λ i → IDesc-gen (φ i) φ) ↝ x
\end{code}
%</idesccompletetype>

%<*idesccompletetrivial>
\begin{code}
  IDesc-gen-Complete {`var i} {φ} {In x}
    with IDesc-gen-Complete {φ i} {φ} {x}
  ... | prf = In-Complete prf
  IDesc-gen-Complete {`1} {φ} {tt} = 1 , here
  IDesc-gen-Complete {δ₁ `× δ₂} {φ} {x , y} =
    `×-Complete  (IDesc-gen-Complete {δ₁})
                 (IDesc-gen-Complete {δ₂})
\end{code}
%</idesccompletetrivial>

\begin{code}
  IDesc-gen-Complete {`σ n T} {φ} {x} = {!!}
  IDesc-gen-Complete {`Σ S T} {φ} {x} = {!!}
\end{code}

\begin{code}
open Inductive
\end{code}

%<*genelem>
\begin{code}
gen∋ : (Γ : Ctx) → (τ : Ty) → Gen (Γ ∋ τ) (λ { tt → Γ ∋ τ }) tt

genTy : Gen Ty (λ { tt → Ty }) tt
\end{code}
%</genelem>

\begin{code}
gen∋ _ _ = empty
genTy = empty
\end{code}

%<*wtmeta>
\begin{code}
wtM  : (i : Ctx × Ty)
     → IDescM (λ S → Gen S (λ { tt → S }) tt) (wt i)
wtM (Γ , `τ) =
  `σ~ λ {  ∙     → `Σ~ (gen∋ Γ `τ) λ _ → `1~
        ; (▻ ∙)  → `Σ~ genTy λ _ → `var~ `×~ `var~
        }
wtM (Γ , (τ₁ `→ τ₂))  =
  `σ~ λ {  ∙       → `Σ~ (gen∋ Γ (τ₁ `→ τ₂)) (λ s → `1~)
        ; (▻ ∙)    → `var~
        ; (▻ ▻ ∙)  → `Σ~ genTy (λ s → `var~ `×~ `var~) }
\end{code}
%</wtmeta>

\begin{code}
data STree (A : Set) : ℕ → Set where
  leaf : STree A 0
  node : ∀ {n m} → STree A n → STree A m → STree A (suc (n + m))
\end{code}

%<*streedesc>
\begin{code}
STreeD : Set → ℕ → IDesc ℕ
STreeD A zero     = `1
STreeD A (suc n)  =
  `Σ (Σ (ℕ × ℕ) λ { ( m , k ) → m + k ≡ n })
    λ { ((m , k) , _) →
      (`var m `× `Σ A λ _ → `1) `× `var k }
\end{code}
%</streedesc>

