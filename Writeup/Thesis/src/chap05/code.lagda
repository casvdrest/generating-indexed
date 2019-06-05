\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-}

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat

open import AgdaGen.Base hiding (Call)
open import AgdaGen.Combinators

open import Function

open import Relation.Binary.PropositionalEquality

record _≃_ (a : Set) (b : Set) : Set where
  field
    from  : a → b
    to    : b → a
    iso₁  : ∀ {x} → to (from x) ≡ x
    iso₂  : ∀ {y} → from (to y) ≡ y

\end{code}


%<*regular>
\begin{code}
data Reg : Set where
  Z    : Reg
  U    : Reg
  _⊕_  : Reg → Reg → Reg
  _⊗_  : Reg → Reg → Reg
  I    : Reg
\end{code}
%</regular>

%<*regularsemantics>
\begin{code}
⟦_⟧ : Reg → Set → Set
⟦ Z        ⟧ r = ⊥
⟦ U        ⟧ r = ⊤
⟦ c₁ ⊕ c₂  ⟧ r = ⟦ c₁ ⟧ r ⊎ ⟦ c₂ ⟧ r
⟦ c₁ ⊗ c₂  ⟧ r = ⟦ c₁ ⟧ r × ⟦ c₂ ⟧ r
⟦ I        ⟧ r = r

data Fix (c : Reg) : Set where
  In : ⟦ c ⟧ (Fix c) → Fix c
\end{code}
%</regularsemantics>

%<*regularmap>
\begin{code}
mapr : ∀ {a b c} → (a → b) → ⟦ c ⟧ a → ⟦ c ⟧ b
mapr {c = Z} f ()
mapr {c = U} f tt = tt
mapr {c = c₁ ⊕ c₂} f (inj₁ x) = inj₁ (mapr f x)
mapr {c = c₁ ⊕ c₂} f (inj₂ y) = inj₂ (mapr f y)
mapr {c = c ⊗ c₁} f (fst , snd) = (mapr f fst) , mapr f snd
mapr {c = I} f x = f x 
\end{code}
%</regularmap>

%<*natregular>
\begin{code}
ℕ' : Set
ℕ' = Fix (U ⊕ I)
\end{code}
%</natregular>

%<*natiso> 
\begin{code}
fromℕ : ℕ → ℕ'
fromℕ zero     = In (inj₁ tt)
fromℕ (suc n)  = In (inj₂ (fromℕ n))

toℕ : ℕ' → ℕ
toℕ (In (inj₁ tt))  = zero
toℕ (In (inj₂ y))   = suc (toℕ y)

ℕ-iso₁ : ∀ {n} → toℕ (fromℕ n) ≡ n
ℕ-iso₁ {zero}   = refl
ℕ-iso₁ {suc n}  = cong suc ℕ-iso₁

ℕ-iso₂ : ∀ {n} → fromℕ (toℕ n) ≡ n
ℕ-iso₂ {In (inj₁ tt)}  = refl
ℕ-iso₂ {In (inj₂ y)}   = cong (In ∘ inj₂) ℕ-iso₂

ℕ≃ℕ' : ℕ ≃ ℕ'
ℕ≃ℕ' = record { from = fromℕ ; to = toℕ ; iso₁ = ℕ-iso₁ ; iso₂ = ℕ-iso₂ }
\end{code}
%</natiso>

%<*regularrecord>
\begin{code}
record Regular (a : Set) : Set where
    field
      W : Σ[ c ∈ Reg ] (a ≃ Fix c)
\end{code}
%</regularrecord>

\begin{code}
module A where 
\end{code}

%<*genericgen>
\begin{code}
  deriveGen : (c : Reg) → Gen (Fix c) (Fix c)
\end{code}
%</genericgen>

\begin{code}
  deriveGen = {!!}

module B where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
\end{code}

%<*genericgen2>
\begin{code}
  deriveGen : (c c' : Reg) → Gen (⟦ c ⟧ (Fix c')) (⟦ c' ⟧ (Fix c'))
\end{code}
 %</genericgen2>

%<*genericgenZU>
\begin{code}
  deriveGen Z c' = empty
  deriveGen U c' = pure tt
\end{code}
%</genericgenZU>μ

%<*genericgenI>
\begin{code}
  deriveGen I c' = ⦇ In μ ⦈
\end{code}
%</genericgenI>

%<*genericgenPCOP>
\begin{code}
  deriveGen (cₗ ⊕ cᵣ) c' = ⦇ inj₁ (deriveGen cₗ c') ⦈ ∥ ⦇ inj₂ (deriveGen cᵣ c') ⦈
  deriveGen (cₗ ⊗ cᵣ) c' = ⦇ deriveGen cₗ c' , deriveGen cᵣ c' ⦈
\end{code}
%</genericgenPCOP>

\begin{code}
  Call : ∀ {a t : Set} → Gen a a → Gen a t
  Call = `_
\end{code}

%<*genericgenFinal>
\begin{code}
  genericGen : (c : Reg) → Gen (Fix c) (Fix c)
  genericGen c = ⦇ In (Call (deriveGen c c)) ⦈
\end{code}
%</genericgenFinal>

%<*genericgenNat>
\begin{code}
  genℕ : Gen ℕ ℕ
  genℕ = ⦇ (_≃_.to ℕ≃ℕ') (Call (genericGen (U ⊕ I))) ⦈
\end{code}
%</genericgenNat>

%<*isogen>
\begin{code}
  isoGen : ∀ {A} → ⦃ p : Regular A ⦄ → Gen A A
  isoGen ⦃ record { W = c , iso } ⦄ = ⦇ (_≃_.to iso) (Call (genericGen c)) ⦈
\end{code}
%</isogen>

