\begin{code}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import AgdaGen.Base
open import AgdaGen.Combinators
open import Level renaming (zero to zeroL ; suc to sucL)

open import Data.Product
open import Data.Nat

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


