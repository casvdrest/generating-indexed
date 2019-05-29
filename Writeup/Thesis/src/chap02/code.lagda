\begin{code}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}


module code where

  open import AgdaGen.Base hiding (Gen; 𝔾; Genᵢ ; 𝔾ᵢ)
  open import AgdaGen.Combinators

  
  open import Data.Nat  hiding (_≟_)
  open import Data.Bool  hiding (_≟_)

  module B where
    infixr 10 _∷_
\end{code}
%<*upolylist>
\begin{code}
    data List {ℓ} (a : Set ℓ) : Set ℓ where
      [] : List a
      _∷_ : a → List a → List a
\end{code}
%</upolylist>
\begin{code}

    xs = 1 ∷ 2 ∷ []
    ys = ℕ ∷ Bool ∷ []

  open import Data.Unit hiding (_≟_)
  open import Data.Product hiding (map)
  open import Level hiding (suc; zero)
  open import Data.List hiding (map)
  open import Data.Sum hiding (map)
  open import Data.Fin  hiding (_≟_)

  open import Relation.Binary.PropositionalEquality

  open import Relation.Binary
  open import Relation.Nullary

  open import Size
  open import Codata.Thunk hiding (map)

  data 𝓤 : Set where

  ⟦_⟧ : 𝓤 → Set → Set
  ⟦_⟧ = {!!}

  data Fix (u : 𝓤) : Set where

  module A where

    open Data.List
    {-# NON_TERMINATING #-}
\end{code}

%<*natsnonterminating>
\begin{code}
    nats : List ℕ
    nats = 0 ∷ map suc nats
\end{code}
%</natsnonterminating>

%<*colist>
\begin{code}
  data Colist (A : Set) (i : Size) : Set where
    [] : Colist A i
    _∷_ : A → Thunk (Colist A) i → Colist A i
\end{code}
%</colist>

\begin{code}
  map : ∀ {A B : Set} {i : Size} → (A → B) → Colist A i → Colist B i
  map f [] = []
  map f (x ∷ xs) = f x ∷ λ where .force → map f (xs .force)
\end{code}

%<*natsterminating>
\begin{code}
  nats : ∀ {i : Size} → Colist ℕ i
  nats = 0 ∷ λ where .force → map suc nats
\end{code}
%</natsterminating>

%<*eqdef>
\begin{code}
  _≟_ : ∀ {u : 𝓤} → (x : Fix u) → (y : Fix u) → x ≡ y ⊎ ¬ x ≡ y
\end{code}
%</eqdef>
\begin{code}
  _≟_ = {!!}
\end{code}



