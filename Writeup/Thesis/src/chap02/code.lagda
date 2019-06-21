\begin{code}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}


module code where

  open import AgdaGen.Base hiding (Gen; 𝔾; Genᵢ ; 𝔾ᵢ)
  open import AgdaGen.Combinators

  open import Data.Empty

  
  open import Data.Nat  hiding (_≟_; _+_ ; _*_)
  open import Data.Bool  hiding (_≟_)
  open import Data.Product renaming (_×_ to _*_) hiding (map)
  open import Data.Sum renaming (_⊎_ to _+_) hiding (map)

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

  open import Data.Unit hiding (_≟_; _≤_)
  open import Data.Product hiding (map)
  open import Level hiding (suc; zero)
  open import Data.List hiding (map; length)
  open import Data.Sum hiding (map)
  open import Data.Fin  hiding (_≟_ ; _+_; _≤_)

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
  module C where
\end{code}
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

%<*tautologytype>
\begin{code}
  tautology : ∀ {P Q R} → P * (Q + R) → (P * Q) + (P * R)
\end{code}
%</tautologytype>

%<*tautologydef>
\begin{code}
  tautology (fst , inj₁ x) = inj₁ (fst , x)
  tautology (fst , inj₂ y) = inj₂ (fst , y)
\end{code}
%</tautologydef>

 ∀ P . ¬ (P ∧ ¬P)
%<*notpandnotp>
\begin{code}
  P∧¬P→⊥ : ∀ {P} → P * (P → ⊥) → ⊥
  P∧¬P→⊥ (P , P→⊥) = P→⊥ P 
\end{code}
%</notpandnotp> ⊥

∀ x . ¬ P x → ¬ ∃ x . P x
%<*forallnottonotexists>
\begin{code}
  ∀¬→¬∃ : ∀ {P} → ((x : Set) → P x → ⊥) → Σ Set P → ⊥
  ∀¬→¬∃ ∀x¬P (x , Px) = ∀x¬P x Px 
\end{code}
%</forallnottonotexists>

\begin{code}
  {-# NON_TERMINATING #-}
\end{code}

%<*lengthdef>
\begin{code}
  length : ∀ {a : Set} → Colist a ∞ → ℕ
  length [] = 0
  length (x ∷ xs) = suc (length (xs .force))
\end{code}
%</lengthdef>

\begin{code}
  module D where

    map : ∀ {a b} → (a → b) → List a → List b
    map f [] = []
    map f (x ∷ xs) = f x ∷ map f xs

    {-# NON_TERMINATING #-}
\end{code}

%<*incposdef>
\begin{code}
    incpos : List ℕ → List ℕ
    incpos [] = []
    incpos (x ∷ xs) = x ∷ incpos (map suc xs)
\end{code}
%</incposdef>

%<*sizedlistdef>
\begin{code}
  data SList (A : Set) : Size → Set where
    []   : ∀ {i} → SList A i
    _∷_  : ∀ {i} → A → SList A i → SList A (↑ i)  
\end{code}
%</sizedlistdef>

\begin{code}
  module E where
\end{code}

%<*sizedmapdef>
\begin{code}
     map : ∀ {i} {A B : Set} → (A → B) → SList A i → SList B i
\end{code}
%</sizedmapdef>

\begin{code}
     map = {!!}
\end{code}

P ∨ ¬ P
%<*excludedmiddle>
\begin{code}
  P∨¬P : ∀ {P} → P + ¬ P
\end{code}
%</excludedmiddle>
\begin{code}
  P∨¬P {P} = {!!}
\end{code}

%<*sorted>
\begin{code}
  data Sorted : (xs : List ℕ) → Set where
    nil     :  Sorted []
    single  :  ∀ {n} → Sorted (n ∷ [])
    step    :  ∀ {n m xs} → n ≤ m → Sorted (m ∷ xs)
            →  Sorted (n ∷ m ∷ xs)
\end{code}
%</sorted>
