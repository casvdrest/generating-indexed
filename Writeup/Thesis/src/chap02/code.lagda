\begin{code}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}


module code where

  open import AgdaGen.Base hiding (Gen; 𝔾)
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
  open import Codata.Thunk hiding (map ; _<*>_)

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
  _≟_ : ∀ {u : 𝓤} → (x : Fix u) → (y : Fix u) → Dec (x ≡ y)
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
    step    :  ∀ {n m xs} → n ≤ m  →  Sorted (m ∷ xs)
                                   →  Sorted (n ∷ m ∷ xs)
\end{code}
%</sorted>

%<*isomorphism>
\begin{code}
  record _≃_ (A B : Set) : Set where
    field 
      from : A → B
      to   : B → A
      iso₁ : ∀ {x : A} → to (from x) ≡ x
      iso₂ : ∀ {y : B} → from (to y) ≡ y
\end{code}
%</isomorphism>

%<*isoequivalence>
\begin{code}
  ≃-refl   : ∀ {A} → A ≃ A
  ≃-sym    : ∀ {A B} → A ≃ B → B ≃ A
  ≃-trans  : ∀ {A B C} → A ≃ B → B ≃ C → A ≃ C 
\end{code}
%</isoequivalence>

\begin{code}
  open import Function

  ≃-refl = {!!}
  
  ≃-sym = {!!}

  ≃-trans = {!!}

  module F where 

    map : ∀ {A B} → (A → B) → (List A → List B)
    map f [] = []
    map f (x ∷ xs) = f x ∷ map f xs

    merge : ∀ {A} → List A → List A → List A
    merge [] ys = ys
    merge (x ∷ xs) ys = x ∷ merge ys xs
\end{code}

%<*abstractgen>
\begin{code}
    data Gen {I} : (Set) → (I → Set) → I → Set where
     Pure : ∀ {A T i}      → A → Gen A T i
     Ap   : ∀ {A B T i j}  → Gen (B → A) T i → Gen B T j
                           → Gen A T i
     Bind : ∀ {A B T i j}  → Gen A T j → (A → Gen B T i)
                           → Gen B T i
     Or   : ∀ {A T i}      → Gen A T i → Gen A T i
                           → Gen A T i
     μ    : ∀ {A}          → (i : I) → Gen (A i) A i
     None : ∀ {A T i}      → Gen A T i
     Call : ∀ {J S T i}    → ((j' : J) → Gen (S j') S j')
                           → (j : J) → Gen (S j) T i
\end{code}
%</abstractgen>

%<*enumerate>
\begin{code}
    enumerate : ∀ {I A T} → ((i : I) → Gen (T i) T i)
                          → (i : I) → Gen A T i → ℕ → List A
    enumerate tg i g                    zero     = []
    enumerate tg i (Pure x)             (suc n)  = x ∷ []
    enumerate tg i (Ap {j = j} g₁ g₂)   (suc n)  =
      concatMap  (λ f → map f (enumerate tg j g₂ (suc n)))
                 (enumerate tg i g₁ (suc n))
    enumerate tg i (Bind {j = j} g₁ fg) (suc n)  =
      concatMap  (λ x → enumerate tg i (fg x) (suc n))
                 (enumerate tg j g₁ (suc n))
    enumerate tg i (Or g₁ g₂)           (suc n)  =
      merge  (enumerate tg i g₁ (suc n))
             (enumerate tg i g₂ (suc n))
    enumerate tg i (μ .i)               (suc n)  =
      enumerate tg i (tg i) n
    enumerate tg i None                 (suc n)  = []
    enumerate tg i (Call g j)           (suc n)  =
      enumerate g j (g j) (suc n)
\end{code}
%</enumerate>

\begin{code}
  open import AgdaGen.Data
  open import AgdaGen.Base
  open import AgdaGen.Enumerate
  open import AgdaGen.Combinators

  open GMonad ⦃...⦄
  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
\end{code}

%<*fingen>
\begin{code}
  fin : (n : ℕ) → Gen (Fin n) Fin n
  fin zero     =  empty
  fin (suc n)  =  ⦇ zero       ⦈
               ∥  ⦇ suc (μ n)  ⦈
\end{code}
%</fingen>

%<*completeness>
\begin{code}
  Complete : ∀ {I} {A : I → Set} → ((i : I) → Gen (A i) A i) → Set
  Complete {I} {A} gen =
    ∀ {i : I} {x : A i} → ∃[ n ] (x ∈ enumerate gen i (gen i) n)
\end{code}
%</completeness>

%<*natgen>
\begin{code}
  nat : Gen ℕ (λ { tt → ℕ }) tt
  nat  =  ⦇ zero        ⦈
       ∥  ⦇ suc (μ tt)  ⦈
\end{code}
%</natgen>
