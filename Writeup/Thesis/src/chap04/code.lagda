\begin{code}
{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import AgdaGen.Base hiding (Gen; 𝔾; Genᵢ ; 𝔾ᵢ)
open import AgdaGen.Combinators

open import Data.Unit
open import Data.Product hiding (map)
open import Level hiding (suc; zero)
open import Data.List
open import Data.Fin
open import Data.Nat

module code where

\end{code}

%<*gendef>
\begin{code}
  data Gen : (a : Set) → (t : Set) → Set where
    Or    : ∀ {a t    : Set} → Gen a t → Gen a t → Gen a t
    Ap    : ∀ {a t b  : Set} → Gen (b → a) t → Gen b t  → Gen a t
    Pure  : ∀ {a t    : Set} → a → Gen a t
    None  : ∀ {a t    : Set} → Gen a t
    μ     : ∀ {a      : Set} → Gen a a
\end{code}
%</gendef>

%<*calldef>
\begin{code}
    Call : ∀ {a t : Set} → Gen a a → Gen a t 
\end{code}
%</calldef>

%<*binddef>
\begin{code}
    Bind : ∀ {a t b  : Set} → Gen a t → (a → Gen b t) → Gen b t
\end{code}
%</binddef>

%<*genidef>
\begin{code}
  data Genᵢ {I : Set} : Set → (I → Set) → I → Set where
      Pureᵢ  :  ∀ {a : Set} {t : I → Set} {i : I} → a → Genᵢ a t i
      
      Apᵢ    :  ∀ {a b : Set} {t : I → Set} {x : I} {y : I} 
                → Genᵢ (b → a) t x → Genᵢ b t y → Genᵢ a t x
            
      Orᵢ    :  ∀ {a : Set} {t : I → Set} {i : I}
                → Genᵢ a t i → Genᵢ a t i → Genᵢ a t i
           
      μᵢ     :  ∀ {a : I → Set} (i : I) → Genᵢ (a i) a i
      
      Noneᵢ  :  ∀ {a : Set} {t : I → Set} {i : I} → Genᵢ a t i

      Callᵢ  :  ∀ {t : I → Set} {i : I} {J : Set} {s : J → Set}
                → ((j : J) → Genᵢ (s j) s j) → (j : J) → Genᵢ (s j) t i
\end{code}
%</genidef>
\begin{code}

  open GFunctor     ⦃...⦄
  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
  open GMonad       ⦃...⦄

  instance
    Gen-Functor' :
      ∀ {t : Set}
      → GFunctor {i = ⊤} λ a _  → Gen a t
    Gen-Functor' =
      record { _<$>_ = λ f → Ap (Pure f)}

  instance
    Gen-Applicative' :
      ∀ {ℓ} {t : Set ℓ}
      → GApplicative {i = ⊤} λ a _ → Gen a t
    Gen-Applicative' =
      record { pure = Pure ; _<*>_ = Ap }

  instance 
    Gen-Alternative' :
      ∀ {ℓ} {t : Set ℓ}
      → GAlternative {i = ⊤} λ a _ → Gen a t
    Gen-Alternative' =
      record { _∥_ = Or ; empty = None}

\end{code}

%<*gdef>
\begin{code}
  𝔾 : Set → Set
  𝔾 a = Gen a a
\end{code}
%</gdef>

%<*gennat>
\begin{code}
  nat : Gen ℕ ℕ
  nat  =  ⦇ zero   ⦈
       ∥  ⦇ suc μ  ⦈
\end{code}
%</gennat>

\begin{code}
  module A where 
\end{code}

%<*listgenhole>
\begin{code}
    list : ∀ {a : Set} → 𝔾 a → 𝔾 (List a)
    list a =  ⦇ []        ⦈
           ∥  ⦇ {!!} ∷ μ  ⦈
\end{code}
%</listgenhole>

\begin{code}
  module B where 
\end{code}

%<*listgen>
\begin{code}
    list : ∀ {a : Set} → 𝔾 a → 𝔾 (List a)
    list a  =  ⦇ []             ⦈
            ∥  ⦇ (Call  a) ∷ μ  ⦈
\end{code}
%</listgen>

%<*intdef>

\begin{code}
  Interpretation : (Set → Set) → Set
  Interpretation T = ∀ {a t : Set} → 𝔾 t → Gen a t → T a 
\end{code}
%</intdef>

%<*scdef>
\begin{code}
  GenAsList : Set
  GenAsList = Interpretation λ a → ℕ → List a
\end{code}
%</scdef>

%<*scint>
\begin{code}
  asList : GenAsList
  asList gen = {!!}
\end{code}
%</scint>

\begin{code}
  open import Codata.Colist hiding (map; _++_)
  open import Size
\end{code}

%<*intcolist>
\begin{code}
  GenAsColist : Set
  GenAsColist = ∀ {i : Size} → Interpretation λ a → Colist a i
\end{code}
%</intcolist>

\begin{code}
  module C where
\end{code}
  
%<*liftgen>
\begin{code}
    𝔾ᵢ : ∀ {I : Set} → (I → Set) → Set
    𝔾ᵢ {I} P = (i : I) → 𝔾 (P i)
\end{code}
%</liftgen>

\begin{code}
  module D where
    open C
\end{code}

%<*finhole>
\begin{code}
    fin : 𝔾ᵢ Fin
    fin zero     =  None
    fin (suc n)  =  ⦇ zero      ⦈
                 ∥  ⦇ suc {!!}  ⦈
\end{code}
%</finhole>

\begin{code}
  module E where
    open C
\end{code}

%<*findirect>
\begin{code}
    fin : 𝔾ᵢ Fin
    fin zero     =  None
    fin (suc n)  =  ⦇ zero               ⦈
                 ∥  ⦇ suc (Call (fin n)) ⦈
\end{code}
%</findirect>

\begin{code}
  module F where
\end{code}

%<*gidef>
\begin{code}
  𝔾ᵢ : ∀ {I : Set} → (I → Set) → Set
  𝔾ᵢ {I} P = (i : I) → Genᵢ (P i) P i
\end{code}
%</gidef>

\begin{code}

  instance
    Genᵢ-Functor' :
      ∀ {ℓ} {I : Set} {t : I → Set ℓ}
      → GFunctor λ a x → Genᵢ a t x
    Genᵢ-Functor' =
      record { _<$>_ = λ f x → Apᵢ (Pureᵢ f) x}

  instance
    Genᵢ-Applicative' :
      ∀ {ℓ} {I : Set} {t : I → Set ℓ}
      → GApplicative λ a x → Genᵢ a t x
    Genᵢ-Applicative' =
      record { pure = Pureᵢ ; _<*>_ = Apᵢ }

  instance 
    Genᵢ-Alternative' :
      ∀ {ℓ} {I : Set} {t : I → Set ℓ}
      → GAlternative λ a x → Genᵢ (a) t x
    Genᵢ-Alternative' =
      record { _∥_ = Orᵢ ; empty = Noneᵢ}

  module G where
\end{code}

%<*genfin>
\begin{code}
    fin : 𝔾ᵢ Fin
    fin zero     =  empty
    fin (suc n)  =  ⦇ zero        ⦈
                 ∥  ⦇ suc (μᵢ n)  ⦈ 
\end{code}
%</genfin>

\begin{code}
  open G

  data WS : ℕ → Set where
    var : ∀ {n : ℕ} → Fin n → WS n
    abs : ∀ {n : ℕ} → WS (suc n) → WS n
    app : ∀ {n : ℕ} → WS n → WS n → WS n

\end{code}

%<*wellscoped>
\begin{code}
  term : 𝔾ᵢ WS
  term n  =  ⦇ var (Callᵢ {i = n} fin n)  ⦈
          ∥  ⦇ abs (μᵢ (suc n))           ⦈
          ∥  ⦇ app (μᵢ n) (μᵢ n)          ⦈
\end{code}
%</wellscoped>

\begin{code}
  merge : ∀ {a : Set} → List a → List a → List a
  merge [] ys        = ys
  merge (x ∷ xs) ys  = x ∷ merge ys xs
\end{code}

%<*tolist>
\begin{code}
  toList : Interpretation λ a → ℕ → List a
  toList _ _           zero     = []
  toList g (Or g1 g2)  (suc n)  = merge (toList g g1 (suc n)) (toList g g2 (suc n))
  toList g (Ap g1 g2)  (suc n)  =
    concatMap (λ f → map f (toList g g2 (suc n))) (toList g g1 (suc n))
  toList _ (Pure x)    (suc n)  = x ∷ []
  toList _ None        (suc n)  = []
  toList g μ           (suc n)  = toList g g n
  toList _ (Call g)    (suc n)  = toList g g (suc n)
\end{code}
%</tolist>

%<*tolistbind>
\begin{code}
  toList g (Bind g₁ f) (suc n) = concatMap (λ x → toList g (f x) n) (toList g g₁ (suc n))
\end{code}
%</tolistbind>

\begin{code}
  module H where
\end{code}
%<*sigmagenhole>
\begin{code}
    gen-Σ : ∀ {I : Set} {P : I → Set} → 𝔾 I → ((i : I) → 𝔾 (P i)) → 𝔾 (Σ[ i ∈ I ] P i)
    gen-Σ gi gp = ⦇ (λ x y → x , {!!} ) (Call gi) (Call (gp {!!} )) ⦈
\end{code}
%</sigmagenhole>

\begin{code}
  module I where

    instance
      Gen-Monad' :
        ∀ {ℓ} {t : Set ℓ}
        → GMonad {i = ⊤} λ a _ → Gen a t
      Gen-Monad' =
        record { _>>=_ = Bind }  
\end{code}
%<*sigmagen>
\begin{code}
    gen-Σ : ∀ {I : Set} {P : I → Set} → 𝔾 I → ((i : I) → 𝔾 (P i)) → 𝔾 (Σ[ i ∈ I ] P i)
    gen-Σ gi gp = (Call gi) >>= λ i → (Call (gp i)) >>= λ p → Pure (i , p)
\end{code}
%</sigmagen>


