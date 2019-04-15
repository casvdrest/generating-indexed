open import AgdaGen.Base

open import Data.Unit

open import Level renaming (suc to sucL; zero to zeroL)

-- Contains some basic combinators for generators.
--
-- Unfortunately, the Gen and Genᵢ type do not fit into the
-- existing functionality of the standard library, but we can still
-- utilize do-notatino and idiom brackets by overloading the
-- necessary operators. 
module AgdaGen.Combinators where

  genMap :
    ∀ {ℓ k} {a b t : Set ℓ}
    → (a → b) → Gen {ℓ} {k} a t → Gen {ℓ} {k} b t
  genMap f g = Ap (Pure f) g

  genMapᵢ :
    ∀ {ℓ k} {i : Set k} {a b t : i → Set ℓ} {x : i}
    → (a x → b x) → Genᵢ a t x → Genᵢ b t x
  genMapᵢ f g = Apᵢ (Pureᵢ f) g
  
  record GFunctor {ℓ k} {i : Set k} (f : (i → Set ℓ) → i → Set (sucL ℓ ⊔ sucL k)) :
         Set (sucL ℓ ⊔ sucL k) where
    infix 30 _<$>_
    field _<$>_ : ∀ {a b : i → Set ℓ} {x : i}
                → (a x → b x) → f a x → f b x

  record GApplicative {ℓ k} {i : Set k} (f : (i → Set ℓ) → i → Set (sucL ℓ ⊔ sucL k)) :
         Set (sucL ℓ ⊔ sucL k) where
    field pure  : ∀ {a : i → Set ℓ} {x : i}
                → a x → f a x
    field _<*>_ : ∀ {a b : i → Set ℓ} {x y : i}
                → f (λ _ → a y → b x) x → f a y → f b x 

  record GMonad {ℓ k} {i : Set k} (m : (i → Set ℓ) → i → Set (sucL ℓ ⊔ sucL k)) :
         Set (sucL ℓ ⊔ sucL k) where
    field _>>=_ : ∀ {a b : i → Set ℓ} {x y : i}
                → m a y → (a y → m b x) → m b x

  record GAlternative {ℓ k} {i : Set k} (f : (i → Set ℓ) → i → Set (sucL ℓ ⊔ sucL k))
         : Set (sucL ℓ ⊔ sucL k) where
    infixr 20 _∥_
    field _∥_ : ∀ {a : i → Set ℓ} {x : i}
              → f a x → f a x → f a x 

  record GNullable {ℓ k} {i : Set k} (f : (i → Set ℓ) → i → Set (sucL ℓ ⊔ sucL k))
         : Set (sucL ℓ ⊔ sucL k) where
    field empty : {a : i → Set ℓ} {x : i} → f a x

  open GMonad ⦃...⦄

  _>>_ :
    ∀ {ℓ k} {i : Set k} {a b : i → Set ℓ}
      {x y : i} {m : (i → Set ℓ) → i → Set (sucL ℓ ⊔ sucL k)}
      ⦃ _ : GMonad m ⦄
    → m a y → m b x → m b x
  f >> g = f >>= λ _ → g


  ------- Non-indexed generators ------

  instance
    Gen-Functor :
      ∀ {ℓ} {t : Set ℓ}
      → GFunctor λ a _ → Gen {ℓ} {0ℓ} (a tt) t
    Gen-Functor =
      record { _<$>_ = genMap }

  instance
    Gen-Applicative :
      ∀ {ℓ} {t : Set ℓ}
      → GApplicative λ a _ → Gen {ℓ} {0ℓ} (a tt) t
    Gen-Applicative =
      record { pure = Pure ; _<*>_ = Ap }

  instance
    Gen-Monad :
      ∀ {ℓ} {t : Set ℓ}
      → GMonad λ a _ → Gen {ℓ} {0ℓ} (a tt) t
    Gen-Monad =
      record { _>>=_ = Bind }

  instance 
    Gen-Alternative :
      ∀ {ℓ} {t : Set ℓ}
      → GAlternative λ a _ → Gen {ℓ} {0ℓ} (a tt) t
    Gen-Alternative =
      record { _∥_ = Or }

  instance
    Gen-Nullable :
      ∀ {ℓ} {t : Set ℓ}
      → GNullable λ a _ → Gen {ℓ} {0ℓ} (a tt) t
    Gen-Nullable =
      record { empty = None }

  ------ Indexed generators ------

  instance
    Genᵢ-Functor :
      ∀ {ℓ k} {i : Set k} {t : i → Set ℓ}
      → GFunctor (λ a x → Genᵢ a t x)
    Genᵢ-Functor =
      record { _<$>_ = genMapᵢ } 

  instance
    Genᵢ-Applicative :
      ∀ {ℓ k} {i : Set k} {t : i → Set ℓ}
      → GApplicative λ a x → Genᵢ a t x
    Genᵢ-Applicative =
      record { pure = Pureᵢ ; _<*>_ = Apᵢ }

  instance
    Genᵢ-Monad :
      ∀ {ℓ k} {i : Set k} {t : i → Set ℓ}
      → GMonad λ a x → Genᵢ a t x
    Genᵢ-Monad =
      record { _>>=_ = Bindᵢ }

  instance
    Genᵢ-Alternative :
      ∀ {ℓ k} {i : Set k} {t : i → Set ℓ}
      → GAlternative λ a x → Genᵢ a t x
    Genᵢ-Alternative =
      record { _∥_ = Orᵢ }

  instance
    Genᵢ-Nullable :
      ∀ {ℓ k} {i : Set k} {t : i → Set ℓ}
      → GNullable λ a x → Genᵢ a t x
    Genᵢ-Nullable =
      record { empty = Noneᵢ } 
