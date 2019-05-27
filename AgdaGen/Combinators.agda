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

  -- 'map' for generators. We define this in terms of '<*>' and 'pure'
  -- in order to limit the number of constructors exposed
  genMap :
    ∀ {ℓ k} {a b t : Set ℓ}
    → (a → b) → Gen {ℓ} {k} a t → Gen {ℓ} {k} b t
  genMap f g = Ap (Pure f) g

  -- 'map', but for indexed generators
  genMapᵢ :
    ∀ {ℓ k} {i : Set k} {a b : Set ℓ} {t : i → Set ℓ} {x : i}
    → (a → b) → Genᵢ a t x → Genᵢ b t x
  genMapᵢ {x = x} f g = Apᵢ (Pureᵢ f) g

  -- Functor typeclass for generators 
  record GFunctor {ℓ k} {i : Set k} (f : Set ℓ → i → Set (sucL ℓ ⊔ sucL k)) :
         Set (sucL ℓ ⊔ sucL k) where
    infix 30 _<$>_
    field _<$>_ : ∀ {a b : Set ℓ} {x : i}
                → (a → b) → f a x → f b x

  -- Applicative typeclass for generators
  record GApplicative {ℓ k} {i : Set k} (f : Set ℓ → i → Set (sucL ℓ ⊔ sucL k)) :
         Set (sucL ℓ ⊔ sucL k) where
    field pure  : ∀ {a : Set ℓ} {x : i}
                → a → f a x
    field _<*>_ : ∀ {a b : Set ℓ} {x y : i}
                → f (a → b) x → f a y → f b x 

  -- Applicative typeclass for generators
  record GMonad {ℓ k} {i : Set k} (m : Set ℓ → i → Set (sucL ℓ ⊔ sucL k)) :
         Set (sucL ℓ ⊔ sucL k) where
    field _>>=_ : ∀ {a b : Set ℓ} {x y : i}
                → m a y → (a → m b x) → m b x

  -- Alternative typeclass for generators
  record GAlternative {ℓ k} {i : Set k} (f : Set ℓ → i → Set (sucL ℓ ⊔ sucL k))
         : Set (sucL ℓ ⊔ sucL k) where
    infixr 20 _∥_
    field _∥_ : ∀ {a : Set ℓ} {x : i}
              → f a x → f a x → f a x
    field empty : {a : Set ℓ} {x : i} → f a x

  -- Expose the GMonad class
  open GMonad ⦃...⦄

  -- We need to expose '>>' in order to be able to utilize do-notation
  _>>_ :
    ∀ {ℓ k} {i : Set k} {a b : Set ℓ}
      {x y : i} {m : Set ℓ → i → Set (sucL ℓ ⊔ sucL k)}
      ⦃ _ : GMonad m ⦄
    → m a y → m b x → m b x
  f >> g = f >>= λ _ → g


  ------- Instances for non-indexed generators ------

  instance
    Gen-Functor :
      ∀ {ℓ} {t : Set ℓ}
      → GFunctor {i = Lift ℓ ⊤} λ a _ → Gen {ℓ} {0ℓ} a t
    Gen-Functor =
      record { _<$>_ = genMap }

  instance
    Gen-Applicative :
      ∀ {ℓ} {t : Set ℓ}
      → GApplicative {i = Lift ℓ ⊤} λ a _ → Gen {ℓ} {0ℓ} a t
    Gen-Applicative =
      record { pure = Pure ; _<*>_ = Ap }

  instance
    Gen-Monad :
      ∀ {ℓ} {t : Set ℓ}
      → GMonad {i = Lift ℓ ⊤} λ a _ → Gen {ℓ} {0ℓ} a t
    Gen-Monad =
      record { _>>=_ = Bind }

  instance 
    Gen-Alternative :
      ∀ {ℓ} {t : Set ℓ}
      → GAlternative {k = ℓ} {i = Lift ℓ ⊤} λ a tt → Gen {ℓ} {0ℓ} a t
    Gen-Alternative =
      record { _∥_ = Or ; empty = None }

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
      record { _∥_ = Orᵢ ; empty = Noneᵢ }
