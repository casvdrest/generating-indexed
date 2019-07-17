open import Model.Base

open import Data.Unit


open import Level renaming (suc to sucL; zero to zeroL)

-- Contains some basic combinators for generators.
--
-- Unfortunately, the Gen and Genᵢ type do not fit into the
-- existing functionality of the standard library, but we can still
-- utilize do-notatino and idiom brackets by overloading the
-- necessary operators. 
module Model.Combinators where

  -- 'map', but for indexed generators
  genMap :
    ∀ {ℓ k} {i : Set k} {a b : Set ℓ} {t : i → Set ℓ} {x : i}
    → (a → b) → Gen a t x → Gen b t x
  genMap {x = x} f g = Ap (Pure f) g

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

  ------ Indexed generators ------

  instance
    Gen-Functor :
      ∀ {ℓ k} {i : Set k} {t : i → Set ℓ}
      → GFunctor (λ a x → Gen a t x)
    Gen-Functor =
      record { _<$>_ = genMap } 

  instance
    Gen-Applicative :
      ∀ {ℓ k} {i : Set k} {t : i → Set ℓ}
      → GApplicative λ a x → Gen a t x
    Gen-Applicative =
      record { pure = Pure ; _<*>_ = Ap }

  instance
    Gen-Monad :
      ∀ {ℓ k} {i : Set k} {t : i → Set ℓ}
      → GMonad λ a x → Gen a t x
    Gen-Monad =
      record { _>>=_  = Bind }

  instance
    Gen-Alternative :
      ∀ {ℓ k} {i : Set k} {t : i → Set ℓ}
      → GAlternative λ a x → Gen a t x
    Gen-Alternative =
      record { _∥_ = Or ; empty = None }
