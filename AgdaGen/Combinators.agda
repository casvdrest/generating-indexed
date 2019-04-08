open import AgdaGen.Base
open import Level renaming (zero to zeroL; suc to sucL)

module AgdaGen.Combinators where
  

  -- 'Functor' instance for the 'Gen' type
  genMap : ∀ {ℓ} {a b t : Set ℓ} → (a → b) → Gen a t → Gen b t
  genMap f g = Ap (Pure f) g

  -- 'Applicative' instance for the 'Gen' type
  genPure : ∀ {ℓ} {a t : Set ℓ} → a → Gen a t
  genPure = Pure

  genAp : ∀ {ℓ} {a b t : Set ℓ} → Gen (a → b) t → Gen a t → Gen b t
  genAp = Ap

  -- 'Monad' instance for the 'Gen' type
  genBind : ∀ {ℓ} {a b t : Set ℓ} → Gen a t → (a → Gen b t) → Gen b t
  genBind = Bind

  record Functor {ℓ} (f : Set ℓ → Set (sucL ℓ)) : Set (sucL ℓ) where
    field _<$>_ : ∀ {a b : Set ℓ} → (a → b) → f a → f b
    
  record Applicative {ℓ} (f : Set ℓ → Set (sucL ℓ)) : Set (sucL ℓ) where
    field pure : ∀ {a : Set ℓ} → a → f a
    field _<*>_ : ∀ {a b : Set ℓ} → f (a → b) → f a → f b

  record Monad {ℓ} (m : Set ℓ → Set (sucL ℓ)) : Set (sucL ℓ) where
    field _>>=_ : ∀ {a b : Set ℓ} → m a → (a → m b) → m b

  instance
    Gen-Functor : ∀ {ℓ} {t : Set ℓ} → Functor λ a → Gen a t
    Gen-Functor = record { _<$>_ = genMap }

  instance
    Gen-Applicative : ∀ {ℓ} {t : Set ℓ} → Applicative λ a → Gen a t
    Gen-Applicative = record { pure = genPure ; _<*>_ = genAp }

  instance
    Gen-Monad : ∀ {ℓ} {t : Set ℓ} → Monad λ a → Gen a t
    Gen-Monad = record { _>>=_ = genBind }

  open Applicative ⦃...⦄
  open Monad ⦃...⦄

  _⊛_ : ∀ {ℓ} {f : Set ℓ → Set (sucL ℓ)} ⦃ _ : Applicative f ⦄ { a b : Set ℓ} → f (a → b) → f a → f b
  _⊛_ = _<*>_

  _>>_ : ∀ {ℓ} {m : Set ℓ → Set (sucL ℓ)} ⦃ _ : Monad m ⦄ {a b : Set ℓ} → m a → m b → m b 
  f >> g = f >>= λ _ → g 
