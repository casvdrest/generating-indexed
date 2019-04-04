open import AgdaGen.Base
open import Level

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

  _<*>_ :  ∀ {ℓ} {a b t : Set ℓ} → Gen (a → b) t → Gen a t → Gen b t
  f <*> g = genAp f g

  _⊛_ : ∀ {ℓ} {a b t : Set ℓ} → Gen (a → b) t → Gen a t → Gen b t
  _⊛_ = _<*>_

  pure : ∀ {ℓ} {a t : Set ℓ} → a → Gen a t
  pure = genPure

  _>>=_ : ∀ {ℓ} {a b t : Set ℓ} → Gen a t → (a → Gen b t) → Gen b t
  _>>=_ = genBind

  _>>_ : ∀ {ℓ} {a b t : Set ℓ} → Gen a t → Gen b t → Gen b t
  f >> g = f >>= λ _ → g
