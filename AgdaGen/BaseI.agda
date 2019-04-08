open import AgdaGen.Data
open import AgdaGen.Base

open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Data.Empty
open import Data.Unit

open import Level renaming (suc to sucL; zero to zeroL)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl; cong; cong₂)

module AgdaGen.BaseI where

  infixr 20 _∥ᵢ_

  data Genᵢ {ℓ k} {i : Set k} : (i → Set ℓ) → (i → Set ℓ) → i → Set (k ⊔ sucL ℓ) where
    Pureᵢ : ∀ {a t : i → Set ℓ} {x : i} → a x → Genᵢ a t x
    Apᵢ   : ∀ {a b t : i → Set ℓ} {x : i} {y : i} → Genᵢ (λ _ → b y → a x) t x → Genᵢ b t y → Genᵢ a t x
    Bindᵢ : ∀ {a b t : i → Set ℓ} {x : i} {y : i} → Genᵢ a t y → (a y → Genᵢ b t x) → Genᵢ b t x
    _∥ᵢ_  : ∀ {a t : i → Set ℓ} {x : i} → Genᵢ a t x → Genᵢ a t x → Genᵢ a t x
    μᵢ    : ∀ {a : i → Set ℓ} (x : i) → Genᵢ a a x
    Noneᵢ : ∀ {a t : i → Set ℓ} {x : i} → Genᵢ a t x
    Call  : ∀ {t : i → Set ℓ} {x : i} {b : Set ℓ} → Gen b b → Genᵢ (λ _ → b) t x
    Callᵢ : ∀ {t : i → Set ℓ} {x : i} {j : Set ℓ} {s : j → Set ℓ} → ((y : j) → Genᵢ s s y) → (y : j) → Genᵢ (λ _ → s y) t x

  interpretᵢ : ∀ {ℓ k} {i : Set k} {a t : i → Set ℓ} → ((y : i) → Genᵢ t t y) → (x : i) → Genᵢ a t x → ℕ → List (a x)
  interpretᵢ tg x g zero = []
  interpretᵢ tg x (Noneᵢ ) (suc n) = []
  interpretᵢ tg x (Pureᵢ v) (suc n) = [ v ]
  interpretᵢ tg x (Apᵢ {y = y} g₁ g₂) (suc n) = concatMap (λ f → map f (interpretᵢ tg y g₂ (suc n) )) (interpretᵢ tg x g₁ (suc n))
  interpretᵢ tg x (Bindᵢ {y = y} g f) (suc n) = concatMap (λ v → interpretᵢ tg x (f v) (suc n)) (interpretᵢ tg y g (suc n))
  interpretᵢ tg x (g₁ ∥ᵢ g₂) (suc n) = merge (interpretᵢ tg x g₁ (suc n)) (interpretᵢ tg x g₂ (suc n))
  interpretᵢ tg x (μᵢ .x) (suc n) = interpretᵢ tg x (tg x) n
  interpretᵢ tg x (Call g) (suc n) = interpret g g (suc n)
  interpretᵢ tg x (Callᵢ g y) (suc n) = interpretᵢ g y (g y) (suc n)

  𝔾ᵢ : ∀ {ℓ k} {i : Set k} → (i → Set ℓ) → i → Set (k ⊔ (sucL ℓ))
  𝔾ᵢ f x = Genᵢ f f x

  ⟨_⟩ᵢ : ∀ {ℓ k} {i : Set k} {f : i → Set ℓ} → ((x : i) → 𝔾ᵢ f x) → (x : i) → ℕ → List (f x)
  ⟨ g ⟩ᵢ x = interpretᵢ g x (g x) 

  fin : (n : ℕ) → Genᵢ Fin Fin n
  fin zero = Noneᵢ
  fin (suc n) = Pureᵢ zero ∥ᵢ Apᵢ (Pureᵢ suc) (μᵢ n)

  _<*>_ : ∀ {ℓ k} {i : Set k} {a b t : i → Set ℓ} {x : i} {y : i} → Genᵢ (λ _ → a y → b x) t x → Genᵢ a t y → Genᵢ b t x
  _<*>_ = Apᵢ
  
  _>>=_ : ∀ {ℓ k} {i : Set k} {a b t : i → Set ℓ} {x : i} {y : i} → Genᵢ a t y → (a y → Genᵢ b t x) → Genᵢ b t x 
  _>>=_ = Bindᵢ

  _>>_ : ∀ {ℓ k} {i : Set k} {a b t : i → Set ℓ} {x : i} {y : i} → Genᵢ a t y → Genᵢ b t x → Genᵢ b t x 
  f >> g = f >>= λ _ → g

  pure : ∀ {ℓ k} {i : Set k} {a t : i → Set ℓ} {x : i} → a x → Genᵢ a t x
  pure = Pureᵢ

  fin' : (n : ℕ) → Genᵢ Fin Fin n
  fin' zero = Noneᵢ
  fin' (suc n) = pure zero ∥ᵢ
    do r ← μᵢ n
       pure (suc r)

  data Lam : ℕ → Set where
    Abs : ∀ {n : ℕ} → Lam (suc n) → Lam n
    App : ∀ {n : ℕ} → Lam n → Lam n → Lam n
    Var : ∀ {n : ℕ} → Fin n → Lam n
  
  lam : (n : ℕ) → Genᵢ Lam Lam n
  lam n = ⦇ Var (Callᵢ {x = n} fin n) ⦈
        ∥ᵢ ⦇ Abs (μᵢ (suc n)) ⦈
        ∥ᵢ ⦇ App (μᵢ n) (μᵢ n) ⦈
