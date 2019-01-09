open import src.Data

open import Data.Nat
open import Data.List using (List; map; [_]; concatMap; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Function

module src.Omega.Base where

  ω : ∀ {ℓ} → Set ℓ → Set ℓ
  ω a = ℕ → List a

  ω-map : ∀ {ℓ} {a b : Set ℓ} → (a → b) → ω a → ω b
  ω-map f x n = map f (x n)

  instance
    ω-functor : ∀ {ℓ} → RawFunctor {ℓ} ω
    ω-functor = record { _<$>_ = ω-map }

  ω-pure : ∀ {ℓ} {a : Set ℓ} → a → ω a
  ω-pure x _ = [ x ]
  list-ap : ∀ {ℓ} {a b : Set ℓ} → List (a → b) → List a → List b
  list-ap fs xs = concatMap (λ f → map f xs) fs
  
  ω-ap : ∀ {ℓ} {a b : Set ℓ} → ω (a → b) → ω a → ω b
  ω-ap f x n = list-ap (f n) (x n)

  instance
    ω-applicative : ∀ {ℓ} → RawApplicative {ℓ} ω
    ω-applicative = record { pure = ω-pure 
                           ; _⊛_  = ω-ap
                           }

  ω-bind : ∀ {ℓ} {a b : Set ℓ} → ω a → (a → ω b) → ω b
  ω-bind f g = λ n → concatMap ((λ x → x n) ∘ g) (f n)

  instance
    ω-monad : ∀ {ℓ} → RawMonad {ℓ} ω
    ω-monad = record { return = ω-pure
                     ; _>>=_  = ω-bind
                     }
  
  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawApplicative ⦃...⦄ using (pure; _⊛_)

  _<*>_ : ∀ {ℓ} {a b : Set ℓ} {f : Set ℓ → Set ℓ}
            ⦃ _ : RawApplicative f ⦄
          → f (a → b) → f a → f b
  _<*>_ = _⊛_

  infixr 2 _∥_  

  _∥_ : ∀ {ℓ} {a : Set ℓ} → ω a → ω a → ω a
  x ∥ y = λ n → merge (x n) (y n)

  κ : ∀ {ℓ} {a : Set ℓ} → ω a → ω a
  κ f zero = []
  κ f (suc n) = f n

  fixed : ∀ {ℓ} → Set ℓ → Set ℓ
  fixed a = a → a

  infix 1 ⟪_⟫

  ⟪_⟫ : ∀ {ℓ} → Set ℓ → Set ℓ
  ⟪ a ⟫ = fixed a

  {-# TERMINATING #-}
  fix : ∀ {ℓ} {a : Set ℓ} → ⟪ ω a ⟫ → ω a
  fix f zero = []
  fix f (suc n) = f (fix f) n

  uninhabited : ∀ {ℓ} {a : Set ℓ} → ω a
  uninhabited _ = []

  ωᵢ : ∀ {ℓ} {i : Set ℓ} → (i → Set ℓ) → Set ℓ
  ωᵢ {i = i} a = (x : i) → ω (a x)

  {-# TERMINATING #-}
  fixᵢ : ∀ {ℓ} {i : Set ℓ} {a : i → Set ℓ} → ⟪ ωᵢ a ⟫ → ωᵢ a
  fixᵢ f i zero = []
  fixᵢ f i (suc n) = f (fixᵢ f) i n

  ⟨_⟩ : ∀ {ℓ} {a : Set ℓ} → ⟪ ω a ⟫ → ω a
  ⟨_⟩ = fix

  ⟨_⟩ᵢ : ∀ {ℓ} {i : Set ℓ} {a : i → Set ℓ} → ⟪ ωᵢ a ⟫ → ωᵢ a
  ⟨_⟩ᵢ = fixᵢ

  Σ-map : ∀ {a : Set} {P Q : a → Set}
          → (∀ {y : a} → (P y → Q y))
          -------------------------------------
          → Σ[ x ∈ a ] P x → Σ[ x ∈ a ] Q x
  Σ-map f (fst , snd) = fst , f snd
          
  Σ-bimap : ∀ {a b : Set} {P : a → Set} {Q : b → Set}       
            → (f : a → b) → (∀ {y : a} → P y → Q (f y))
            -------------------------------------------
            → Σ[ x ∈ a ] P x → Σ[ x ∈ b ] Q x
  Σ-bimap f g (fst , snd) = f fst , g snd

  Σ₁ : ∀ {a : Set} {P : a → Set} → Σ[ x ∈ a ] P x → a
  Σ₁ (fst , _) = fst

  Σ₂ : ∀ {a : Set} {P : a → Set} → (p : Σ[ x ∈ a ] P x) → P (Σ₁ p)
  Σ₂ (_ , snd) = snd

  

  -- TODO : deep embedding van omega
  --        mailing list over omega monad
  --        typed lambda calculus
  --        refactoren met verschillende implementaties
