open import src.Data
open import Level using (_⊔_)

open import Data.Nat hiding (_⊔_)
open import Data.Bool
open import Data.List using (List; map; [_]; concatMap; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module src.Omega.Base where

  𝔾 : Set → ℕ → Set 
  𝔾 a m = (p : Σ[ n ∈ ℕ ] n ≡ m) → List a  

  𝔾-map : ∀ {a b : Set} {n : ℕ} → (a → b) → 𝔾 a n → 𝔾 b n
  𝔾-map f x n = map f (x n)

  instance
    𝔾-functor : ∀ {n : ℕ} → RawFunctor λ a → 𝔾 a n
    𝔾-functor = record { _<$>_ = 𝔾-map }

  𝔾-pure : ∀ {a : Set} {n : ℕ} → a → 𝔾 a n
  𝔾-pure x _ = [ x ]
  
  list-ap : ∀ {ℓ} {a b : Set ℓ} → List (a → b) → List a → List b
  list-ap fs xs = concatMap (λ f → map f xs) fs
  
  𝔾-ap : ∀ {a b : Set} {n : ℕ} → 𝔾 (a → b) n → 𝔾 a n → 𝔾 b n
  𝔾-ap f x n = list-ap (f n) (x n)

  instance
    𝔾-applicative : ∀ {n : ℕ} → RawApplicative λ a → 𝔾 a n
    𝔾-applicative = record { pure = 𝔾-pure 
                           ; _⊛_  = 𝔾-ap
                           }

  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawApplicative ⦃...⦄ using (pure; _⊛_)

  _<*>_ : ∀ {ℓ} {a b : Set ℓ} {f : Set ℓ → Set ℓ}
            ⦃ _ : RawApplicative f ⦄
          → f (a → b) → f a → f b
  _<*>_ = _⊛_

  infixr 2 _∥_

  _∥_ : ∀ {a : Set} {n : ℕ} → 𝔾 a n → 𝔾 a n → 𝔾 a n
  x ∥ y = λ n → merge (x n) (y n)

  𝔾-bind : ∀ {a b : Set} {n : ℕ} → 𝔾 a n → (a → 𝔾 b n) → 𝔾 b n
  𝔾-bind f g = λ n → concatMap ((λ x → x n) ∘ g) (f n)

  instance
    𝔾-monad : ∀ {n : ℕ} → RawMonad λ a → 𝔾 a n
    𝔾-monad = record { return = 𝔾-pure
                     ; _>>=_  = 𝔾-bind
                     }

  uninhabited : ∀ {a : Set} {n : ℕ} → 𝔾 a n
  uninhabited _ = []

  choice : ∀ {a : Set} {n : ℕ} → List (𝔾 a n) → 𝔾 a n
  choice xs = λ n → mergeₙ (map (λ x → x n) xs )

  fixed : (ℕ → Set) → Set
  fixed a = ∀ {n : ℕ} → a n → a n

  infix 1 ⟪_⟫

  ⟪_⟫ : (ℕ → Set) → Set
  ⟪ a ⟫ = fixed a

  𝔾ᵢ : ∀ {i : Set} → (i → Set) → ℕ → Set
  𝔾ᵢ {i = i} a n = (x : i) → 𝔾 (a x) n

  _∥ᵢ_ : ∀ {i : Set} {a : i → Set} {n : ℕ} → 𝔾ᵢ a n → 𝔾ᵢ a n → 𝔾ᵢ a n 
  (f ∥ᵢ g) i = f i ∥ g i

  choiceᵢ : ∀ {i : Set} {a : i → Set} {n : ℕ} → List (𝔾ᵢ a n) → 𝔾ᵢ a n
  choiceᵢ xs i = choice (map (λ x → x i) xs)

  fix : ∀ {a : Set} → (m : ℕ) → ⟪ 𝔾 a ⟫ → 𝔾 a m
  fix zero f (.0 , refl) = []
  fix (suc m) f (.suc m , refl) = f {m} (fix m f) (m , refl)

  fixᵢ : ∀ {i : Set} {a : i → Set} → (m : ℕ) → ⟪ 𝔾ᵢ a ⟫ → 𝔾ᵢ a m
  fixᵢ zero f i (.0 , refl) = []
  fixᵢ (suc m) f i (.(suc m) , refl) = f {m} (fixᵢ m f) i (m , refl)


  ⟨_⟩ : ∀ {a : Set} {n : ℕ} → ⟪ 𝔾 a ⟫ → 𝔾 a n
  ⟨_⟩ {n = n} = fix n

  ⟨_⟩ᵢ : ∀ {i : Set} {a : i → Set} {n : ℕ} → ⟪ 𝔾ᵢ a ⟫ → 𝔾ᵢ a n
  ⟨_⟩ᵢ {n = n} = fixᵢ n

  𝔾-run : ∀ {a : Set } → ⟪ 𝔾 a ⟫ → ℕ → List a
  𝔾-run f n = fix n f (n , refl)


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

  infix 3 〖_
  infix 1 _〗
  infixl 2 _⋎_

  〖_ : ∀ {i : Set} {a : i → Set} → ⟪ 𝔾ᵢ a ⟫ → List ⟪ 𝔾ᵢ a ⟫
  〖 x = [ x ]

  _〗 : ∀ {i : Set} {a : i → Set} → List ⟪ 𝔾ᵢ a ⟫ → ⟪ 𝔾ᵢ a ⟫
  (xs 〗) μ = choiceᵢ (map (λ x → x μ) xs) 

  _⋎_ : ∀ {i : Set} {a : i → Set} → List ⟪ 𝔾ᵢ a ⟫ → ⟪ 𝔾ᵢ a ⟫ → List ⟪ 𝔾ᵢ a ⟫
  xs ⋎ x = x ∷ xs 

  -- TODO : mailing list over omega monad
  --        refactoren met verschillende implementaties

