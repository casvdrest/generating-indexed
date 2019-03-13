{-# OPTIONS --type-in-type #-}

open import src.Data
open import Level using (_⊔_)

open import Data.Nat hiding (_⊔_)
open import Data.Bool
open import Data.List using (List; map; [_]; concatMap; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Unit
open import Data.Fin
open import Data.Maybe using (Maybe; just; nothing)

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module src.Gen.Base where

  -- The generator type. The `a` type parameter marks the output type of the
  -- generator. The resultin type family is indexed by a type marking the type
  -- of values produced by recursive positions. 
  data Gen (a : Set) : Set → Set where

    -- Marks choice between generators
    _∥_   : ∀ {t : Set} → Gen a t → Gen a t → Gen a t

    -- Applies the values generated by one generator to another
    Ap    : ∀ {b t : Set} → Gen (b → a) t → Gen b t → Gen a t

    -- Lift a single value into the generator type
    Pure  : ∀ {t : Set} → a → Gen a t

    -- Monadic bind for generators
    Bind  : ∀ {b t : Set} → Gen b t → (b → Gen a t) → Gen a t

    -- Generator that produces no elements at all. 
    None  : ∀ {t : Set} → Gen a t

    -- Marks a recursive positions
    μ     : Gen a a

    -- Call to an external generator. Using this constructor is
    -- only different from including the generator itself if the
    -- called generator itself contains one or more recursive
    -- positions. 
    `_    : ∀ {t : Set} → Gen a a → Gen a t

  -- Type synonym for 'closed' generators, e.g. generators whose recursive
  -- positions refer to the same type as the generator as a whole. 
  𝔾 : Set → Set
  𝔾 a = Gen a a

  -- Type synonym for 'closed' generators for function types
  co𝔾 : Set → Set
  co𝔾 a = ∀ {b : Set} → 𝔾 b → 𝔾 (a → b)

  -- 'Functor' instance for the generator type
  instance
    Gen-functor : ∀ {t : Set} → RawFunctor (λ a → Gen a t)
    Gen-functor = record { _<$>_ = Ap ∘ Pure }

  -- 'Applicative' instance for the generator type
  instance
    Gen-applicative : ∀ {t : Set} → RawApplicative λ a → Gen a t
    Gen-applicative = record { pure = Pure 
                           ; _⊛_  = Ap
                           }

  -- Bring 'Applicative' and 'Functor' into scope
  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawApplicative ⦃...⦄ using (pure; _⊛_)
  
  -- We need this to allow the use of idiom brackets
  _<*>_ : ∀ {ℓ} {a b : Set ℓ} {f : Set ℓ → Set ℓ}
            ⦃ _ : RawApplicative f ⦄
          → f (a → b) → f a → f b
  _<*>_ = _⊛_

  -- 'Monad' instance for the generator type
  instance
    Gen-monad : ∀ {t : Set} → RawMonad λ a → Gen a t
    Gen-monad =
      record { return = Pure
             ; _>>=_  = Bind
             }

  -- Interpretation function for generators. Interprets a a value of the Gen type as a
  -- function from `ℕ` to `List a`.
  --
  -- The first parameter is the generator to be interpreted, the second parameter is a
  -- closed generator that is referred to by recursive positions.
  interpret : ∀ {a t : Set} → Gen a t → 𝔾 t → ℕ → List a
  interpret (g         ) tg zero = []
  interpret (g₁ ∥ g₂   ) tg (suc n) =
    merge (interpret g₁ tg (suc n)) (interpret g₂ tg (suc n))
  interpret (Ap g₁ g₂  ) tg (suc n) =
    concatMap (λ f → map f (interpret g₂ tg (suc n))) (interpret g₁ tg (suc n))
  interpret (Pure x    ) tg (suc n) = [ x ]
  interpret (Bind g₁ g₂) tg (suc n) =
    (flip concatMap) (interpret g₁ tg (suc n)) (λ x → interpret (g₂ x) tg (suc n))
  interpret (None      ) tg (suc n) = []
  interpret (μ         ) tg (suc n) =
    interpret tg tg n
  interpret (` g       ) tg (suc n) =
    interpret g g (suc n)

  -- Interpret a closed generator as a function from `ℕ` to `List a`
  ⟨_⟩ : ∀ {a : Set} → Gen a a → ℕ → List a
  ⟨ g ⟩ = interpret g g
  
{-
  infix 3 〖_
  infix 1 _〗
  infixl 2 _⋎_

  〖_ : ∀ {i : Set} {a : i → Set} → ⟪ 𝔾ᵢ a ⟫ → List ⟪ 𝔾ᵢ a ⟫
  〖 x = [ x ]

  _〗 : ∀ {i : Set} {a : i → Set} → List ⟪ 𝔾ᵢ a ⟫ → ⟪ 𝔾ᵢ a ⟫
  (xs 〗) μ = choiceᵢ (map (λ x → x μ) xs) 

  _⋎_ : ∀ {i : Set} {a : i → Set} → List ⟪ 𝔾ᵢ a ⟫ → ⟪ 𝔾ᵢ a ⟫ → List ⟪ 𝔾ᵢ a ⟫
  xs ⋎ x = x ∷ xs
-}
