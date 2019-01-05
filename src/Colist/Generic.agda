
{-#  OPTIONS --type-in-type #-}

module src.Generic where

  _∘_ : ∀ {a b c : Set} → (b → c) → (a → b) → (a → c)
  g ∘ f = λ x → g (f (x))

  data _⊕_ (a : Set → Set) (b : Set → Set) : Set → Set where
    inl : ∀ {r : Set} → a r → (a ⊕ b) r
    inr : ∀ {r : Set} → b r → (a ⊕ b) r

  data _⊗_ (a : Set → Set) (b : Set → Set) : Set → Set where
    _,_ : ∀ {r : Set} → a r → b r → (a ⊗ b) r
    
  data 𝒰 (r : Set) : Set where
    U : 𝒰 r

  data ℐ (r : Set) : Set where
    I : r → ℐ r

  data 𝒦 (a : Set) (r : Set) : Set where
    K : a → 𝒦 a r 

  {-# NO_POSITIVITY_CHECK #-}
  data Fix (f : Set → Set) : Set where
    μ : f (Fix f) → Fix f

  ListF : Set → Set → Set
  ListF a =  𝒰 ⊕ (𝒦 a ⊗ ℐ)

  List' : Set → Set
  List' = Fix ∘ ListF

  ℕF : Set → Set
  ℕF = 𝒰 ⊕ ℐ

  ℕ' : Set
  ℕ' = Fix ℕF

  BoolF : Set → Set
  BoolF = 𝒰 ⊕ 𝒰

  Bool' : Set
  Bool' = Fix BoolF

  MaybeF : Set → Set → Set
  MaybeF a = 𝒦 a ⊕ 𝒰

  Maybe' : Set → Set
  Maybe' = Fix ∘ MaybeF

  EitherF : Set → Set → Set → Set
  EitherF a b = 𝒦 a ⊕ 𝒦 b

  Either' : Set → Set → Set
  Either' a b = Fix (EitherF a b)

  PairF : Set → Set → Set → Set
  PairF a b = 𝒦 a ⊗ 𝒦 b

  Pair' : Set → Set → Set
  Pair' a b = Fix (PairF a b)
