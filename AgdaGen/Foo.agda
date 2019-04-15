open import Data.Nat hiding (_≤_; _+_; _≟_)
open import Data.Sum

open import Relation.Binary.PropositionalEquality

module Foo where

  data _∧_ (a : Set) (b : Set) : Set where
    _,_ : a → b → a ∧ b

  data _∨_ (a : Set) (b : Set) : Set where
    Left  : a → a ∨ b
    Right : b → a ∨ b

  uncurry : ∀ {P Q R : Set} → (P → (Q → R)) → (P ∧ Q) → R
  uncurry f (x , y) = f x y

  prop : ∀ {P Q R : Set} → (P ∨ Q) ∧ R → (P ∧ R) ∨ (Q ∧ R)
  prop (Left x , y) = Left (x , y)
  prop (Right x , y) = Right (x , y)

  data Exists (I : Set) (P : I → Set) : Set where
    In : (i : I) → P i → Exists I P 

  prop2 : Exists ℕ λ n → n ≡ 10
  prop2 = In 10 refl

  data _≤_ : ℕ → ℕ → Set where 
    z≤m : ∀ {m : ℕ} → 0 ≤ m
    s≤s : ∀ {n m : ℕ} → n ≤ m → (suc n) ≤ (suc m)

  prop3 : ∀ {n : ℕ} → 0 ≤ n
  prop3 = z≤m

  lemma : ∀ {n : ℕ} → n ≤ suc n
  lemma {zero} = z≤m
  lemma {suc n} = s≤s lemma
  
  prop4 : ∀ {n : ℕ} → Exists ℕ λ m → n ≤ m
  prop4 {n} = In (suc n) lemma

  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  suc n + m = suc (n + m)

  +-right-ident : ∀ {n : ℕ} → n + 0 ≡ n
  +-right-ident {zero} = refl
  +-right-ident {suc n} = cong suc +-right-ident

  +-lemma : ∀ {n m : ℕ} → n + (suc m) ≡ suc (n + m)
  +-lemma {zero} {m} = refl
  +-lemma {suc n} {m} = cong suc +-lemma

  +-comm : ∀ {n m : ℕ} → n + m ≡ m + n
  +-comm {zero} {m} rewrite +-right-ident {m} = refl
  +-comm {suc n} {m} rewrite +-lemma {m} {n} = cong suc (+-comm {n} {m})

  data ⊥ : Set 

  _≟_ : (n : ℕ) → (m : ℕ) → n ≡ m ⊎ (n ≡ m → ⊥)
  zero ≟ zero = inj₁ refl
  zero ≟ suc m = inj₂ λ { () }
  suc n ≟ zero = inj₂ λ { () }
  suc n ≟ suc m with n ≟ m
  (suc n ≟ suc m) | inj₁ p = inj₁ (cong suc p)
  (suc n ≟ suc m) | inj₂ p = inj₂ λ { refl → p refl }
