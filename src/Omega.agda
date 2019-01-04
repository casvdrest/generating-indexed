import Level as L using (suc)

open import Data.Nat
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; map; [_]; concatMap; []; _∷_)
open import Data.Product using (∃; ∃-syntax; _,_)

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import src.Data

module src.Omega where

  ω : ∀ {ℓ} → Set ℓ → Set ℓ
  ω a = ℕ → List a

  ω-map : ∀ {ℓ} {a b : Set ℓ} → (a → b) → ω a → ω b
  ω-map f x n = map f (x n)

  instance
    functor : ∀ {ℓ} → RawFunctor {ℓ} ω
    functor = record { _<$>_ = ω-map }

  ω-pure : ∀ {ℓ} {a : Set ℓ} → a → ω a
  ω-pure x zero = []
  ω-pure x (suc n) = [ x ]
  
  ω-ap : ∀ {ℓ} {a b : Set ℓ} → ω (a → b) → ω a → ω b
  ω-ap f x n = concatMap (λ f → map f (x n)) (f n)

  instance
    applicative : ∀ {ℓ} → RawApplicative {ℓ} ω
    applicative = record { pure = ω-pure 
                         ; _⊛_  = ω-ap
                         }

  ω-bind : ∀ {ℓ} {a b : Set ℓ} → ω a → (a → ω b) → ω b
  ω-bind f g = λ n → concatMap ((λ x → x n) ∘ g) (f n)

  instance
    monad : ∀ {ℓ} → RawMonad {ℓ} ω
    monad = record { return = ω-pure
                   ; _>>=_  = ω-bind
                   }
  
  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawApplicative ⦃...⦄ using (pure; _⊛_)

  _<*>_ : ∀ {ℓ} {a b : Set ℓ} 
          → ω (a → b) → ω a → ω b
  _<*>_ = ω-ap

  _∥_ : ∀ {ℓ} {a : Set ℓ} → ω a → ω a → ω a
  x ∥ y = λ n → merge (x n) (y n)

  κ : ∀ {ℓ} {a : Set ℓ} → ω a → ω a
  κ f zero = []
  κ f (suc n) = f n

  {-# TERMINATING #-}
  fix : ∀ {ℓ} {a : Set ℓ} → (ω a → ω a) → ω a
  fix f zero = []
  fix f (suc n) = f (fix f) n

  bools : ω Bool
  bools = ⦇ true ⦈
        ∥ ⦇ false ⦈

  maybes : ∀ {ℓ} {a : Set ℓ} → ω a → ω (Maybe a)
  maybes a = ⦇ nothing ⦈
           ∥ ⦇ just (κ a)  ⦈

  nats : ω ℕ → ω ℕ
  nats μ = ⦇ zero  ⦈
         ∥ ⦇ suc μ ⦈

  lists : ∀ {ℓ} {a : Set ℓ} → ω a → ω (List a) → ω (List a)
  lists a μ = ⦇ [] ⦈
            ∥ ⦇ (κ a) ∷ μ ⦈

  pairs : ∀ {ℓ} {a b : Set ℓ} → ω a → ω b → ω (a ⊗ b)
  pairs a b = ⦇ a , b ⦈

  eithers : ∀ {ℓ} {a b : Set ℓ} → ω a → ω b → ω (a ⊕ b)
  eithers a b = ⦇ inl (κ a) ⦈
              ∥ ⦇ inr (κ b) ⦈
  
  prop1 : (fix nats) 10 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []
  prop1 = refl

  prop2 : bools 10 ≡ true ∷ false ∷ []
  prop2 = refl

  prop3 : maybes (fix nats) 10 ≡ nothing ∷ just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷ just 4 ∷ just 5 ∷ just 6 ∷ just 7 ∷ []
  prop3 = refl

  prop4 : fix (lists (fix nats)) 5  ≡ [] ∷ (0 ∷ []) ∷ (0 ∷ 0 ∷ []) ∷ (1 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ []
  prop4 = refl
  
  _↝_ : ∀ {ℓ} {a : Set ℓ} → ω a → a → Set ℓ
  f ↝ x = ∃[ n ] (x ∈ f n)

  ∈-rewr : ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a} → xs ≡ ys → x ∈ xs → x ∈ ys
  ∈-rewr refl x = x

  merge-empty-sym : ∀ {ℓ} {a : Set ℓ} {xs : List a} → merge xs [] ≡ merge [] xs
  merge-empty-sym {xs = []} = refl
  merge-empty-sym {xs = x ∷ xs} = refl

  merge-sym : ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a} → x ∈ merge ys xs → x ∈ merge xs ys
  merge-sym {xs = []} {[]} ()
  merge-sym {xs = []} {x ∷ ys} here = here
  merge-sym {xs = []} {x ∷ ys} (there p) = there p
  merge-sym {xs = x ∷ xs} {[]} here = here
  merge-sym {xs = x ∷ xs} {[]} (there p) = there p
  merge-sym {xs = x ∷ xs} {y ∷ ys} here = there here
  merge-sym {xs = x ∷ xs} {y ∷ ys} (there here) = here
  merge-sym {xs = x ∷ xs} {y ∷ ys} (there (there p)) =
    there (there (merge-sym {xs = xs} {ys = ys} p))

  merge-cong : ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x y : a}
               → y ∈ merge xs ys
               → y ∈ merge (x ∷ xs) ys
  merge-cong {a = a} {xs = xs} {ys = []} p =
    there (∈-rewr (merge-empty-sym {xs = xs}) p)
  merge-cong {ys = x ∷ ys} p = there (merge-sym {xs = x ∷ ys} p)

  merge-complete-left : ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
                        → x ∈ xs
                        → x ∈ merge xs ys
  merge-complete-left (here) = here
  merge-complete-left {xs = _ ∷ xs} (there p) =
    merge-cong {xs = xs} (merge-complete-left p)

  merge-complete-right : ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
                         → x ∈ ys
                         → x ∈ merge xs ys
  merge-complete-right {xs = xs} p
    = merge-sym {xs = xs} (merge-complete-left p)
  
  ∥-complete-left : ∀ {ℓ} {a : Set ℓ} {x : a} {f g : ω a} → f ↝ x → (f ∥ g) ↝ x
  ∥-complete-left (n , p) = n , merge-complete-left p

  ∥-complete-right : ∀ {ℓ} {a : Set ℓ} {x : a} {f g : ω a} → g ↝ x → (f ∥ g) ↝ x
  ∥-complete-right (n , p) = n , merge-complete-right p
