import Level as L using (suc)

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; map; [_]; concatMap; []; _∷_; _++_; foldr)
open import Data.List.Categorical using (functor; applicative)
open import Data.Product using (∃; ∃-syntax; _,_)

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import src.Data

module src.Omega where

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
  maybes a = ⦇ nothing    ⦈
           ∥ ⦇ just (κ a) ⦈

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
  
  prop1 : (fix nats) 10 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  prop1 = refl

  prop2 : bools 10 ≡ true ∷ false ∷ []
  prop2 = refl

  prop3 : maybes (fix nats) 10 ≡ nothing ∷ just 0 ∷ just 1 ∷ just 2 ∷ just 3 ∷ just 4 ∷ just 5 ∷ just 6 ∷ just 7 ∷ just 8 ∷ []
  prop3 = refl

  prop4 : fix (lists (fix nats)) 4 ≡ [] ∷ (0 ∷ []) ∷ (0 ∷ 0 ∷ []) ∷ (1 ∷ []) ∷ (1 ∷ 0 ∷ []) ∷ []
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
  
  ∥-complete-left : ∀ {ℓ} {a : Set ℓ} {x : a} {f g : ω a}
                    → f ↝ x
                    ------------------------------------
                    → (f ∥ g) ↝ x
  ∥-complete-left (n , p) = n , merge-complete-left p

  ∥-complete-right : ∀ {ℓ} {a : Set ℓ} {x : a} {f g : ω a}
                     → g ↝ x
                     ------------------------------------
                     → (f ∥ g) ↝ x
  ∥-complete-right (n , p) = n , merge-complete-right p

  ∥-sound : ∀ {ℓ} {a : Set ℓ} {x : a} {f g : ω a}
            → (f ∥ g) ↝ x
            ------------------------------------
            → (f ↝ x) ⊕ (g ↝ x)
  

  ++-elem-left : ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a}
              → x ∈ xs → x ∈ (xs ++ ys)
  ++-elem-left here = here
  ++-elem-left (there p) = there (++-elem-left p)

  ++-elem-right : ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a}
                  → x ∈ ys → x ∈ (xs ++ ys)
  ++-elem-right {xs = []} p = p
  ++-elem-right {xs = x ∷ xs} p = there (++-elem-right p)

  ++-right-ident : ∀ {ℓ} {a : Set ℓ} {xs : List a}
                   → xs ++ [] ≡ xs
  ++-right-ident {xs = []} = refl
  ++-right-ident {xs = x ∷ xs} = cong (_∷_ x) (++-right-ident {xs = xs})

  map-preserves-elem : ∀ {ℓ} {a b : Set ℓ} {f : a → b}
                         {x : a} {xs : List a}
                       → x ∈ xs → f x ∈ map f xs
  map-preserves-elem here = here
  map-preserves-elem (there p) =
    there (map-preserves-elem p)

  list-ap-complete : ∀ {ℓ} {a b : Set ℓ} {f : a → b} {x : a}
                       {fs : List (a → b)} {xs : List a} 
                     → f ∈ fs → x ∈ xs
                     → f x ∈ list-ap fs xs
  list-ap-complete here p2 = ++-elem-left (map-preserves-elem p2)
  list-ap-complete (there p1) p2 = ++-elem-right (list-ap-complete p1 p2)

  postulate depth-monotone : ∀ {ℓ} {a : Set ℓ} {x : a} {f : ω a} {n m : ℕ}
                             → n ≤ m → x ∈ f n → x ∈ f m

  concatMap-singleton : ∀ {ℓ} {a b : Set ℓ} {x : a} {f : a → List b} → concatMap (λ y → f y) [ x ] ≡ f x

  ap-pure-is-map : ∀ {ℓ} {a b : Set ℓ} {xs : List a} {C : a → b}
                   → map C xs ≡ list-ap [ C ] xs
  ap-pure-is-map {xs = xs} {C = C} =
    begin
      map C xs
    ≡⟨ sym ++-right-ident ⟩
      map C xs ++ foldr _++_ (map C []) []
    ≡⟨⟩
      concatMap (λ f → map f xs) [ C ]
    ∎
    
  list-ap-constr : ∀ {ℓ} {a b c : Set ℓ} {x : a} {y : b}
                     {xs : List a} {ys : List b} {C : a → b → c}
                   → x ∈ xs → y ∈ ys
                   → C x y ∈ (list-ap (list-ap [ C ] xs) ys)
  list-ap-constr {x = x} {y = y} {xs = xs} {ys = ys} {C = C} p1 p2 =
    list-ap-complete {f = C x} {x = y} {fs = list-ap [ C ] xs} {xs = ys}
      (∈-rewr ap-pure-is-map (map-preserves-elem p1)) p2

  ≤-rewr : ∀ {n m k : ℕ} → m ≡ k → n ≤ m → n ≤ k
  ≤-rewr refl p = p

  ≤-cong : ∀ {n m : ℕ} → n ≤ m → n ≤ suc m
  ≤-cong z≤n = z≤n
  ≤-cong (s≤s p) = s≤s (≤-cong p)

  ≤-comm : ∀ {n m : ℕ} → n ≤ n + m → n ≤ m + n
  ≤-comm {n = n} {m = m} p = ≤-rewr (+-comm n m) p 

  ≤-sum : (n m : ℕ) → n ≤ (n + m)
  ≤-sum n zero = ≤-reflexive (+-comm 0 n)
  ≤-sum n (suc m) with ≤-sum n m
  ... | p = ≤-rewr (sym (+-suc n m)) (≤-cong p) 

  ⊛-complete : ∀ {ℓ} {a b c : Set ℓ} {x : a} {y : b}
                 {f : ω a} {g : ω b} {C : a → b → c}
               → f ↝ x → g ↝ y
               -------------------------------------
               → ⦇ C f g ⦈ ↝ C x y
  ⊛-complete {f = f} {g = g} (n , p1) (m , p2) =
    n + m , list-ap-constr
      {xs = f (n + m)} {ys = g (n + m)}
      (depth-monotone {f = f} (≤-sum n m) p1)
      (depth-monotone {f = g} (≤-comm (≤-sum m n)) p2)

  ⊛-sound-left : ∀ {ℓ} {a b c : Set ℓ} {x : a} {y : b}
                   {f : ω a} {g : ω b} {C : a → b → c}
                 → ⦇ C f g ⦈ ↝ C x y
                 -------------------------------------
                 → f ↝ x

  ⊛-sound-right  : ∀ {ℓ} {a b c : Set ℓ} {x : a} {y : b}
                     {f : ω a} {g : ω b} {C : a → b → c}
                   → ⦇ C f g ⦈ ↝ C x y
                   -------------------------------------
                   → g ↝ y
                 
