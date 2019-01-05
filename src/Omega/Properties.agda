open import src.Omega.Base
open import src.Data

open import Data.Product using (∃; ∃-syntax; _,_)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Category.Functor
open import Category.Applicative

module src.Omega.Properties where

  open RawApplicative ⦃...⦄

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

  ⊕-dimap : ∀ {ℓ} {a b c d : Set ℓ}
            → (a → c) → (b → d)
            → (a ⊕ b) → (c ⊕ d)
  ⊕-dimap f _ (inl x) = inl (f x)
  ⊕-dimap _ g (inr y) = inr (g y)

  merge-sound : ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
                → x ∈ merge xs ys
                → (x ∈ xs) ⊕ (x ∈ ys)
  merge-sound {xs = []} {ys} p = inr p
  merge-sound {xs = x ∷ xs} {[]} p = inl p
  merge-sound {xs = x ∷ xs} {y ∷ ys} here = inl here
  merge-sound {xs = x ∷ xs} {y ∷ ys} (there here) = inr here
  merge-sound {xs = x ∷ xs} {y ∷ ys} (there (there p)) =
    ⊕-dimap (λ x → there x) (λ y → there y) (merge-sound p)
  
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
  ∥-sound (n , prf) = ⊕-dimap (λ x → n , x) (λ y → n , y) (merge-sound prf)

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

  -- Obviously, we can't prove this for functions of type 'ℕ → List a'
  -- in general, so for the time being i'll postulate it.
  -- TODO: add depth monotonicity as an assumption to the completeness
  -- proof for the ap-combinator instead of assuming it. 
  postulate depth-monotone : ∀ {ℓ} {a : Set ℓ} {x : a} {f : ω a} {n m : ℕ}
                             → n ≤ m → x ∈ f n → x ∈ f m

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
