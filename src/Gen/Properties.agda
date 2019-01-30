open import src.Gen.Base
open import src.Data

open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum hiding (map)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Category.Functor
open import Category.Applicative
open import Category.Monad

module src.Gen.Properties where

  open RawApplicative ⦃...⦄

  ------ General Properties ------

  -- Generator productivity: we say that a generator produces
  -- Some value 'x' if there is some n ∈ ℕ such that 'x' is in
  -- the list we get by applying 'n' to the generator. 
  _↝_ : ∀ {a : Set} → (∀ {n : ℕ} → 𝔾 a n) → a → Set
  f ↝ x = ∃[ n ] (x ∈ f (n , refl))

  -- Completeness: A generator is complete if we can produce
  -- a productivity proof for all values of its type
  Complete : ∀ {a : Set} → (∀ {n : ℕ} → 𝔾 a n) → Set
  Complete {a} f = ∀ {x : a} → f ↝ x

  
  ------ List Merge ------

  -- If two lists are equal, we can rewrite elemental proofs about them
  ∈-rewr : ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a} → xs ≡ ys → x ∈ xs → x ∈ ys
  ∈-rewr refl x = x

  -- Left and right identity of 'merge'
  merge-empty-sym : ∀ {ℓ} {a : Set ℓ} {xs : List a} → merge xs [] ≡ merge [] xs
  merge-empty-sym {xs = []} = refl
  merge-empty-sym {xs = x ∷ xs} = refl

  -- Merge interpreted as a set is commutative. Notice the collection of
  -- elements in the merge remains the same, but the order changes
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

  -- Merging a cons constructor is the same as 'cons' with the
  -- result of the merge
  merge-cong : ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x y : a}
               → y ∈ merge xs ys
               → y ∈ merge (x ∷ xs) ys
  merge-cong {a = a} {xs = xs} {ys = []} p =
    there (∈-rewr (merge-empty-sym {xs = xs}) p)
  merge-cong {ys = x ∷ ys} p = there (merge-sym {xs = x ∷ ys} p)

  -- Merging retains all elements from the left list
  merge-complete-left : ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
                        → x ∈ xs
                        → x ∈ merge xs ys
  merge-complete-left (here) = here
  merge-complete-left {xs = _ ∷ xs} (there p) =
    merge-cong {xs = xs} (merge-complete-left p)

  -- Merging retains all elements from the right list
  merge-complete-right : ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
                         → x ∈ ys
                         → x ∈ merge xs ys
  merge-complete-right {xs = xs} p
    = merge-sym {xs = xs} (merge-complete-left p)

  -- Bimap for coproducts
  ⊕-bimap : ∀ {ℓ} {a b c d : Set ℓ}
            → (a → c) → (b → d)
            → (a ⊕ b) → (c ⊕ d)
  ⊕-bimap f _ (inl x) = inl (f x)
  ⊕-bimap _ g (inr y) = inr (g y)

  -- If an element is in the merge of two lists, it had to come
  -- from one of the two sublists
  merge-sound : ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
                → x ∈ merge xs ys
                ---------------------
                → (x ∈ xs) ⊕ (x ∈ ys)
  merge-sound {xs = []} {ys} p = inr p
  merge-sound {xs = x ∷ xs} {[]} p = inl p
  merge-sound {xs = x ∷ xs} {y ∷ ys} here = inl here
  merge-sound {xs = x ∷ xs} {y ∷ ys} (there here) = inr here
  merge-sound {xs = x ∷ xs} {y ∷ ys} (there (there p)) =
    ⊕-bimap (λ x → there x) (λ y → there y) (merge-sound p)


  ------ Generator Choice ------
  
  -- Choice between two generators produces an element, given that it is
  -- produced by its left option
  ∥-complete-left : ∀ {a : Set} {x : a} {f g : ∀ {n : ℕ} → 𝔾 a n}
                    → f ↝ x
                    ------------------------------------
                    → (f ∥ g) ↝ x
  ∥-complete-left (n , p) = n , merge-complete-left p

  -- Choice between two generators produces an element, given that it is produced
  -- by its right option
  ∥-complete-right : ∀ {a : Set} {x : a} {f g : ∀ {n : ℕ} → 𝔾 a n}
                     → g ↝ x
                     ------------------------------------
                     → (f ∥ g) ↝ x
  ∥-complete-right (n , p) = n , merge-complete-right p

  -- If an element is produced by choice between two generators, it is either
  -- produced by the left option or by the right option
  ∥-sound : ∀ {a : Set} {x : a} {n : ℕ} → {f g : ∀ {n : ℕ} → 𝔾 a n}
            → (f ∥ g) ↝ x
            ------------------------------------
            → (f ↝ x) ⊕ (g ↝ x)
  ∥-sound (n , prf) = ⊕-bimap (λ x → n , x) (λ y → n , y) (merge-sound prf)


  ------ List Concatenation ------

  -- A value is an element of the concatenation of two lists
  -- if it is an element of the left operand
  ++-elem-left : ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a}
              → x ∈ xs → x ∈ (xs ++ ys)
  ++-elem-left here = here
  ++-elem-left (there p) = there (++-elem-left p)

  -- A value is an element of the concatenation of two lists
  -- if it is an element of the right operand
  ++-elem-right : ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a}
                  → x ∈ ys → x ∈ (xs ++ ys)
  ++-elem-right {xs = []} p = p
  ++-elem-right {xs = x ∷ xs} p = there (++-elem-right p)

  -- Right identity for concatenation
  ++-right-ident : ∀ {ℓ} {a : Set ℓ} {xs : List a}
                   → xs ++ [] ≡ xs
  ++-right-ident {xs = []} = refl
  ++-right-ident {xs = x ∷ xs} = cong (_∷_ x) (++-right-ident {xs = xs})

  -- If f ∈ xs, then f x ∈ map f xs
  map-preserves-elem : ∀ {ℓ} {a b : Set ℓ} {f : a → b}
                         {x : a} {xs : List a}
                       → x ∈ xs → f x ∈ map f xs
  map-preserves-elem here = here
  map-preserves-elem (there p) =
    there (map-preserves-elem p)

  -- The 'list-ap' function does indeed produce all combinations
  list-ap-complete : ∀ {ℓ} {a b : Set ℓ} {f : a → b} {x : a}
                       {fs : List (a → b)} {xs : List a} 
                     → f ∈ fs → x ∈ xs
                     → f x ∈ list-ap fs xs
  list-ap-complete here p2 = ++-elem-left (map-preserves-elem p2)
  list-ap-complete (there p1) p2 = ++-elem-right (list-ap-complete p1 p2)

  -- pure f <*> xs ≡ map f xs
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

  -- Applying a constructor of arity 2 over two lists yields all
  -- possible combination of elements applied to that constructor
  list-ap-constr : ∀ {ℓ} {a b c : Set ℓ} {x : a} {y : b}
                     {xs : List a} {ys : List b} {C : a → b → c}
                   → x ∈ xs → y ∈ ys
                   -----------------------------------------
                   → C x y ∈ (list-ap (list-ap [ C ] xs) ys)
  list-ap-constr {x = x} {y = y} {xs = xs} {ys = ys} {C = C} p1 p2 =
    list-ap-complete {f = C x} {x = y} {fs = list-ap [ C ] xs} {xs = ys}
      (∈-rewr ap-pure-is-map (map-preserves-elem p1)) p2


  ------ Generator Product ------

  -- Gets a genrator's depth
  depth : ∀ {a : Set} {f : ∀ {n : ℕ} → 𝔾 a n} {x : a} → f ↝ x → ℕ
  depth (fst₁ , snd₁) = fst₁

  -- Applying a constructor to a generator does not affect
  -- its production
  constr-preserves-elem : ∀ {a b : Set} {f : a → b}
                            {g : ∀ {n : ℕ} → 𝔾 a n} {x : a}
                          → g ↝ x
                          ---------------------------
                          → ⦇ f g ⦈ ↝ f x
  constr-preserves-elem {f = f} (p , elem) =
    p , list-ap-complete {fs = f ∷ []} here elem

  -- If f produces x and g produces y, then ⦇ C f g ⦈, where C is any
  -- 2-arity constructor, produces C x y
  ⊛-complete : ∀ {a b c : Set} {x : a} {y : b}
                 {f : ∀ {n : ℕ} → 𝔾 a n} {g : ∀ {n : ℕ} → 𝔾 b n} {C : a → b → c}
               → (p₁ : f ↝ x) → (p₂ : g ↝ y)
               → depth {f = f} p₁ ≡ depth {f = g} p₂ -- TODO: use depth monotonicity and maximum of the operand depths
               -------------------------------------
               → ⦇ C f g ⦈ ↝ C x y
  ⊛-complete (n , snd₁) (n , snd₂) refl  = n , list-ap-constr snd₁ snd₂

  ------ Combinator Completeness ------

  -- Completeness of the ∥ combinator, using coproducts to unify
  -- option types
  ∥-Complete : ∀ {a b : Set} 
                 {f : ∀ {n : ℕ} → 𝔾 a n}
                 {g : ∀ {n : ℕ} → 𝔾 b n}
               → Complete f → Complete g
               ------------------------------------
               → Complete (⦇ inj₁ f ⦈ ∥ ⦇ inj₂ g ⦈)
  ∥-Complete {f = f} {g = g} p₁ p₂ {inj₁ x} =
    ∥-complete-left {f = ⦇ inj₁ f ⦈} {g = ⦇ inj₂ g ⦈} (constr-preserves-elem {g = f} p₁)
  ∥-Complete {f = f} {g = g} p₁ p₂ {inj₂ y} =
    ∥-complete-right {f = ⦇ inj₁ f ⦈} {g = ⦇ inj₂ g ⦈} (constr-preserves-elem {g = g} p₂)
  
  -- Completeness of the ⊗ combinator, using products to unify
  -- the operands into a single type
  ⊗-Complete : ∀ {a b : Set} {x : a} {y : b}
                 {f : ∀ {n : ℕ} → 𝔾 a n} {g : ∀ {n : ℕ} → 𝔾 b n} 
               → (p₁ : f ↝ x) → (p₂ : g ↝ y)
               → depth {f = f} p₁ ≡ depth {f = g} p₂ -- TODO: use depth monotonicity and maximum of the operand depths
               -------------------------------------
               → ⦇ f , g ⦈ ↝ (x , y)
  ⊗-Complete {a} {b} {f = f} {g = g} (n , snd₁) (n , snd₂) refl =
    ⊛-complete {c = a × b} {f = f} {g = g} (n , snd₁) (n , snd₂) refl
