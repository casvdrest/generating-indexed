open import Data.List

open import Relation.Binary.PropositionalEquality hiding ([_])
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Model.Data hiding (_⊎_)
open import Model.Base

open import Data.Sum using (inj₁; inj₂; _⊎_)

module Model.Properties.General where 

  ------ List Merge ------

  list-ap :
    ∀ {ℓ} {a b : Set ℓ} → List (a → b) → List a → List b
  list-ap fs xs = concatMap (λ f → map f xs) fs

  -- If two lists are equal, we can rewrite elemental proofs about them
  ∈-rewr :
    ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a}
    → xs ≡ ys → x ∈ xs → x ∈ ys
  ∈-rewr refl x = x

  ∈-rewr' :
    ∀ {ℓ} {a : Set ℓ} {x y : a} {xs : List a}
    → x ≡ y → x ∈ xs → y ∈ xs
  ∈-rewr' refl p = p

  -- Left and right identity of 'merge'
  merge-empty-sym :
    ∀ {ℓ} {a : Set ℓ} {xs : List a}
    → merge xs [] ≡ merge [] xs
  merge-empty-sym {xs = []} = refl
  merge-empty-sym {xs = x ∷ xs} = refl

  -- Merge interpreted as a set is commutative. Notice the collection of
  -- elements in the merge remains the same, but the order changes
  merge-sym :
    ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a}
    → x ∈ merge ys xs → x ∈ merge xs ys
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
  merge-cong :
    ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x y : a}
    → y ∈ merge xs ys
    → y ∈ merge (x ∷ xs) ys
  merge-cong {a = a} {xs = xs} {ys = []} p =
    there (∈-rewr (merge-empty-sym {xs = xs}) p)
  merge-cong {ys = x ∷ ys} p = there (merge-sym {xs = x ∷ ys} p)

  -- Merging retains all elements from the left list
  merge-complete-left :
    ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
    → x ∈ xs
    → x ∈ merge xs ys
  merge-complete-left (here) = here
  merge-complete-left {xs = _ ∷ xs} (there p) =
    merge-cong {xs = xs} (merge-complete-left p)

  -- Merging retains all elements from the right list
  merge-complete-right :
    ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
    → x ∈ ys
    → x ∈ merge xs ys
  merge-complete-right {xs = xs} p
    = merge-sym {xs = xs} (merge-complete-left p)

  -- Bimap for coproducts
  ⊕-bimap :
    ∀ {ℓ} {a b c d : Set ℓ}
    → (a → c) → (b → d)
    → (a ⊎ b) → (c ⊎ d)
  ⊕-bimap f _ (inj₁ x) = inj₁ (f x)
  ⊕-bimap _ g (inj₂ y) = inj₂ (g y)

  -- If an element is in the merge of two lists, it had to come
  -- from one of the two sublists
  merge-sound :
    ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
    → x ∈ merge xs ys
    → (x ∈ xs) ⊎ (x ∈ ys)
  merge-sound {xs = []} {ys} p = inj₂ p
  merge-sound {xs = x ∷ xs} {[]} p = inj₁ p
  merge-sound {xs = x ∷ xs} {y ∷ ys} here = inj₁ here
  merge-sound {xs = x ∷ xs} {y ∷ ys} (there here) = inj₂ here
  merge-sound {xs = x ∷ xs} {y ∷ ys} (there (there p)) =
    ⊕-bimap there there (merge-sound p) 

  ------ List Concatenation ------

  -- A value is an element of the concatenation of two lists
  -- if it is an element of the left operand
  ++-elem-left :
    ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a}
    → x ∈ xs → x ∈ (xs ++ ys)
  ++-elem-left here = here
  ++-elem-left (there p) = there (++-elem-left p)

  -- A value is an element of the concatenation of two lists
  -- if it is an element of the right operand
  ++-elem-right :
    ∀ {ℓ} {a : Set ℓ} {x : a} {xs ys : List a}
    → x ∈ ys → x ∈ (xs ++ ys)
  ++-elem-right {xs = []} p = p
  ++-elem-right {xs = x ∷ xs} p =
    there (++-elem-right p)

  -- Right identity for concatenation
  ++-right-ident :
    ∀ {ℓ} {a : Set ℓ} {xs : List a}
    → xs ++ [] ≡ xs
  ++-right-ident {xs = []} = refl
  ++-right-ident {xs = x ∷ xs} =
    cong (_∷_ x) (++-right-ident {xs = xs})

  map-++-ident :
    ∀ {ℓ} {a b : Set ℓ} {f : a → b} {y : b} {xs : List a}
    → y ∈ ((map f (xs)) ++ []) → y ∈ map f xs
  map-++-ident {xs = []} ()
  map-++-ident {xs = x ∷ xs} here = here
  map-++-ident {xs = x ∷ xs} (there elem) =
    there (map-++-ident elem)

  -- If x ∈ xs, then f x ∈ map f xs
  map-preserves-elem :
    ∀ {ℓ} {a b : Set ℓ} {f : a → b} {x : a} {xs : List a}
    → x ∈ xs → f x ∈ map f xs
  map-preserves-elem here = here
  map-preserves-elem (there p) =
    there (map-preserves-elem p)

  -- The 'list-ap' function does indeed produce all combinations
  list-ap-complete :
    ∀ {ℓ} {a b : Set ℓ} {f : a → b} {x : a}
      {fs : List (a → b)} {xs : List a} 
    → f ∈ fs → x ∈ xs
    → f x ∈ list-ap fs xs
  list-ap-complete here p2 =
    ++-elem-left (map-preserves-elem p2)
  list-ap-complete (there p1) p2 =
    ++-elem-right (list-ap-complete p1 p2)

  -- pure f <*> xs ≡ map f xs
  ap-pure-is-map :
    ∀ {ℓ} {a b : Set ℓ} {xs : List a} {C : a → b}
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
  list-ap-constr :
    ∀ {ℓ} {a b c : Set ℓ} {x : a} {y : b}
      {xs : List a} {ys : List b} {C : a → b → c}
    → x ∈ xs → y ∈ ys
    → C x y ∈ (list-ap (list-ap [ C ] xs) ys)
  list-ap-constr {x = x} {y = y} {xs = xs} {ys = ys} {C = C} p1 p2 =
    list-ap-complete {f = C x} {x = y} {fs = list-ap [ C ] xs} {xs = ys}
      (∈-rewr ap-pure-is-map (map-preserves-elem p1)) p2

