open import src.Gen.Base
open import src.Gen.Regular.Isomorphism
open import src.Gen.ListProperties
open import src.Data using (_∈_; here; _⊕_; inl; inr; there; merge)

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

module src.Gen.Monotonicity where

  open RawApplicative ⦃...⦄

  ------ Monotonicity definition ------

  Depth-Monotone :
    ∀ {a : Set}
    → (∀ {n : ℕ} → 𝔾 a n) → a → Set
  Depth-Monotone {a} g x =
    ∀ {n m : ℕ} 
    → n ≤ m → x ∈ g (n , refl)
    → x ∈ g (m , refl)

  ------ Combinator monotonicity ------

  
  pure-monotone :
    ∀ {a : Set} {x : a}
    → Depth-Monotone (pure x) x
  pure-monotone prf elem = elem

  uninhabited-monotone :
    ∀ {a : Set} {x : a}
    → Depth-Monotone {a} uninhabited x
  uninhabited-monotone leq ()
  
  
  -- Bimap for coproducts
  ⊎-bimap : ∀ {ℓ} {a b c d : Set ℓ}
            → (a → c) → (b → d)
            → (a ⊎ b) → (c ⊎ d)
  ⊎-bimap f _ (inj₁ x) = inj₁(f x)
  ⊎-bimap _ g (inj₂ y) = inj₂ (g y)

  -- If an element is in the merge of two lists, it had to come
  -- from one of the two sublists
  merge-sound' :
    ∀ {ℓ} {a : Set ℓ} {xs ys : List a} {x : a}
    → x ∈ merge xs ys
    → (x ∈ xs) ⊎ (x ∈ ys)
  merge-sound' {xs = []} {ys} p =
    inj₂ p
  merge-sound' {xs = x ∷ xs} {[]} p =
    inj₁ p
  merge-sound' {xs = x ∷ xs} {y ∷ ys} here =
    inj₁ here
  merge-sound' {xs = x ∷ xs} {y ∷ ys} (there here) =
    inj₂ here
  merge-sound' {xs = x ∷ xs} {y ∷ ys} (there (there p)) =
    ⊎-bimap there there (merge-sound' p)

  ≤-left : ∀ {n m : ℕ} → n ≤ m → ℕ
  ≤-left {n} _ = n

  ≤-right : ∀ {m n : ℕ} → n ≤ m → ℕ
  ≤-right {m} _ = m
  
  $_ : ∀ {a b : Set} → (a → b) × a → b
  $ (f , x) = f x

  ap-right-[] :
    ∀ {a b : Set} {fs : List (a → b)}
    → list-ap fs [] ≡ []
  ap-right-[] {fs = []} = refl
  ap-right-[] {fs = f ∷ fs} =
    cong (λ x → map f [] ++ x) (ap-right-[] {fs = fs}) 

  ++-choose :
    ∀ {a : Set} {x : a} {xs xs' : List a}
    → x ∈ (xs ++ xs') → x ∈ xs ⊎ x ∈ xs'
  ++-choose {xs = []} elem = inj₂ elem
  ++-choose {xs = x ∷ xs} here = inj₁ here
  ++-choose {xs = x ∷ xs} (there elem) with
    ++-choose {xs = xs} elem
  ++-choose {x = _} {x ∷ xs} (there elem)
    | inj₁ x₁ = inj₁ (there x₁)
  ++-choose {x = _} {x ∷ xs} (there elem)
    | inj₂ y  = inj₂ y

  ap-tail-split :
    ∀ {a b : Set} {f : a → b} {fs : List (a → b)}
      {y : b} {xs : List a} → y ∈ (map f xs ++ list-ap fs xs)
    → (y ∈ map f xs) ⊎ (y ∈ list-ap fs xs)
  ap-tail-split elem = ++-choose elem

  ap-∈-split :
    ∀ {a b : Set} {x : b} {f : a → b}
      {fs : List (a → b)} {xs : List a}
    → x ∈ list-ap (f ∷ fs) xs
    → x ∈ list-ap [ f ] xs ⊎ x ∈ list-ap fs xs
  ap-∈-split {f = f} {fs = fs} {xs = []} rewrite
    ap-right-[] {fs = f ∷ fs} = λ()
  ap-∈-split {xs = x ∷ xs} here = inj₁ here
  ap-∈-split {x = x} {f} {[]} {x' ∷ xs} (there elem) =
    inj₁ (there elem)
  ap-∈-split {x = x} {f} {f' ∷ fs} {x' ∷ xs} (there elem) with
    ap-tail-split {f = f} {fs = f' ∷ fs} {y = x}
                  {xs = x' ∷ xs} (there elem)
  ap-∈-split {x = x} {f} {f' ∷ fs} {x' ∷ xs} (there elem) | inj₁ loc =
    inj₁ (++-elem-left loc)
  ap-∈-split {x = x} {f} {f' ∷ fs} {x' ∷ xs} (there elem) | inj₂ loc =
    inj₂ loc
  
  ap-singleton :
    ∀ {a b : Set} {y : b} {xs : List a} {f : a → b}
    → y ∈ list-ap [ f ] xs → Σ[ x ∈ a ] ((x ∈ xs) × f x ≡ y)
  ap-singleton {xs = []} ()
  ap-singleton {xs = x ∷ xs} here =
    x , (here , refl)
  ap-singleton {xs = x ∷ xs} (there elem)
    with ap-singleton elem
  ap-singleton {y = _} {x ∷ xs} (there elem)
    | x' , loc , refl =
    x' , there loc , refl

  ∈-x : ∀ {a : Set} {x : a} {xs : List a} → x ∈ xs → a
  ∈-x {x = x} _ = x

  ∈-xs : ∀ {a : Set} {x : a} {xs : List a} → x ∈ xs → List a
  ∈-xs {xs = xs} _ = xs
  
  ap-inv :
    ∀ {a b : Set} {fs : List (a → b)} {xs : List a} {y : b}
    → y ∈ list-ap fs xs
    → Σ[ t ∈ ((a → b) × a) ]
       (((proj₁ t ∈ fs) × (proj₂ t ∈ xs)) × (($ t) ≡ y))
  ap-inv {fs = fs} {[]} rewrite ap-right-[] {fs = fs} = λ()
  ap-inv {fs = []} {x ∷ xs} ()
  ap-inv {fs = f ∷ fs} {x ∷ xs} here =
    (f , x) , (here , here) , refl
  ap-inv {fs = f ∷ fs} {x ∷ xs} (there elem)
    with ap-∈-split {fs = fs} (there elem)
  ap-inv {b = _} {f ∷ fs} {x ∷ xs} (there elem)
    | inj₁ elem' with ap-singleton elem'
  ap-inv {b = _} {f ∷ fs} {x ∷ xs} (there elem)
    | inj₁ elem' | x' , loc , refl =
      (f , (∈-x loc)) , (here , loc) , refl
  ap-inv {b = _} {f ∷ fs} {x ∷ xs} (there elem)
    | inj₂ elem' with ap-inv {fs = fs} elem'
  ap-inv {b = _} {f ∷ fs} {x ∷ xs} (there elem)
    | inj₂ elem' | (f' , x') , (loc₁ , loc₂) , refl =
      (f' , x') , (there loc₁ , loc₂) , refl 

  ∈x-rewr : ∀ {a : Set} {x y : a} {xs : List a} → x ∈ xs → x ≡ y → y ∈ xs
  ∈x-rewr elem refl = elem

  constr-monotone : ∀ {a b : Set} {g : ∀ {n : ℕ} → 𝔾 a n} 
                      {C : a → b} {x : a}
                    → (∀ {x y : a} → C x ≡ C y → x ≡ y) 
                    → Depth-Monotone g x
                    → Depth-Monotone ⦇ C g ⦈ (C x)
  constr-monotone {g = g} {C} {x} inv p leq elem with ap-singleton elem
  constr-monotone {g = g} {C} {x} inv p leq elem | val , (loc , eq) =
    list-ap-complete {fs = [ C ]} here (p leq (∈x-rewr loc (inv eq)))

  ⊛-monotone : ∀ {a b c : Set} {x : a} {y : b} {g₁ : ∀ {n : ℕ} → 𝔾 a n}
                 {g₂ : ∀ {n : ℕ} → 𝔾 b n} {C : a → b → c}
               → (∀ {x₁ x₂ : a} {y₁ y₂ : b} → C x₁ y₁ ≡ C x₂ y₂ → x₁ ≡ x₂ × y₁ ≡ y₂)
               → Depth-Monotone g₁ x → Depth-Monotone g₂ y
               → Depth-Monotone ⦇ C g₁ g₂ ⦈ (C x y)
  ⊛-monotone {g₁ = g₁} {g₂ = g₂} {C} inv p₁ p₂ leq elem with
    ap-inv {fs = list-ap [ C ] (g₁ ((≤-left leq) , refl))}
           {xs = g₂ (≤-left leq , refl)} elem
  ... | (Cx , y) , loc₁ , eq with
    ap-singleton (proj₁ loc₁)
  ... | (x) , loc₂ , refl  = list-ap-complete
    (list-ap-complete {fs = [ C ]} here
      (p₁ leq (∈x-rewr loc₂ (proj₁ (inv eq))))) (p₂ leq (∈x-rewr (proj₂ loc₁) (proj₂ (inv eq))
    ))

  map-inv : ∀ {a b : Set} {y : b} {xs : List a} {f : a → b} → y ∈ map f xs → Σ[ x ∈ a ] f x ∈ map f xs × f x ≡ y
  map-inv {xs = []} ()
  map-inv {xs = x ∷ xs} here = x , (here , refl)
  map-inv {xs = x ∷ xs} (there elem) with map-inv elem
  map-inv {y = _} {x ∷ xs} (there elem) | x' , elem' , eq = x' , ((there elem') , eq)

  lemma : ∀ {a b : Set} {f : a → b} → map f [] ≡ []
  lemma = refl

  ∥-monotone-left : ∀ {a b : Set} {x : a} {g₁ : ∀ {n : ℕ} → 𝔾 a n} { g₂ : ∀ {n : ℕ} → 𝔾 b n}
                    → Depth-Monotone g₁ x
                    → Depth-Monotone (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) (inj₁ x)
  ∥-monotone-left {g₁ = g₁} {g₂ = g₂} mt₁ leq elem with merge-sound' {ys = list-ap [ inj₂ ] (g₂ (≤-left leq , refl))} elem
  ∥-monotone-left {g₁ = g₁} {g₂ = g₂} mt₁ leq elem | inj₁ x' with ap-singleton x'
  ∥-monotone-left {g₁ = g₁} {g₂ = g₂} mt₁ leq elem | inj₁ x' | _ , (loc , refl) =
    merge-complete-left (list-ap-complete {fs = [ inj₁ ]} here (mt₁ leq loc))
  ∥-monotone-left {g₁ = g₁} {g₂ = g₂} mt₁ leq elem | inj₂ y' with ap-singleton y'
  ∥-monotone-left {g₁ = g₁} {g₂} mt₁ leq elem | inj₂ y' | fst , fst₁ , ()
  
  ∥-monotone-right : ∀ {a b : Set} {y : b} {g₁ : ∀ {n : ℕ} → 𝔾 a n} { g₂ : ∀ {n : ℕ} → 𝔾 b n}
                     → Depth-Monotone g₂ y
                     → Depth-Monotone (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) (inj₂ y)
  ∥-monotone-right {g₁ = g₁} {g₂ = g₂} mt₁ leq elem with merge-sound' {xs = list-ap [ inj₁ ] (g₁ (≤-left leq , refl))} elem
  ∥-monotone-right {g₁ = g₁} {g₂ = g₂} mt₁ leq elem | inj₁ x' with ap-singleton x'
  ∥-monotone-right {g₁ = g₁} {g₂} mt₁ leq elem | inj₁ x' | _ , _ , ()
  ∥-monotone-right {g₁ = g₁} {g₂ = g₂} mt₁ leq elem | inj₂ y' with ap-singleton y'
  ∥-monotone-right {g₁ = g₁} {g₂} mt₁ leq elem | inj₂ y' | _ , (loc , refl) =
    merge-complete-right (list-ap-complete {fs = [ inj₂ ]} here (mt₁ leq loc))
