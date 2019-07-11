open import AgdaGen.Base
open import AgdaGen.Combinators
open import AgdaGen.Enumerate

open import AgdaGen.Generic.Isomorphism
open import AgdaGen.Properties.General
open import AgdaGen.Data
  using (_∈_; here; _⊕_; inl; inr; there; merge)

open import Data.Product
  using (Σ; Σ-syntax; ∃; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum hiding (map)
open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Empty

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Level renaming (suc to sucL ; zero to zeroL)

module AgdaGen.Properties.Monotonicity where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄

  ------ Monotonicity definition ------

  Depth-Monotoneᵢ :
    ∀ {ℓ k} {I : Set k} {a : Set ℓ} {t : I → Set ℓ} {i : I}
    → Gen a t i → ((i : I) → 𝔾 t i) → a → Set ℓ
  Depth-Monotoneᵢ {ℓ} {k} {i = i} g tg x = 
    ∀ {n m : ℕ}
    → n ≤ m → x ∈ enumerate tg i g n
    → x ∈ enumerate tg i g m

  ------ Combinator monotonicity ------

  pureᵢ-monotone :
    ∀ {ℓ} {k} {I : Set k} {a t : I → Set ℓ} {i : I}
      {x : a i} {tg : (i : I) → 𝔾 {ℓ} {k} a i}
    → Depth-Monotoneᵢ {a = a i} {i = i} (Pure x) tg x
  pureᵢ-monotone (s≤s p) elem = elem

  uninhabited-monotoneᵢ :
    ∀ {ℓ} {k} {I : Set k} {a t : I → Set ℓ} {i : I} {x : a i}
      {tg : (i : I) → 𝔾 {ℓ} {k} t i}
    → Depth-Monotoneᵢ {a = a i} {i = i} None tg x
  uninhabited-monotoneᵢ (s≤s p) ()

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
  
  $_ : ∀ {ℓ} {a b : Set ℓ} → (a → b) × a → b
  $ (f , x) = f x
  
  ap-right-[] :
    ∀ {ℓ} {a b : Set ℓ} {fs : List (a → b)}
    → list-ap fs [] ≡ []
  ap-right-[] {fs = []} = refl
  ap-right-[] {fs = f ∷ fs} =
    cong (λ x → map f [] ++ x) (ap-right-[] {fs = fs}) 

  ++-choose :
    ∀ {ℓ} {a : Set ℓ} {x : a} {xs xs' : List a}
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
    ∀ {ℓ} {a b : Set ℓ} {f : a → b} {fs : List (a → b)}
      {y : b} {xs : List a} → y ∈ (map f xs ++ list-ap fs xs)
    → (y ∈ map f xs) ⊎ (y ∈ list-ap fs xs)
  ap-tail-split elem = ++-choose elem

  ap-∈-split :
    ∀ {ℓ} {a b : Set ℓ} {x : b} {f : a → b}
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
    ∀ {ℓ} {a b : Set ℓ} {y : b} {xs : List a} {f : a → b}
    → y ∈ list-ap [ f ] xs → Σ[ x ∈ a ] ((x ∈ xs) × f x ≡ y)
  ap-singleton {xs = []} ()
  ap-singleton {xs = x ∷ xs} here =
    x , (here , refl)
  ap-singleton {xs = x ∷ xs} (there elem)
    with ap-singleton elem
  ap-singleton {y = _} {x ∷ xs} (there elem)
    | x' , loc , refl =
    x' , there loc , refl

  ∈-x : ∀ {ℓ} {a : Set ℓ} {x : a} {xs : List a} → x ∈ xs → a
  ∈-x {x = x} _ = x

  ∈-xs : ∀ {ℓ} {a : Set ℓ} {x : a} {xs : List a} → x ∈ xs → List a
  ∈-xs {xs = xs} _ = xs
  
  ap-inv :
    ∀ {ℓ} {a b : Set ℓ} {fs : List (a → b)} {xs : List a} {y : b}
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

  ∈x-rewr :
    ∀ {ℓ} {a : Set ℓ} {x y : a} {xs : List a}
    → x ∈ xs → x ≡ y → y ∈ xs
  ∈x-rewr elem refl = elem

  constr-monotoneᵢ :
    ∀ {ℓ} {k} {I : Set k} {a b t : I → Set ℓ} {i₁ i₂ : I} {x : a i₁} {g : Gen (a i₁) t i₁}
    → {C : a i₁ → b i₂} {tg : (i : I) → 𝔾 t i} → (∀ {x y : a i₁} → C x ≡ C y → x ≡ y)
    → Depth-Monotoneᵢ g tg x → Depth-Monotoneᵢ {ℓ} {k} {a = b i₂} {i = i₂} ⦇ C g ⦈ tg (C x)
  constr-monotoneᵢ {C = C} inv p (s≤s leq) elem with ap-singleton elem
  constr-monotoneᵢ {C = C} inv p (s≤s leq) elem | val , (loc , eq) =
    list-ap-complete {fs = [ C ]} here (p (s≤s leq) (∈x-rewr loc (inv eq)))

  
  ⊛-monotoneᵢ :
    ∀ {ℓ k} {I : Set k} {a b c t : I → Set ℓ} {i₁ i₂ i₃}
      {x : a i₁} {y : b i₂} {g₁ : Gen (a i₁) t i₁} {g₂ : Gen (b i₂) t i₂}
      {tg : (i : I) → 𝔾 t i} {C : a i₁ → b i₂ → c i₃}
    → (∀ {x₁ x₂ : a i₁} {y₁ y₂ : b i₂} → C x₁ y₁ ≡ C x₂ y₂ → x₁ ≡ x₂ × y₁ ≡ y₂)
    → Depth-Monotoneᵢ g₁ tg x → Depth-Monotoneᵢ g₂ tg y
    → Depth-Monotoneᵢ {a = c i₃} {i = i₃} ⦇ C g₁ g₂ ⦈ tg (C x y)
  ⊛-monotoneᵢ {i₁ = i₁} {i₂} {i₃} {g₁ = g₁} {g₂ = g₂} {tg} {C}
    inv p₁ p₂ (s≤s leq) elem with
    ap-inv {fs = list-ap [ C ] (enumerate tg i₁ g₁ (≤-left (s≤s leq)))} elem
  ... | (Cs , y) , loc₁ , eq with ap-singleton (proj₁ loc₁)
  ... | x , loc₂ , refl = list-ap-complete
    (list-ap-complete {fs = [ C ]} here
      (p₁ (s≤s leq) (∈x-rewr loc₂ (proj₁ (inv eq)))))
      (p₂ (s≤s leq) (∈x-rewr (proj₂ loc₁) (proj₂ (inv eq))))
  
  map-inv :
    ∀ {ℓ} {a b : Set ℓ} {y : b} {xs : List a} {f : a → b}
    → y ∈ map f xs → Σ[ x ∈ a ] f x ∈ map f xs × f x ≡ y
  map-inv {xs = []} ()
  map-inv {xs = x ∷ xs} here = x , (here , refl)
  map-inv {xs = x ∷ xs} (there elem) with map-inv elem
  map-inv {y = _} {x ∷ xs} (there elem) | x' , elem' , eq =
    x' , ((there elem') , eq)

  lemma : ∀ {ℓ} {a b : Set ℓ} {f : a → b} → map f [] ≡ []
  lemma = refl

  ∥-monotone-leftᵢ :
    ∀ {ℓ k} {I : Set k} {a t : I → Set ℓ} {i : I} {x : a i}
      {g₁ : Gen (a i) t i} {g₂ : Gen (a i) t i} {tg : (i : I) → 𝔾 t i}
    → Depth-Monotoneᵢ g₁ tg x
    → (∀ {n : ℕ} → x ∈ enumerate tg i g₂ n → ⊥)
    → Depth-Monotoneᵢ (g₁ ∥ g₂) tg x
  ∥-monotone-leftᵢ {g₁ = g₁} {tg = tg} mt₁ mt₂ (s≤s leq) elem with merge-sound' elem
  ... | inj₁ p = merge-complete-left (mt₁ (s≤s leq) p)
  ... | inj₂ p = ⊥-elim (mt₂ {n = ≤-left (s≤s leq)} p)

  ∥-monotone-rightᵢ :
    ∀ {ℓ k} {I : Set k} {a t : I → Set ℓ} {i : I} {x : a i}
      {g₁ : Gen (a i) t i} {g₂ : Gen (a i) t i} {tg : (i : I) → 𝔾 t i}
    → (∀ {n : ℕ} → x ∈ enumerate tg i g₁ n → ⊥)
    → Depth-Monotoneᵢ g₂ tg x
    → Depth-Monotoneᵢ (g₁ ∥ g₂) tg x
  ∥-monotone-rightᵢ {g₁ = g₁} {tg = tg} mt₁ mt₂ (s≤s leq) elem with merge-sound' elem
  ... | inj₂ p = merge-complete-right (mt₂ (s≤s leq) p)
  ... | inj₁ p = ⊥-elim (mt₁ {n = ≤-left (s≤s leq)} p)

  ∥-inj₁-monotone-leftᵢ :
    ∀ {ℓ k} {I : Set k} {a b t : I → Set ℓ} {i : I} {x : a i}
      {g₁ : Gen (a i) t i} {g₂ : Gen (b i) t i}
      {tg : (i : I) → 𝔾 t i}
    → Depth-Monotoneᵢ g₁ tg x
    → Depth-Monotoneᵢ {a = a i ⊎ b i} {i = i} (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) tg (inj₁ x)
  ∥-inj₁-monotone-leftᵢ {i = i} {g₁ = g₁} {g₂ = g₂} {tg} mt₁ (s≤s leq) elem with
    merge-sound' {ys = list-ap [ inj₂ ] (enumerate tg i g₂ (≤-left (s≤s leq)) )} elem
  ∥-inj₁-monotone-leftᵢ {g₁ = g₁} {g₂ = g₂} {tg} mt₁ (s≤s leq) elem | inj₁ x' with ap-singleton x'
  ∥-inj₁-monotone-leftᵢ {g₁ = g₁} {g₂ = g₂} {tg} mt₁ (s≤s leq) elem | inj₁ x' | _ , (loc , refl) =
    merge-complete-left (list-ap-complete {fs = [ inj₁ ]} here (mt₁ (s≤s leq) loc)) 
  ∥-inj₁-monotone-leftᵢ {g₁ = g₁} {g₂ = g₂} mt₁ leq elem | inj₂ y' with ap-singleton y'
  ∥-inj₁-monotone-leftᵢ {g₁ = g₁} {g₂} mt₁ leq elem | inj₂ y' | fst , fst₁ , () 

  ∥-inj₁-monotone-rightᵢ :
    ∀ {ℓ k} {I : Set k} {a b t : I → Set ℓ} {i : I} {y : b i}
      {g₁ : Gen (a i) t i} {g₂ : Gen (b i) t i}
      {tg : (i : I) → 𝔾 t i}
    → Depth-Monotoneᵢ g₂ tg y
    → Depth-Monotoneᵢ {a = a i ⊎ b i} {i = i} (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) tg (inj₂ y)
  ∥-inj₁-monotone-rightᵢ {i = i} {g₁ = g₁} {g₂ = g₂} {tg} mt₁ (s≤s leq) elem with
    merge-sound' {ys = list-ap [ inj₂ ] (enumerate tg i g₂ (≤-left (s≤s leq)) )} elem
  ∥-inj₁-monotone-rightᵢ {g₁ = g₁} {g₂ = g₂} {tg} mt₁ (s≤s leq) elem | inj₂ x' with ap-singleton x'
  ∥-inj₁-monotone-rightᵢ {g₁ = g₁} {g₂ = g₂} {tg} mt₁ (s≤s leq) elem | inj₂ x' | _ , (loc , refl) =
    merge-complete-right (list-ap-complete {fs = [ inj₂ ]} here (mt₁ (s≤s leq) loc)) 
  ∥-inj₁-monotone-rightᵢ {g₁ = g₁} {g₂ = g₂} mt₁ leq elem | inj₁ y' with ap-singleton y'
  ∥-inj₁-monotone-rightᵢ {g₁ = g₁} {g₂} mt₁ leq elem | inj₁ y' | fst , fst₁ , () 

  Callᵢ-monotone :
    ∀ {ℓ k} {I : Set k} {a t : I → Set ℓ} {i : I} {x : a i}
      {tg : (i : I) → 𝔾 t i} {g :(i : I) → 𝔾 a i}
    → Depth-Monotoneᵢ (g i) g x
    → Depth-Monotoneᵢ {i = i} (Call i g) tg x
  Callᵢ-monotone mt (s≤s leq) elem =
    mt (s≤s leq) elem

  μᵢ-monotone :
    ∀ {ℓ k} {I : Set k} {t : I → Set ℓ} {tg : (i : I) → 𝔾 t i}
      {i : I} {x : t i}
    → Depth-Monotoneᵢ (tg i) tg x
    → Depth-Monotoneᵢ (μ i) tg x
  μᵢ-monotone mt (s≤s leq) elem = mt leq elem

