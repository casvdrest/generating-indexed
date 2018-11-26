open import Agda.Builtin.Coinduction
open import Data.List hiding (zipWith)

open import Relation.Nullary.Decidable
open import Data.Bool using (if_then_else_)
open import Data.Nat
open import Data.Bool hiding (_≟_)

module test.CoList where

  data Colist (A : Set) : Set where
    []   : Colist A
    _∷_  : A → ∞ (Colist A) → Colist A

  data Stream (A : Set) : Set where
    _∷ₛ_ : A → ∞ (Stream A) → Stream A

  data Coℕ : Set where
    CoZ : Coℕ
    CoS : ∞ Coℕ → Coℕ

  inf : Coℕ 
  inf = CoS (♯ inf) 

  comap : ∀ {A B : Set} → (A → B) → Colist A → Colist B
  comap f [] = []
  comap f (x ∷ xs) = f x ∷ (♯ (comap f (♭ xs)))

  _⟨$⟩_ : ∀ {A B : Set} → (A → B) → Colist A → Colist B
  _⟨$⟩_ = comap

  infixl 5 _⟨$⟩_

  fromList : ∀ {A : Set} → List A → Colist A 
  fromList [] = []
  fromList (x ∷ xs) = x ∷ ♯ fromList xs

  repeat : ∀ {A : Set} → A → Colist A
  repeat x = x ∷ ♯ repeat x

  iterate : ∀ {A : Set} → (A → A) → A → Colist A
  iterate f x = x ∷ ♯ iterate f (f x)

  iterateₛ : ∀ {A : Set} → (A → A) → A → Stream A
  iterateₛ f x = x ∷ₛ (♯ iterateₛ f (f x))

  mapₛ : ∀ {A B : Set} → (A → B) → Stream A → Stream B
  mapₛ f (x ∷ₛ xs) = f x ∷ₛ (♯ mapₛ f (♭ xs))

  interleave : ∀ {A : Set} → Colist A → Colist A → Colist A
  interleave [] _  = []
  interleave _  [] = []
  interleave (x ∷ xs) (y ∷ ys) = x ∷ ♯ (y ∷ ♯ interleave (♭ xs) (♭ ys))
  
  record Enumerable (A : Set) : Set where
    field enumerate : Colist A

  open Enumerable ⦃...⦄ public

  data _⊗_ (A : Set) (B : Set) : Set where
    _,_ : A → B → A ⊗ B

  fst : ∀ {A B : Set} → A ⊗ B → A
  fst (x , _) = x

  snd : ∀ {A B : Set} → A ⊗ B → B
  snd (_ , x) = x 

  data _⊕_ (A : Set) (B : Set) : Set where
    Inl : A → A ⊕ B
    Inr : B → A ⊕ B

  next : ℕ ⊗ ℕ -> ℕ ⊗ ℕ
  next (n , m) = if ⌊ n ≟ 1 ⌋ then ((m + 1) , 1) else pred n , suc m

  ℚ : Stream (ℕ ⊗ ℕ)
  ℚ = iterateₛ next (1 , 1)

  _⊛_ : ∀ {A B : Set} → Colist (A → B) → Colist A → Colist B
  [] ⊛ xs = []
  fs ⊛ [] = []
  (f ∷ fs) ⊛ (x ∷ xs) = f x ∷ ♯ (♭ fs ⊛ ♭ xs)

  _×_ : ∀ {A B : Set} → Colist A → Colist B → Colist (A ⊗ B)
  xs × ys = ((_,_) ⟨$⟩ xs) ⊛ ys 
 
  _⊎_ : ∀ {A B : Set} → Colist A → Colist B → Colist (A ⊕ B)
  xs ⊎ ys = interleave (Inl ⟨$⟩ xs) (Inr ⟨$⟩ ys)

  _‼_ : ∀ {A : Set} → Stream A → ℕ → A
  (x ∷ₛ  _) ‼ zero    = x
  (_ ∷ₛ xs) ‼ (suc n) = ♭ xs ‼ n 

  prod : ∀ {A B : Set} → Stream A → Stream B → Stream (A ⊗ B)
  prod xs ys = mapₛ (λ x → (xs ‼ fst x) , (ys ‼ snd x)) ℚ

  inhabitants : (A : Set) ⦃ _ : Enumerable A ⦄ → Colist A
  inhabitants _ = enumerate

  instance
    enumBool : Colist Bool
    enumBool = fromList (true ∷ (false ∷ []))

  instance
    enumℕ : Colist ℕ
    enumℕ = iterate suc zero

  instance
    enum⊕ : {A : Set} ⦃ enumL : Enumerable A ⦄ →
            {B : Set} ⦃ enumR : Enumerable B ⦄ → Colist (A ⊕ B)
    enum⊕ {A} {B} = inhabitants A ⊎ inhabitants B 

  -- Obviously this results in something that is incomplete 
  instance
    enum⊗ : {A : Set} ⦃ enumF : Enumerable A ⦄ →
            {B : Set} ⦃ enumS : Enumerable B ⦄ → Colist (A ⊗ B)
    enum⊗ {A} {B} = (inhabitants A) × (inhabitants B)  

    
