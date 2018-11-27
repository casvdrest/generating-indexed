open import Agda.Builtin.Coinduction
open import Data.List hiding (_++_; zipWith)

open import Relation.Nullary.Decidable
open import Data.Nat
open import Data.Bool hiding (_≟_)

module src.Colist where

  data Coℕ : Set where
    CoZ : Coℕ
    CoS : ∞ Coℕ → Coℕ

  data Colist (A : Set) : Set where
    []   : Colist A 
    _∷_  : A → ∞ (Colist A) → Colist A

  data Stream (A : Set) : Set where
    Cons : A → ∞ (Stream A) → Stream A

  inf : Coℕ 
  inf = CoS (♯ inf) 

  comap : ∀ {A B : Set}  → (A → B) → Colist A → Colist B
  comap f [] = []
  comap f (x ∷ xs) = f x ∷ (♯ (comap f (♭ xs)))

  _⟨$⟩_ : ∀ {A B : Set} → (A → B) → Colist A → Colist B
  _⟨$⟩_ = comap 

  infixl 5 _⟨$⟩_

  fromList : ∀ {A : Set} → (xs : List A) → Colist A
  fromList [] = []
  fromList (x ∷ xs) = x ∷ ♯ fromList (xs)

  repeat : ∀ {A : Set} → A → Colist A
  repeat x = x ∷ ♯ repeat x

  iterate : ∀ {A : Set} → (A → A) → A → Colist A
  iterate f x = x ∷ ♯ iterate f (f x)

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

  zipWith : ∀ {A B C : Set} → (A → B → C) → Colist A → Colist B → Colist C
  zipWith f []       _        = []
  zipWith f _        []       = []
  zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ ♯ zipWith f (♭ xs) (♭ ys) 
  
  -- TODO: this does not include all possible combinations
  _×_ : ∀ {A B : Set} → Colist A → Colist B → Colist (A ⊗ B)
  (_×_) = zipWith (_,_)
 
  _⊎_ : ∀ {A B : Set} → Colist A → Colist B → Colist (A ⊕ B)
  xs ⊎ ys = interleave (Inl ⟨$⟩ xs) (Inr ⟨$⟩ ys)

  inhabitants : (A : Set) ⦃ _ : Enumerable A ⦄ → Colist A
  inhabitants _ = enumerate

  instance
    enumBool : Colist Bool
    enumBool = fromList (true ∷ (false ∷ []))

  instance
    enumℕ : Colist ℕ
    enumℕ = iterate suc zero

  instance
    enumList : ∀ {A : Set} ⦃ _ : Enumerable A ⦄ → Colist (List A)
    enumList = {!!}

  instance
    enum⊕ : {A : Set} ⦃ enumL : Enumerable A ⦄ →
            {B : Set} ⦃ enumR : Enumerable B ⦄ → Colist (A ⊕ B)
    enum⊕ {A} {B} = inhabitants A ⊎ inhabitants B
    
  instance
    enum⊗ : {A : Set} ⦃ enumF : Enumerable A ⦄ →
            {B : Set} ⦃ enumS : Enumerable B ⦄ → Colist (A ⊗ B)
    enum⊗ {A} {B} = (inhabitants A) × (inhabitants B)  

  
