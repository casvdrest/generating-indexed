open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.List hiding (fromMaybe)
open import Data.Bool
open import Data.Maybe hiding (fromMaybe) 

open import src.Generic
open import src.Enumerable

module src.Isomorphism where

  data Iso (A : Set) (B : Set) : Set where
     MkIso : (f : A → B) → (g : B → A)
                      → (∀ {x : A} → (g ∘ f) x ≡ x)
                      → (∀ {y : B} → (f ∘ g) y ≡ y)
                      → Iso A B

  record _≅_ (a : Set) (b : Set) : Set where
    field iso : Iso a b

  open _≅_ ⦃...⦄ public

  from : ∀ {a b : Set} → Iso a b → (a → b)
  from (MkIso f _ _ _) = f

  fromℕ : ∀ {r : Set} → ℕ → ℕ'
  fromℕ zero = μ (inl U)
  fromℕ {r} (suc n) = μ (inr (I (fromℕ {r} n)))

  toℕ : ∀ {r : Set} → ℕ' → ℕ
  toℕ (μ (inl x)) = zero
  toℕ {r} (μ (inr (I x))) = suc (toℕ {r} x)

  isoℕ₁ : ∀ {r : Set} {n : ℕ} → toℕ {r} (fromℕ {r} n) ≡ n
  isoℕ₁ {n = zero} = refl
  isoℕ₁ {r} {n = suc n} = cong suc (isoℕ₁ {r})

  isoℕ₂ : ∀ {r : Set} {n' : ℕ'} → fromℕ {r} (toℕ {r} n') ≡ n'
  isoℕ₂ {n' = μ (inl U)} = refl
  isoℕ₂ {r} {n' = μ (inr (I x))} = cong ((μ ∘ inr) ∘ I) (isoℕ₂ {r})

  instance
    isoℕ : ∀ {r : Set} → Iso ℕ ℕ'
    isoℕ {r} = MkIso (fromℕ {r}) (toℕ {r}) (isoℕ₁ {r}) (isoℕ₂ {r})
  
   fromList : ∀ {r a : Set} → List a → List' a
  fromList [] = μ (inl U)
  fromList {r} (x ∷ xs) = μ (inr (K x , I (fromList {r} xs)))

  toList : ∀ {r a : Set} → List' a → List a
  toList (μ (inl x)) = []
  toList {r} (μ (inr (K x , I xs))) = x ∷ toList {r} xs

  isoList₁ : ∀ {r a : Set} {xs : List a} → toList {r} (fromList {r} xs) ≡ xs
  isoList₁ {r} {xs = []} = refl
  isoList₁ {r} {xs = x ∷ xs} = cong (λ ys → x ∷ ys) (isoList₁ {r})

  isoList₂ : ∀ {r a : Set} {xs : List' a} → fromList {r} (toList {r} xs) ≡ xs
  isoList₂ {r} {xs = μ (inl U)} = refl
  isoList₂ {r} {xs = μ (inr (K x , I xs))} = cong (λ r → μ (inr (K x , I r))) (isoList₂ {r})

  instance 
    isoList : ∀ {r a : Set} → Iso (List a) (List' a)
    isoList {r} = MkIso (fromList {r}) (toList {r}) (isoList₁ {r}) (isoList₂ {r})

  fromBool : Bool → Bool'
  fromBool false = μ (inl U)
  fromBool true = μ (inr U)

  toBool : Bool' → Bool
  toBool (μ (inl x)) = false
  toBool (μ (inr x)) = true

  isoBool₁ : ∀ {b : Bool} → toBool (fromBool b) ≡ b
  isoBool₁ {false} = refl
  isoBool₁ {true} = refl

  isoBool₂ : ∀ {b : Bool'} → fromBool (toBool b) ≡ b
  isoBool₂ {μ (inl U)} = refl
  isoBool₂ {μ (inr U)} = refl

  instance
    isoBool : Iso Bool Bool'
    isoBool = MkIso fromBool toBool isoBool₁ isoBool₂

  fromMaybe : ∀ {a : Set} → Maybe a → Maybe' a
  fromMaybe (just x) = μ (inl (K x))
  fromMaybe nothing = μ (inr U)

  toMaybe : ∀ {a : Set} → Maybe' a → Maybe a
  toMaybe (μ (inl (K x))) = just x
  toMaybe (μ (inr U)) = nothing

  isoMaybe₁ : ∀ {a : Set} {m : Maybe a} → toMaybe (fromMaybe m) ≡ m
  isoMaybe₁ {m = just x} = refl
  isoMaybe₁ {m = nothing} = refl

  isoMaybe₂ : ∀ {a : Set} {m : Maybe' a} → fromMaybe (toMaybe m) ≡ m
  isoMaybe₂ {m = μ (inl (K x))} = refl
  isoMaybe₂ {m = μ (inr U)} = refl

  instance
    isoMaybe : ∀ {a : Set} → Iso (Maybe a) (Maybe' a)
    isoMaybe {a} = MkIso fromMaybe toMaybe isoMaybe₁ isoMaybe₂

  fromEither : ∀ {a b : Set} → Either a b → Either' a b
  fromEither (Left x) = μ (inl (K x))
  fromEither (Right x) = μ (inr (K x))

  toEither : ∀ {a b : Set} → Either' a b → Either a b
  toEither (μ (inl (K x))) = Left x
  toEither (μ (inr (K x))) = Right x

  isoEither₁ : ∀ {a b : Set} {e : Either a b} → toEither (fromEither e) ≡ e
  isoEither₁ {e = Left x} = refl
  isoEither₁ {e = Right x} = refl

  isoEither₂ : ∀ {a b : Set} {e : Either' a b} → fromEither (toEither e) ≡ e
  isoEither₂ {e = μ (inl (K x))} = refl
  isoEither₂ {e = μ (inr (K x))} = refl

  instance
    isoEither : ∀ {a b : Set} → Iso (Either a b) (Either' a b)
    isoEither = MkIso fromEither toEither isoEither₁ isoEither₂

  fromPair : ∀ {a b : Set} → Pair a b → Pair' a b
  fromPair (MkPair x y) = μ (K x , K y)

  toPair : ∀ {a b : Set} → Pair' a b → Pair a b
  toPair (μ (K x , K y)) = MkPair x y

  isoPair₁ : ∀ {a b : Set} {p : Pair a b} → toPair (fromPair p) ≡ p
  isoPair₁ {p = MkPair x y} = refl

  isoPair₂ : ∀ {a b : Set} {p : Pair' a b} → fromPair (toPair p) ≡ p
  isoPair₂ {p = μ (K x , K y)} = refl

  instance
    isoPair : ∀ {a b : Set} → Iso (Pair a b) (Pair' a b)
    isoPair = MkIso fromPair toPair isoPair₁ isoPair₂

  -- a ≅ b ⇔ b ≅ a
  instance
    isoSym : ∀ {a b : Set} ⦃ _ : a ≅ b ⦄ → Iso b a
    isoSym {a} {b} with (iso {a} {b})
    ... | MkIso f g p₁ p₂ = MkIso g f p₂ p₁

  -- Enumerable a ∧ a ≅ b ⇒ Enumerable b
  instance
    enumIso : ∀ {a b : Set} ⦃ _ : Enumerable a ⦄ ⦃ _ : a ≅ b ⦄ → Colist b
    enumIso {a} = (from (iso {a})) <$> enumerate
