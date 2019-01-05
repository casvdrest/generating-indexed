open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.List hiding (fromMaybe)
open import Data.Bool
open import Data.Maybe hiding (fromMaybe) 

open import src.Generic
open import src.Enumerable
open import src.Colist

module src.Isomorphism where

  record 𝓤 (a : Set) : Set₁ where
    field PF : Set → Set 

  instance
    PFList : (a : Set) → 𝓤 (List a)
    PFList a = record { PF = ListF a }

  instance
    PFℕ : 𝓤 ℕ
    PFℕ = record { PF = ℕF }

  ↰_ : ∀ {a : Set} → 𝓤 a → Set → Set
  (↰_) (record { PF = ty }) = ty

  data Reg (a : Set) ⦃ pf : 𝓤 a ⦄ : Set where
     MkIso : (f : a → (↰ pf) a) → (g : (↰ pf) a → a)
                      → (∀ {x : a} → (g ∘ f) x ≡ x)
                      → (∀ {y : (↰ pf) a} → (f ∘ g) y ≡ y)
                      → Reg a

  record _≅ (a : Set) ⦃ _ : 𝓤 a ⦄ : Set where
    field iso : Reg a
    
  open _≅ ⦃...⦄ public


  from : ∀ {a : Set} ⦃ pf : 𝓤 a ⦄ → Reg a → ((↰ pf) a → a)
  from (MkIso _ g _ _) = g

  to : ∀ {a : Set} ⦃ pf : 𝓤 a ⦄ → Reg a → (a → (↰ pf) a)
  to (MkIso f _ _ _) = f

  fromℕ : ℕ → ℕF ℕ
  fromℕ zero = inl U
  fromℕ (suc n) = inr (I n)

  toℕ : ℕF ℕ → ℕ
  toℕ (inl U) = zero
  toℕ (inr (I x)) = suc x

  isoℕ₁ : ∀ {n : ℕ} → toℕ (fromℕ n) ≡ n
  isoℕ₁ {zero} = refl
  isoℕ₁ {suc n} = refl

  isoℕ₂ : ∀ {n' : ℕF ℕ} → fromℕ (toℕ n') ≡ n'
  isoℕ₂ {inl U} = refl
  isoℕ₂ {inr (I x)} = refl

  instance
    isoℕ : ℕ ≅
    isoℕ = record { iso = MkIso fromℕ toℕ isoℕ₁ isoℕ₂ }

  extr : ∀ {a : Set} → ⦃ e : Enumerable a ⦄ → Colist a
  extr ⦃ e = record { enum = xs } ⦄ = xs

   -- Enumerable a ∧ a ≅ b ⇒ Enumerable 
  instance
    enumIso : ∀ {a : Set} ⦃ pf : 𝓤 a ⦄ ⦃ iso : a ≅ ⦄ ⦃ prf : GenericEnumerable (↰ pf) ⦄ → Enumerable a
    enumIso {a} ⦃ pf ⦄ ⦃ iso = record { iso = val } ⦄ ⦃ prf ⦄ = record { enum = from val <$> gInhabitants (↰ pf) ? }


  allℕ : Colist ℕ
  allℕ with enumIso ⦃ pf = PFℕ ⦄ ⦃ iso = isoℕ ⦄
  ... | record { enum = xs } = xs

  prop : take' 2 allℕ ≡ 0 ∷ 1 ∷ []
  prop = {!refl!}

{-
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
    isoBool : Bool ≅ Bool'
    isoBool = record { iso = MkIso fromBool toBool isoBool₁ isoBool₂ }

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
    isoSym : ∀ {a b : Set} ⦃ prf : a ≅ b ⦄ → b ≅ a
    isoSym ⦃ prf ⦄ with prf
    ... | record { iso = MkIso f g p₁ p₂ }  = record { iso = MkIso g f p₂ p₁ } 

  -- Enumerable a ∧ a ≅ b ⇒ Enumerable 
  instance
    {-# TERMINATING #-}
    enumIso : ∀ {a : Set} {f : Set → Set} ⦃ gprf : GenericEnumerable f ⦄ ⦃ prf : a ≅ (Fix f) ⦄ → Enumerable a
    enumIso ⦃ gprf = record { gEnum = ge } ⦄ ⦃ prf = prf ⦄ with prf
    ... | record { iso = MkIso f g _ _ } = record { enum = let r = gEnum in {!!} }

  allBool : ⦃ prf : GenericEnumerable BoolF ⦄ → Colist Bool
  allBool ⦃ prf ⦄ with enumIso ⦃ gprf = prf ⦄ ⦃ prf = isoBool ⦄
  ... | record { enum = xs } = xs

  allℕ : ∀ {r : Set} ⦃ prf : GenericEnumerable ℕF ⦄ → Colist ℕ
  allℕ {r} ⦃ prf ⦄ with enumIso ⦃ gprf = prf ⦄ ⦃ prf = isoℕ {r} ⦄
  ... | record { enum = xs } = xs

  prop1 : take' 2 allBool ≡ false ∷ true ∷ []
  prop1 = {!!}
-}
