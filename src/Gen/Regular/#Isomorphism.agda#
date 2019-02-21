{-#  OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Data.Product using (Σ; _,_; Σ-syntax; _×_; proj₁; proj₂)
open import Data.Sum
open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.List
open import Data.Maybe

open import Category.Monad

open import Function

open import src.Gen.Base
open import src.Gen.Regular.Generic

module src.Gen.Regular.Isomorphism where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  record _≅_ (a b : Set) : Set where
    field
      from : a → b
      to   : b → a
      iso₁ : ∀ {x : a} → to (from x) ≡ x
      iso₂ : ∀ {y : b} → from (to y) ≡ y

  open _≅_ ⦃...⦄

  ≅-symmetric : ∀ {a b : Set} → a ≅ b → b ≅ a
  ≅-symmetric record { from = from ; to = to ; iso₁ = iso₁ ; iso₂ = iso₂ } =
    record { from = to
           ; to   = from
           ; iso₁ = iso₂
           ; iso₂ = iso₁
           }

  ≅-distributes-over-∘ : ∀ {a b c : Set} {g₁ : a → b}
                           {f₁ : b → a} {g₂ : b → c} {f₂ : c → b}
                         → (∀ {x : a} → f₁ (g₁ x) ≡ x)
                         → (∀ {y : b} → f₂ (g₂ y) ≡ y)
                         → (∀ {x : a} → (f₁ ∘ f₂) ((g₂ ∘ g₁) x) ≡ x)
  ≅-distributes-over-∘ {g₁ = g₁} p₁ p₂ {x} rewrite p₂ {g₁ x} | p₁ {x} = refl   

  ≅-transitive : ∀ {a b c : Set} → a ≅ b → b ≅ c → a ≅ c
  ≅-transitive {a} {b} {c} i₁ i₂ =
    record { from = _≅_.from i₂ ∘ _≅_.from i₁
           ; to   = _≅_.to i₁ ∘ _≅_.to i₂
           ; iso₁ = ≅-distributes-over-∘ {f₁ = _≅_.to i₁} {f₂ = _≅_.to i₂}
                                         (_≅_.iso₁ i₁)    (_≅_.iso₁ i₂)
           ; iso₂ = ≅-distributes-over-∘ {a = c} {b = b} {c = a}
                                         {f₁ = _≅_.from i₂} {f₂ = _≅_.from i₁}
                                         (_≅_.iso₂ i₂) (_≅_.iso₂ i₁)
           }

  
  record Regular (a : Set) : Set where
    field
      W : Σ[ f ∈ Reg ] (a ≅ μ f)

  getPf : ∀ {a : Set} → Regular a → Reg
  getPf record { W = W } = proj₁ W

  open Regular ⦃...⦄

  isoGen : ∀ {n : ℕ} → (a : Set) → ⦃ p : Regular a ⦄
           → RegInfo (λ a → ⟪ 𝔾 a ⟫) (getPf p) → 𝔾 a n
  isoGen a ⦃ record { W = f , iso } ⦄ reginfo =
    ⦇ (_≅_.to iso ∘ `μ) ⟨ deriveGen {f = f} {g = f} reginfo ⟩ ⦈
  
  ℕF : Reg
  ℕF = U ⊕ I

  ℕ→ℕF : ℕ → μ ℕF
  ℕ→ℕF zero = `μ (inj₁ tt)
  ℕ→ℕF (suc n) = `μ (inj₂ (ℕ→ℕF n))

  ℕF→ℕ : μ ℕF → ℕ
  ℕF→ℕ (`μ (inj₁ x)) = zero
  ℕF→ℕ (`μ (inj₂ y)) = suc (ℕF→ℕ y)

  isoℕ : ∀ {n : ℕ} → ℕF→ℕ (ℕ→ℕF n) ≡ n
  isoℕ {zero} = refl
  isoℕ {suc n} = cong suc isoℕ

  isoℕF : ∀ {f : μ ℕF} → ℕ→ℕF (ℕF→ℕ f) ≡ f
  isoℕF {`μ (inj₁ tt)} = refl
  isoℕF {`μ (inj₂ y)}  = cong (`μ ∘ inj₂) isoℕF

  
  ℕ≅ℕF : ℕ ≅ μ ℕF
  ℕ≅ℕF = record { from = ℕ→ℕF
                ; to   = ℕF→ℕ
                ; iso₁ = isoℕ
                ; iso₂ = isoℕF
                }

  instance 
    ℕ-Regular : Regular ℕ
    ℕ-Regular = record { W = ℕF , ℕ≅ℕF }

  BoolF : Reg
  BoolF = U ⊕ U

  Bool→BoolF : Bool → μ BoolF
  Bool→BoolF false = `μ (inj₁ tt)
  Bool→BoolF true = `μ (inj₂ tt)

  BoolF→Bool : μ BoolF → Bool
  BoolF→Bool (`μ (inj₁ tt)) = false
  BoolF→Bool (`μ (inj₂ tt)) = true

  isoBool : ∀ {b : Bool} → BoolF→Bool (Bool→BoolF b) ≡ b
  isoBool {false} = refl
  isoBool {true} = refl

  isoBoolF : ∀ {f : μ BoolF} → Bool→BoolF (BoolF→Bool f) ≡ f
  isoBoolF {`μ (inj₁ x)} = refl
  isoBoolF {`μ (inj₂ y)} = refl

  Bool≅BoolF : Bool ≅ μ BoolF
  Bool≅BoolF = record { from = Bool→BoolF
                      ; to   = BoolF→Bool
                      ; iso₁ = isoBool
                      ; iso₂ = isoBoolF
                      }

  instance 
    Bool-Regular : Regular Bool
    Bool-Regular = record { W = BoolF , Bool≅BoolF }

  prop : 𝔾-run (const (isoGen Bool (U~ ⊕~ U~))) 5 ≡ false ∷ true ∷ []
  prop = refl

  prop1 : 𝔾-run (const (isoGen ℕ (U~ ⊕~ I~))) 5 ≡ zero ∷ 1 ∷ 2 ∷ 3 ∷ []
  prop1 = refl

  ListF : Set → Reg
  ListF a = U ⊕ (K a ⊗ I)

  List→ListF : ∀ {a : Set} → List a → μ (ListF a)
  List→ListF [] = `μ (inj₁ tt)
  List→ListF (x ∷ xs) = `μ (inj₂ (x , List→ListF xs))

  ListF→List : ∀ {a : Set} → μ (ListF a) → List a
  ListF→List (`μ (inj₁ tt)) = []
  ListF→List (`μ (inj₂ (fst , snd))) = fst ∷ ListF→List snd

  isoList : ∀ {a : Set} {xs : List a} → ListF→List (List→ListF xs) ≡ xs
  isoList {xs = []} = refl
  isoList {xs = x ∷ xs} = cong (_∷_ x) isoList

  isoListF : ∀ {a : Set} {xs : μ (ListF a)} → List→ListF (ListF→List xs) ≡ xs
  isoListF {xs = `μ (inj₁ tt)} = refl
  isoListF {xs = `μ (inj₂ (fst , snd))} = cong (`μ ∘ inj₂ ∘ _,_ fst) isoListF

  List≅ListF : ∀ {a : Set} → List a ≅ μ (ListF a)
  List≅ListF = record { from = List→ListF
                      ; to = ListF→List
                      ; iso₁ = isoList
                      ; iso₂ = isoListF
                      }

  
  instance
    List-Regular : ∀ {a : Set} → Regular (List a)
    List-Regular {a} = record { W = ListF a , List≅ListF }
  
  _⊎F_ : Set → Set → Reg
  a ⊎F b = K a ⊕ K b

  ⊎→⊎F : ∀ {a b} → a ⊎ b → μ (a ⊎F b)
  ⊎→⊎F (inj₁ x) = `μ (inj₁ x)
  ⊎→⊎F (inj₂ y) = `μ (inj₂ y)

  ⊎F→⊎ : ∀ {a b} → μ (a ⊎F b) → a ⊎ b
  ⊎F→⊎ (`μ (inj₁ x)) = inj₁ x
  ⊎F→⊎ (`μ (inj₂ y)) = inj₂ y

  iso⊎ : ∀ {a b : Set} → {x : a ⊎ b} → ⊎F→⊎ (⊎→⊎F x) ≡ x
  iso⊎ {x = inj₁ x} = refl
  iso⊎ {x = inj₂ y} = refl

  iso⊎F : ∀ {a b : Set} → {y : μ (a ⊎F b)} → ⊎→⊎F (⊎F→⊎ y) ≡ y
  iso⊎F {y = `μ (inj₁ x)} = refl
  iso⊎F {y = `μ (inj₂ y)} = refl

  ⊎≅⊎F : ∀ {a b : Set} → (a ⊎ b) ≅ (μ (a ⊎F b))
  ⊎≅⊎F = record { from = ⊎→⊎F
                ; to   = ⊎F→⊎
                ; iso₁ = iso⊎
                ; iso₂ = iso⊎F
                }
  
  instance
    ⊎-Regular : ∀ {a b : Set} → Regular (a ⊎ b)
    ⊎-Regular {a} {b} = record { W = a ⊎F b , ⊎≅⊎F }

  
  _×F_ : Set → Set → Reg
  a ×F b = K a ⊗ K b

  ×→×F : ∀ {a b} → a × b → μ (a ×F b)
  ×→×F (fst , snd) = `μ (fst , snd)
  
  ×F→× : ∀ {a b} → μ (a ×F b) → a × b
  ×F→× (`μ (fst , snd)) = fst , snd

  iso× : ∀ {a b : Set} → {x : a × b} → ×F→× (×→×F x) ≡ x
  iso× {x = fst , snd} = refl

  iso×F : ∀ {a b : Set} → {y : μ (a ×F b)} → ×→×F (×F→× y) ≡ y
  iso×F {y = `μ x} = refl

  ×≅×F : ∀ {a b : Set} → (a × b) ≅ (μ (a ×F b))
  ×≅×F  = record { from = ×→×F
                                     ; to   = ×F→×
                                     ; iso₁ = iso× 
                                     ; iso₂ = iso×F
                                     }

  instance
    ×-Regular : ∀ {a b : Set} → Regular (a × b)
    ×-Regular {a} {b} = record { W = a ×F b , ×≅×F }

  
  MaybeF : Set → Reg
  MaybeF a = K a ⊕ U

  Maybe→MaybeF : ∀ {a : Set} → Maybe a → μ (MaybeF a)
  Maybe→MaybeF (just x) = `μ (inj₁ x)
  Maybe→MaybeF nothing = `μ (inj₂ tt)

  MaybeF→Maybe : ∀ {a : Set} → μ (MaybeF a) → Maybe a
  MaybeF→Maybe (`μ (inj₁ x)) = just x
  MaybeF→Maybe (`μ (inj₂ tt)) = nothing

  isoMaybe : ∀ {a : Set} {m : Maybe a} → MaybeF→Maybe (Maybe→MaybeF m) ≡ m
  isoMaybe {m = just x} = refl
  isoMaybe {m = nothing} = refl

  isoMaybeF : ∀ {a : Set} {m : μ (MaybeF a)} → Maybe→MaybeF (MaybeF→Maybe m) ≡ m
  isoMaybeF {m = `μ (inj₁ x)} = refl
  isoMaybeF {m = `μ (inj₂ y)} = refl

  Maybe≅MaybeF : ∀ {a : Set} → Maybe a ≅ μ (MaybeF a)
  Maybe≅MaybeF = record { from = Maybe→MaybeF
                        ; to   = MaybeF→Maybe 
                        ; iso₁ = isoMaybe
                        ; iso₂ = isoMaybeF
                        }

  instance
    Maybe-Regular : ∀ {a : Set} → Regular (Maybe a)
    Maybe-Regular {a} = record { W = MaybeF a , Maybe≅MaybeF }

