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

open import AgdaGen.Base
open import AgdaGen.Regular.Generic
open import AgdaGen.Regular.Cogen

module AgdaGen.Regular.Isomorphism where

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
      W : Σ[ f ∈ Reg ] (a ≅ Fix f)

  getPf : ∀ {a : Set} → Regular a → Reg
  getPf record { W = W } = proj₁ W

  open Regular ⦃...⦄

  isoGen : ∀ (a : Set) → ⦃ p : Regular a ⦄
           → RegInfo (𝔾) (getPf p) → 𝔾 a
  isoGen a ⦃ record { W = f , iso } ⦄ reginfo =
    ⦇ (_≅_.to iso ∘ In) (` deriveGen reginfo) ⦈

  isoCogen : ∀ (a : Set) → ⦃ p : Regular a ⦄
             → RegInfo co𝔾 (getPf p) → co𝔾 a
  isoCogen a ⦃ record { W = f , iso } ⦄ reginfo {b} gₐ =
    ⦇ (λ f → f ∘ (λ { (In x) → x }) ∘ _≅_.from iso)
      (` deriveCogen {g = f} reginfo gₐ) ⦈
  
  ℕF : Reg
  ℕF = U ⊕ I

  ℕ→ℕF : ℕ → Fix ℕF
  ℕ→ℕF zero = In (inj₁ tt)
  ℕ→ℕF (suc n) = In (inj₂ (ℕ→ℕF n))

  ℕF→ℕ : Fix ℕF → ℕ
  ℕF→ℕ (In (inj₁ x)) = zero
  ℕF→ℕ (In (inj₂ y)) = suc (ℕF→ℕ y)

  isoℕ : ∀ {n : ℕ} → ℕF→ℕ (ℕ→ℕF n) ≡ n
  isoℕ {zero} = refl
  isoℕ {suc n} = cong suc isoℕ

  isoℕF : ∀ {f : Fix ℕF} → ℕ→ℕF (ℕF→ℕ f) ≡ f
  isoℕF {In (inj₁ tt)} = refl
  isoℕF {In (inj₂ y)}  = cong (In ∘ inj₂) isoℕF
  
  ℕ≅ℕF : ℕ ≅ Fix ℕF
  ℕ≅ℕF = record { from = ℕ→ℕF
                ; to   = ℕF→ℕ
                ; iso₁ = isoℕ
                ; iso₂ = isoℕF
                }

  instance 
    ℕ-Regular : Regular ℕ
    ℕ-Regular = record { W = ℕF , ℕ≅ℕF }

  prop : ⟨ isoGen ℕ (U~ ⊕~ I~) ⟩ 10 ≡ zero ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ []
  prop = refl

  BoolF : Reg
  BoolF = U ⊕ U

  Bool→BoolF : Bool → Fix BoolF
  Bool→BoolF false = In (inj₁ tt)
  Bool→BoolF true = In (inj₂ tt)

  BoolF→Bool : Fix BoolF → Bool
  BoolF→Bool (In (inj₁ tt)) = false
  BoolF→Bool (In (inj₂ tt)) = true

  isoBool : ∀ {b : Bool} → BoolF→Bool (Bool→BoolF b) ≡ b
  isoBool {false} = refl
  isoBool {true} = refl

  isoBoolF : ∀ {f : Fix BoolF} → Bool→BoolF (BoolF→Bool f) ≡ f
  isoBoolF {In (inj₁ x)} = refl
  isoBoolF {In (inj₂ y)} = refl

  Bool≅BoolF : Bool ≅ Fix BoolF
  Bool≅BoolF = record { from = Bool→BoolF
                      ; to   = BoolF→Bool
                      ; iso₁ = isoBool
                      ; iso₂ = isoBoolF
                      }

  instance 
    Bool-Regular : Regular Bool
    Bool-Regular = record { W = BoolF , Bool≅BoolF }

  ListF : Set → Reg
  ListF a = U ⊕ (K a ⊗ I)

  List→ListF : ∀ {a : Set} → List a → Fix (ListF a)
  List→ListF [] = In (inj₁ tt)
  List→ListF (x ∷ xs) = In (inj₂ (x , List→ListF xs))

  ListF→List : ∀ {a : Set} → Fix (ListF a) → List a
  ListF→List (In (inj₁ tt)) = []
  ListF→List (In (inj₂ (fst , snd))) = fst ∷ ListF→List snd

  isoList : ∀ {a : Set} {xs : List a} → ListF→List (List→ListF xs) ≡ xs
  isoList {xs = []} = refl
  isoList {xs = x ∷ xs} = cong (_∷_ x) isoList

  isoListF : ∀ {a : Set} {xs : Fix (ListF a)} → List→ListF (ListF→List xs) ≡ xs
  isoListF {xs = In (inj₁ tt)} = refl
  isoListF {xs = In (inj₂ (fst , snd))} = cong (In ∘ inj₂ ∘ _,_ fst) isoListF

  List≅ListF : ∀ {a : Set} → List a ≅ Fix (ListF a)
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

  ⊎→⊎F : ∀ {a b} → a ⊎ b → Fix (a ⊎F b)
  ⊎→⊎F (inj₁ x) = In (inj₁ x)
  ⊎→⊎F (inj₂ y) = In (inj₂ y)

  ⊎F→⊎ : ∀ {a b} → Fix (a ⊎F b) → a ⊎ b
  ⊎F→⊎ (In (inj₁ x)) = inj₁ x
  ⊎F→⊎ (In (inj₂ y)) = inj₂ y

  iso⊎ : ∀ {a b : Set} → {x : a ⊎ b} → ⊎F→⊎ (⊎→⊎F x) ≡ x
  iso⊎ {x = inj₁ x} = refl
  iso⊎ {x = inj₂ y} = refl

  iso⊎F : ∀ {a b : Set} → {y : Fix (a ⊎F b)} → ⊎→⊎F (⊎F→⊎ y) ≡ y
  iso⊎F {y = In (inj₁ x)} = refl
  iso⊎F {y = In (inj₂ y)} = refl

  ⊎≅⊎F : ∀ {a b : Set} → (a ⊎ b) ≅ (Fix (a ⊎F b))
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

  ×→×F : ∀ {a b} → a × b → Fix (a ×F b)
  ×→×F (fst , snd) = In (fst , snd)
  
  ×F→× : ∀ {a b} → Fix (a ×F b) → a × b
  ×F→× (In (fst , snd)) = fst , snd

  iso× : ∀ {a b : Set} → {x : a × b} → ×F→× (×→×F x) ≡ x
  iso× {x = fst , snd} = refl

  iso×F : ∀ {a b : Set} → {y : Fix (a ×F b)} → ×→×F (×F→× y) ≡ y
  iso×F {y = In x} = refl

  ×≅×F : ∀ {a b : Set} → (a × b) ≅ (Fix (a ×F b))
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

  Maybe→MaybeF : ∀ {a : Set} → Maybe a → Fix (MaybeF a)
  Maybe→MaybeF (just x) = In (inj₁ x)
  Maybe→MaybeF nothing = In (inj₂ tt)

  MaybeF→Maybe : ∀ {a : Set} → Fix (MaybeF a) → Maybe a
  MaybeF→Maybe (In (inj₁ x)) = just x
  MaybeF→Maybe (In (inj₂ tt)) = nothing

  isoMaybe : ∀ {a : Set} {m : Maybe a} → MaybeF→Maybe (Maybe→MaybeF m) ≡ m
  isoMaybe {m = just x} = refl
  isoMaybe {m = nothing} = refl

  isoMaybeF : ∀ {a : Set} {m : Fix (MaybeF a)} → Maybe→MaybeF (MaybeF→Maybe m) ≡ m
  isoMaybeF {m = In (inj₁ x)} = refl
  isoMaybeF {m = In (inj₂ y)} = refl

  Maybe≅MaybeF : ∀ {a : Set} → Maybe a ≅ Fix (MaybeF a)
  Maybe≅MaybeF = record { from = Maybe→MaybeF
                        ; to   = MaybeF→Maybe 
                        ; iso₁ = isoMaybe
                        ; iso₂ = isoMaybeF
                        }

  instance
    Maybe-Regular : ∀ {a : Set} → Regular (Maybe a)
    Maybe-Regular {a} = record { W = MaybeF a , Maybe≅MaybeF }

