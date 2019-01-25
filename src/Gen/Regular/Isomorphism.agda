{-#  OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.Product using (Σ; _,_; Σ-syntax)
open import Data.Sum
open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Data.List

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

  record Regular (a : Set) : Set where
    field
      W : Σ[ f ∈ Reg ] (a ≅ μ f)

  open Regular ⦃...⦄

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

  isoGen : ∀ {n : ℕ} → (a : Set) → ⦃ p : Regular a ⦄ → 𝔾 a n
  isoGen a ⦃ record { W = f , iso } ⦄ = ⦇ (_≅_.to iso ∘ `μ) ⟨ deriveGen {f = f} {g = f} ⟩ ⦈

  prop : 𝔾-run (const (isoGen Bool)) 5 ≡ false ∷ true ∷ []
  prop = refl

  prop1 : 𝔾-run (const (isoGen ℕ)) 5 ≡ zero ∷ 1 ∷ 2 ∷ 3 ∷ []
  prop1 = refl

  ListF : ∀ {a : Set} → ⟪ 𝔾 a ⟫ → Reg
  ListF {a} gen = U ⊕ (K (a , gen) ⊗ I)

  List→ListF : ∀ {a : Set} {g : ⟪ 𝔾 a ⟫} → List a → μ (ListF g)
  List→ListF [] = `μ (inj₁ tt)
  List→ListF (x ∷ xs) = `μ (inj₂ (x , List→ListF xs))

  ListF→List : ∀ {a : Set} {g : ⟪ 𝔾 a ⟫} → μ (ListF g) → List a
  ListF→List (`μ (inj₁ tt)) = []
  ListF→List (`μ (inj₂ (fst , snd))) = fst ∷ ListF→List snd

  isoList : ∀ {a : Set} {g : ⟪ 𝔾 a ⟫} {xs : List a} → ListF→List {g = g} (List→ListF xs) ≡ xs
  isoList {xs = []} = refl
  isoList {xs = x ∷ xs} = cong (_∷_ x) isoList

  isoListF : ∀ {a : Set} {g : ⟪ 𝔾 a ⟫} {xs : μ (ListF g)} → List→ListF (ListF→List xs) ≡ xs
  isoListF {xs = `μ (inj₁ tt)} = refl
  isoListF {xs = `μ (inj₂ (fst , snd))} = cong (`μ ∘ inj₂ ∘ _,_ fst) isoListF

  List≅ListF : ∀ {a : Set} {g : ⟪ 𝔾 a ⟫} → List a ≅ μ (ListF g)
  List≅ListF = record { from = List→ListF
                      ; to = ListF→List
                      ; iso₁ = isoList
                      ; iso₂ = isoListF
                      }

  instance
    List-Regular : ∀ {a : Set} ⦃ _ : Regular a ⦄ → Regular (List a)
    List-Regular {a} = record { W = ListF (const (isoGen a)) , List≅ListF }

  prop2 : isoGen (List Bool) (5 , refl)
    ≡ [] ∷ (false ∷ []) ∷ (false ∷ false ∷ []) ∷ (false ∷ false ∷ false ∷ []) ∷
      (false ∷ false ∷ true ∷ []) ∷ (false ∷ true ∷ []) ∷ (false ∷ true ∷ false ∷ []) ∷
      (false ∷ true ∷ true ∷ []) ∷ (true ∷ []) ∷ (true ∷ false ∷ []) ∷
      (true ∷ false ∷ false ∷ []) ∷ (true ∷ false ∷ true ∷ []) ∷ (true ∷ true ∷ []) ∷
      (true ∷ true ∷ false ∷ []) ∷ (true ∷ true ∷ true ∷ []) ∷ []
  prop2 = refl
