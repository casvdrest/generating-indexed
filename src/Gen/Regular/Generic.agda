
{-# OPTIONS --type-in-type #-}

open import src.Gen.Base

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.List

open import Category.Monad

open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Sum

open import Function

open import Codata.Thunk using (Thunk; force)
open import Size

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module src.Gen.Regular.Generic where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  data Reg : Set where
    U   : Reg
    _⊕_ : Reg → Reg → Reg
    _⊗_ : Reg → Reg → Reg
    I   : Reg

  ⟦_⟧ : Reg → Set → Set
  ⟦ U           ⟧ r = ⊤
  ⟦ reg₁ ⊕ reg₂ ⟧ r = ⟦ reg₁ ⟧ r ⊎ ⟦ reg₂ ⟧ r
  ⟦ reg₁ ⊗ reg₂ ⟧ r = ⟦ reg₁ ⟧ r × ⟦ reg₂ ⟧ r 
  ⟦ I           ⟧ r = r
  
  data μ (f : Reg) : Set where
    `μ : ⟦ f ⟧ (μ f) → μ f

  mapᵣ : ∀ {a b : Set} → (f : Reg) → (a → b) → ⟦ f ⟧ a → ⟦ f ⟧ b
  mapᵣ U f tt = tt
  mapᵣ (pf₁ ⊕ pf₂) f (inj₁ x) = inj₁ (mapᵣ pf₁ f x)
  mapᵣ (pf₁ ⊕ pf₂) f (inj₂ y) = inj₂ (mapᵣ pf₂ f y)
  mapᵣ (pf₁ ⊗ pf₂) f (fst , snd) = mapᵣ pf₁ f fst , mapᵣ pf₂ f snd
  mapᵣ I f i = f i

  BoolF : Set
  BoolF = μ (U ⊕ U)

  fromBool : Bool → BoolF
  fromBool false = `μ (inj₁ tt)
  fromBool true = `μ (inj₂ tt)

  toBool : BoolF → Bool
  toBool (`μ (inj₁ tt)) = false
  toBool (`μ (inj₂ tt)) = true

  isoBool₁ : ∀ {b : Bool} → toBool (fromBool b) ≡ b
  isoBool₁ {false} = refl
  isoBool₁ {true} = refl

  isoBool₂ : ∀ {bf : BoolF} → fromBool (toBool bf) ≡ bf
  isoBool₂ {`μ (inj₁ x)} = refl
  isoBool₂ {`μ (inj₂ y)} = refl

  ℕF : Set
  ℕF = μ (U ⊕ I)

  fromℕ : ℕ → ℕF
  fromℕ zero = `μ (inj₁ tt)
  fromℕ (suc n) = `μ (inj₂ (fromℕ n))

  toℕ : ℕF → ℕ
  toℕ (`μ (inj₁ tt)) = zero
  toℕ (`μ (inj₂ y)) = suc (toℕ y)

  isoℕ₁ : ∀ {n : ℕ} → toℕ (fromℕ n) ≡ n
  isoℕ₁ {zero} = refl
  isoℕ₁ {suc n} = cong suc isoℕ₁

  isoℕ₂ : ∀ {nf : ℕF} → fromℕ (toℕ nf) ≡ nf
  isoℕ₂ {`μ (inj₁ x)} = refl
  isoℕ₂ {`μ (inj₂ y)} = cong (`μ ∘ inj₂) isoℕ₂

  {-
  ListF : Set → Set
  ListF a = μ (U ⊕ (K a ⊗ I))

  fromList : ∀ {a : Set} → List a → ListF a
  fromList [] = `μ (inj₁ tt)
  fromList (x ∷ xs) = `μ (inj₂ (x , fromList xs))

  toList : ∀ {a : Set} → ListF a → List a
  toList (`μ (inj₁ tt)) = []
  toList (`μ (inj₂ (fst , snd))) = fst ∷ toList snd

  isoList₁ : ∀ {a : Set} {xs : List a} → toList (fromList xs) ≡ xs
  isoList₁ {xs = []} = refl
  isoList₁ {xs = x ∷ xs} = cong (_∷_ x) isoList₁

  isoList₂ : ∀ {a : Set} {xs : ListF a} → fromList (toList xs) ≡ xs
  isoList₂ {xs = `μ (inj₁ x)} = refl
  isoList₂ {xs = `μ (inj₂ (fst , snd))} = cong (`μ ∘ inj₂ ∘ _,_ fst) isoList₂
  -}

  ugen : ∀ {n : ℕ} {a : Set} → 𝔾 (⟦ U ⟧ a) n
  ugen = pure tt

  igen : ∀ {n : ℕ} {a : Set} {f : Reg} → 𝔾 (⟦ f ⟧ a) n →
         𝔾 (⟦ f ⟧ a) n
  igen μ = μ

  ⊕gen : ∀ {n : ℕ} {f g : Reg} {a : Set} →
         𝔾 (⟦ f ⟧ a) n → 𝔾 (⟦ g ⟧ a) n →
         𝔾 (⟦ f ⊕ g ⟧ a) n
  ⊕gen f g = ⦇ inj₁ f ⦈ ∥ ⦇ inj₂ g ⦈

  ⊗gen : ∀ {n : ℕ} {f g : Reg} {a : Set} →
         𝔾 (⟦ f ⟧ a) n → 𝔾 (⟦ g ⟧ a) n →
         𝔾 (⟦ f ⊗ g ⟧ a) n
  ⊗gen f g = ⦇ f , g ⦈

  deriveGen : ∀ {f g : Reg} {n : ℕ}
              → 𝔾 (⟦ g ⟧ (μ g)) n
              → 𝔾 (⟦ f ⟧ (μ g)) n
  deriveGen {U}      {g} rec = ugen {a = μ g}
  deriveGen {f ⊕ f₁} {g} rec = ⊕gen {f = f} (deriveGen rec) (deriveGen rec)
  deriveGen {f ⊗ f₁} {g} rec = ⊗gen {f = f} (deriveGen rec) (deriveGen rec)
  deriveGen {I}      {g} rec = ⦇ `μ (igen {f = g} rec) ⦈

  prop : Data.List.map (toBool ∘ `μ) (𝔾-run (deriveGen {f = U ⊕ U}) 5) ≡ false ∷ true ∷ []
  prop = refl

  
