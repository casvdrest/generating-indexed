open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Data.Product using (Σ; _,_; Σ-syntax; _×_; proj₁; proj₂)
open import Data.Sum
open import Data.Nat hiding (_⊔_)
open import Data.Bool
open import Data.Unit
open import Data.List
open import Data.Maybe

open import Function
open import Level hiding (zero; suc)

open import Model.Base
open import Model.Combinators

module Model.Generic.Isomorphism where

  -- Captures an isomorphism/bijection between type a and b
  record _≃_ {ℓ ℓ'} (a : Set ℓ) (b : Set ℓ') : Set (ℓ ⊔ ℓ') where
    field
      from : a → b
      to   : b → a
      iso₁ : ∀ {x : a} → to (from x) ≡ x
      iso₂ : ∀ {y : b} → from (to y) ≡ y

  open _≃_ ⦃...⦄

  -- Isomorphisms are reflexive, e.g. ∀ a . a ≃ a
  ≃-reflexive : ∀ {a : Set} → a ≃ a
  ≃-reflexive =
    record { from = id
           ; to   = id
           ; iso₁ = refl
           ; iso₂ = refl
           }

  -- Isomorphisms are symmetric, e.g. ∀ a b . a ≃ b ⇒ b ≃ a 
  ≃-symmetric : ∀ {a b : Set} → a ≃ b → b ≃ a
  ≃-symmetric record { from = from ; to = to ; iso₁ = iso₁ ; iso₂ = iso₂ } =
    record { from = to
           ; to   = from
           ; iso₁ = iso₂
           ; iso₂ = iso₁
           }

  -- Traveling through an isomorphism and back results in the same value
  ≃-distributes-over-∘ :
    ∀ {a b c : Set} {g₁ : a → b}
      {f₁ : b → a} {g₂ : b → c} {f₂ : c → b}
    → (∀ {x : a} → f₁ (g₁ x) ≡ x)
    → (∀ {y : b} → f₂ (g₂ y) ≡ y)
    → (∀ {x : a} → (f₁ ∘ f₂) ((g₂ ∘ g₁) x) ≡ x)
  ≃-distributes-over-∘ {g₁ = g₁} p₁ p₂ {x} rewrite p₂ {g₁ x} | p₁ {x} = refl   

  -- Isomorphisms are transitive, e.g. ∀ a b c . a ≃ b ∧ b ≃ c ⇒ a ≃ c
  ≃-transitive : ∀ {a b c : Set} → a ≃ b → b ≃ c → a ≃ c
  ≃-transitive {a} {b} {c} i₁ i₂ =
    record { from = _≃_.from i₂ ∘ _≃_.from i₁
           ; to   = _≃_.to i₁ ∘ _≃_.to i₂
           ; iso₁ = ≃-distributes-over-∘ {f₁ = _≃_.to i₁} {f₂ = _≃_.to i₂}
                                         (_≃_.iso₁ i₁)    (_≃_.iso₁ i₂)
           ; iso₂ = ≃-distributes-over-∘ {a = c} {b = b} {c = a}
                                         {f₁ = _≃_.from i₂} {f₂ = _≃_.from i₁}
                                         (_≃_.iso₂ i₂) (_≃_.iso₂ i₁)}

  ≃lift : ∀ {ℓ ℓ'} {a : Set ℓ} → a ≃ Lift ℓ' a
  ≃lift = record { from = lift ; to = lower ; iso₁ = λ {x} → refl ; iso₂ = refl }
