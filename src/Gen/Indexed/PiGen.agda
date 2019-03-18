{-# OPTIONS --type-in-type #-}

open import src.Gen.Base
open import src.Gen.Regular.Cogen
open import src.Gen.Regular.Generic

open import Data.Unit
open import Data.Sum
open import Data.Product

open import Category.Monad

open import Function

module src.Gen.Indexed.PiGen where

  open RawMonad ⦃...⦄ using (_⊛_; pure; _>>=_; return)

  Π𝔾 : Set → Set
  Π𝔾 a = ∀ {P : a → Set} → 𝔾ᵢ P → 𝔾 ((x : a) → P x)

  U-PiGen : ∀ {g : Reg} → Π𝔾 (⟦ U ⟧ ((Fix g)))
  U-PiGen gₐ = (` gₐ tt) >>= λ x → Pure λ { tt → x }

  ⊕sl : ∀ {a b : Set} {P : a ⊎ b → Set} → 𝔾ᵢ P → 𝔾ᵢ λ x → P (inj₁ x)
  ⊕sl g x = g (inj₁ x)

  ⊕sr : ∀ {a b : Set} {P : a ⊎ b → Set} → 𝔾ᵢ P → 𝔾ᵢ λ x → P (inj₂ x)
  ⊕sr g y = g (inj₂ y)

  ⊕-PiGen :
    ∀ {f₁ f₂ g : Reg} → Π𝔾 (⟦ f₁ ⟧ (Fix g)) → Π𝔾 (⟦ f₂ ⟧ (Fix g))
    → Π𝔾 (⟦ f₁ ⊕ f₂ ⟧ (Fix g))
  ⊕-PiGen cg₁ cg₂ gₐ =
    (` cg₁ (λ x → gₐ (inj₁ x))) >>= (λ f →
    (` cg₂ (λ y → gₐ (inj₂ y))) >>= (λ g →
    Pure λ { (inj₁ x) → f x ; (inj₂ y) → g y } ))

  ⊗-PiGen :
    ∀ {f₁ f₂ g : Reg} → Π𝔾 (⟦ f₁ ⟧ (Fix g)) → Π𝔾 (⟦ f₂ ⟧ (Fix g))
    → Π𝔾 (⟦ f₁ ⊗ f₂ ⟧ (Fix g))
  ⊗-PiGen cg₁ cg₂ gₐ = (` cg₁ λ x → cg₂ λ y → gₐ (x , y)) >>= Pure ∘ uncurry
  
  derivePiGen :
    ∀ {f g : Reg} → RegInfo Π𝔾 f → Π𝔾 (⟦ f ⟧ (Fix g))
  derivePiGen {U} {g} info = U-PiGen {g = g}
  derivePiGen {f₁ ⊕ f₂} {g} (iₗ ⊕~ iᵣ) =
    ⊕-PiGen {f₁ = f₁} {f₂ = f₂} (derivePiGen iₗ) (derivePiGen iᵣ)
  derivePiGen {f₁ ⊗ f₂} {g} (iₗ ⊗~ iᵣ) =
    ⊗-PiGen {f₁ = f₁} {f₂ = f₂} (derivePiGen iₗ) (derivePiGen iᵣ)
  derivePiGen {I} {g} info gₐ = μ
  derivePiGen {K x} {g} (K~ pg) gₐ = pg gₐ
  derivePiGen {Z} Z~ = λ _ → Pure (λ ())
