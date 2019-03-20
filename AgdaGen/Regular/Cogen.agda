open import AgdaGen.Base
open import AgdaGen.Regular.Generic

open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Function

open import Category.Monad

module AgdaGen.Regular.Cogen where

  open RawMonad ⦃...⦄ using (_⊛_; pure; _>>=_; return)

  U-Cogen : ∀ {f : Reg} {a : Set} → Gen a a → 𝔾 (⟦ U ⟧ (Fix f) → a) 
  U-Cogen gen = ⦇ (λ x → λ { tt → x }) (` gen) ⦈

  ⊎lift : ∀ {a b c : Set} → (a → c) → (b → c) → a ⊎ b → c
  ⊎lift fx fy (inj₁ x) = fx x
  ⊎lift fx fy (inj₂ y) = fy y

  ⊕-Cogen :
    ∀ {f₁ f₂ g : Reg} {a : Set}
    → (𝔾 a → 𝔾 (⟦ f₁ ⟧ (Fix g) → a))
    → (𝔾 a → 𝔾 (⟦ f₂ ⟧ (Fix g) → a))
    → 𝔾 a → 𝔾 (⟦ f₁ ⊕ f₂ ⟧ (Fix g) → a )
  ⊕-Cogen cg₁ cg₂ gₐ =
    ⦇ ⊎lift (` (cg₁ gₐ)) (` cg₂ gₐ) ⦈

  ⊗-Cogen :
    ∀ {f₁ f₂ g : Reg} {a : Set}
    → (∀ {a : Set} → 𝔾 a → 𝔾 (⟦ f₁ ⟧ (Fix g) → a))
    → (∀ {a : Set} → 𝔾 a → 𝔾 (⟦ f₂ ⟧ (Fix g) → a))
    → 𝔾 a → 𝔾 (⟦ f₁ ⊗ f₂ ⟧ (Fix g) → a)
  ⊗-Cogen cg₁ cg₂ gₐ = ⦇ uncurry (` cg₁ (cg₂ gₐ)) ⦈ 
 
  deriveCogen :
    ∀ {f g : Reg} → RegInfo co𝔾 f → co𝔾 (⟦ f ⟧ (Fix g))
  deriveCogen {U} {g} info gₐ = U-Cogen {f = g} gₐ
  deriveCogen {f₁ ⊕ f₂} {g} (iₗ ⊕~ iᵣ) = 
    ⊕-Cogen {f₁} {f₂} (deriveCogen iₗ ) (deriveCogen iᵣ )
  deriveCogen {f₁ ⊗ f₂} {g} (iₗ ⊗~ iᵣ) =
    ⊗-Cogen {f₁} {f₂} {g} (deriveCogen iₗ) (deriveCogen iᵣ)
  deriveCogen {I} I~ _ = μ 
  deriveCogen {K x} {g} (K~ cg) = cg
  deriveCogen {Z} Z~ = λ _ → Pure λ()
  

