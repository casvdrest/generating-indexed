open import AgdaGen.Base
open import AgdaGen.Combinators
open import AgdaGen.Generic.Regular.Universe

open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Function
open import Level

open import Category.Monad

module AgdaGen.Generic.Regular.Cogen where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄

  U-Cogen :
    ∀ {ℓ} {f : Reg {ℓ}} {a : Set ℓ}
    → Gen a a → 𝔾 (⟦_⟧ {ℓ} U (Fix f) → a) 
  U-Cogen gen = ⦇ (λ x → λ { tt → x }) (` gen) ⦈

  ⊎lift :
    ∀ {ℓ} {a b c : Set ℓ}
    → (a → c) → (b → c)
    → a ⊎ b → c
  ⊎lift fx fy (inj₁ x) = fx x
  ⊎lift fx fy (inj₂ y) = fy y

  ⊕-Cogen :
    ∀ {f₁ f₂ g : Reg {0ℓ}} {a : Set}
    → (𝔾 {0ℓ} {0ℓ} a → 𝔾 {0ℓ} (⟦ f₁ ⟧ (Fix g) → a))
    → (𝔾 {0ℓ} {0ℓ} a → 𝔾 {0ℓ} (⟦ f₂ ⟧ (Fix g) → a))
    → 𝔾 {0ℓ} {0ℓ} a → 𝔾 {0ℓ} (⟦ f₁ ⊕ f₂ ⟧ (Fix g) → a )
  ⊕-Cogen cg₁ cg₂ gₐ = ⦇ ⊎lift (` cg₁ gₐ) (` cg₂ gₐ) ⦈

  ⊗-Cogen :
    ∀ {ℓ} {f₁ f₂ g : Reg {ℓ}} {a : Set ℓ}
    → (∀ {a : Set ℓ} → 𝔾 {ℓ} {0ℓ} a → 𝔾 {ℓ} {0ℓ} (⟦ f₁ ⟧ (Fix g) → a))
    → (∀ {a : Set ℓ} → 𝔾 {ℓ} {0ℓ} a → 𝔾 {ℓ} {0ℓ} (⟦ f₂ ⟧ (Fix g) → a))
    → 𝔾 a → 𝔾 (⟦ f₁ ⊗ f₂ ⟧ (Fix g) → a)
  ⊗-Cogen cg₁ cg₂ gₐ = ⦇ uncurry (` cg₁ (cg₂ gₐ)) ⦈ 
  
  deriveCogen :
    ∀ {f g : Reg {0ℓ}}
    → RegInfo co𝔾 f → co𝔾 (⟦_⟧ {0ℓ} f (Fix g)) 
  deriveCogen {U} {g} info gₐ = U-Cogen {f = g} gₐ 
  deriveCogen {f₁ ⊕ f₂} {g} (iₗ ⊕~ iᵣ) = 
    ⊕-Cogen {f₁ = f₁} {f₂} (deriveCogen  iₗ ) (deriveCogen  iᵣ ) 
  deriveCogen {f₁ ⊗ f₂} {g} (iₗ ⊗~ iᵣ) =
    ⊗-Cogen {f₁ = f₁} {f₂} {g} (deriveCogen iₗ) (deriveCogen iᵣ) 
  deriveCogen {I} I~ _ = μ  
  deriveCogen {K x} {g} (K~ cg) = cg 
  deriveCogen {Z} Z~ = λ _ → Pure λ() 
  
