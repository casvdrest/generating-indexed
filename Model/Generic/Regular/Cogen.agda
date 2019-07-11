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
    ∀ {ℓ k} {f : Reg {ℓ}} {a : Lift k ⊤ → Set ℓ}
    → Gen (a (lift tt)) a (lift tt) → 𝔾 (λ { _ → ⟦_⟧ {ℓ} U (Fix f) → a (lift tt)}) (lift tt)
  U-Cogen gen = ⦇ (λ x → λ { tt → x }) (Call' λ { _ → gen }) ⦈

  ⊎lift :
    ∀ {ℓ} {a b c : Set ℓ}
    → (a → c) → (b → c)
    → a ⊎ b → c
  ⊎lift fx fy (inj₁ x) = fx x
  ⊎lift fx fy (inj₂ y) = fy y

  ⊕-Cogen :
    ∀ {ℓ} {f₁ f₂ g : Reg {ℓ}} {a : ⊤ → Set}
    → (𝔾 a (tt) → 𝔾 {0ℓ} {0ℓ} (λ _ → ⟦ f₁ ⟧ (Fix g) → a (tt)) (lift tt) )
    → (𝔾 a (tt) → 𝔾 (λ _ → ⟦ f₂ ⟧ (Fix g) → a (tt)) (lift tt))
    → 𝔾 a ( tt) → 𝔾 (λ _ → ⟦ f₁ ⊕ f₂ ⟧ (Fix g) → a (tt)) (lift tt)
  ⊕-Cogen cg₁ cg₂ gₐ = ⦇ (λ { fx fy (inj₁ x) → fx x ; fx fy (inj₂ y) → fy y }) (Call (lift tt) λ _ → cg₁ gₐ) (Call (lift tt) λ _ → cg₂ gₐ) ⦈

  ⊗-Cogen :
    ∀ {ℓ} {f₁ f₂ g : Reg {ℓ}} {a : ⊤ → Set ℓ}
    → (∀ {a : ⊤ → Set ℓ} → 𝔾 {ℓ} {0ℓ} a tt → 𝔾 {ℓ} {0ℓ} (λ _ → ⟦ f₁ ⟧ (Fix g) → a tt) tt)
    → (∀ {a : ⊤ → Set ℓ} → 𝔾 {ℓ} {0ℓ} a tt → 𝔾 {ℓ} {0ℓ} (λ _ → ⟦ f₂ ⟧ (Fix g) → a tt) tt)
    → 𝔾 a tt → 𝔾 (λ _ → ⟦ f₁ ⊗ f₂ ⟧ (Fix g) → a tt) tt
  ⊗-Cogen cg₁ cg₂ gₐ = ⦇ uncurry (Call tt λ _ → cg₁ (cg₂ gₐ)) ⦈ 

  deriveCogen :
    ∀ {f g : Reg}
    → RegInfo (λ s → co𝔾 (λ _ → s) tt) f → co𝔾 (λ _ → ⟦_⟧ f (Fix g)) (lift tt) 
  deriveCogen {U} {g} info gₐ = U-Cogen {f = g} (μ (lift tt)) 
  deriveCogen {f₁ ⊕ f₂} {g} (iₗ ⊕~ iᵣ) = 
    ⊕-Cogen {f₁ = f₁} {f₂} (deriveCogen  iₗ ) (deriveCogen  iᵣ ) 
  deriveCogen {f₁ ⊗ f₂} {g} (iₗ ⊗~ iᵣ) gₐ = empty --⦇ {!!} {!!} ⦈
    --⊗-Cogen {f₁ = f₁} {f₂} {g} (deriveCogen iₗ) (deriveCogen iᵣ) 
  deriveCogen {I} I~ _ = μ (lift tt)
  deriveCogen {K x} {g} (K~ cg) gₐ = Call tt λ _ → cg gₐ
  deriveCogen {Z} Z~ = λ _ → Pure λ() 
