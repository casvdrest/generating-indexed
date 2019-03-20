{-# OPTIONS --type-in-type #-}

open import AgdaGen.Base
open import AgdaGen.Properties
open import AgdaGen.Data using (_∈_; here; there)
open import AgdaGen.Regular.Generic
open import AgdaGen.ListProperties
open import AgdaGen.Regular.Cogen
open import AgdaGen.Regular.Properties
open import AgdaGen.Monotonicity
open import AgdaGen.Indexed.Isomorphism

open import Relation.Binary.PropositionalEquality

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.Bool
open import Data.List
open import Data.Unit hiding (_≤_)
open import Data.List

open import Function

open import Category.Monad

module AgdaGen.Indexed.Properties where

  ⊎-split : ∀ {a b c : Set} → (h : a ⊎ b → c)
            → Σ[ f ∈ (a → c) ] Σ[ g ∈ (b → c) ]
              (λ { (inj₁ x) → f x ; (inj₂ y) → g y }) ≡ h
  ⊎-split f = (λ x → f ((inj₁ x))) , (λ y → f (inj₂ y))
    , funext λ { {inj₁ x} → refl ; {inj₂ y} → refl }

  ⊤-split : ∀ {a : Set} → (h : ⊤ → a) → Σ[ x ∈ a ] (λ { tt → x }) ≡ h
  ⊤-split h = (h tt) , refl

  _∘↝_ : ∀ {a : Set} → 𝔾 a → a → Set
  g ∘↝ x = g ∣ g ↝ x

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  CoComplete : ∀ {a : Set} → co𝔾 a → Set
  CoComplete {a} cg = ∀ {b : Set} → (σ : Σ[ g ∈ 𝔾 b ] Complete g g)
    → ∀ {f : a → b} → Σ[ f' ∈ (a → b) ] (cg (proj₁ σ) ∘↝ f') × (f' ≡ f)

  CoMonotone : ∀ {a : Set} → co𝔾 a → Set
  CoMonotone {a} cg = ∀ {b : Set} → (σ : Σ[ g ∈ 𝔾 b ] (∀ {y : b} → Depth-Monotone g y g))
    → ∀ {f : a → b} → Σ[ f' ∈ (a → b) ] (
        (∀ {n m : ℕ} → n ≤ m → f' ∈ ⟨ cg (proj₁ σ) ⟩ n
         → f' ∈ ⟨ cg (proj₁ σ) ⟩ m) × f' ≡ f )

  U-Cogen-Monotone :
    ∀ {g : Reg} → CoMonotone (deriveCogen {g = g} U~)
  U-Cogen-Monotone = {!!}

  U-Cogen-Complete :
    ∀ {g : Reg} → CoComplete (deriveCogen {g = g} U~)
  U-Cogen-Complete {b = b} σ {f} with ⊤-split f
  ... | x , eq rewrite
    sym eq with (proj₂ σ) {x}
  ... | zero , () 
  ... | suc n , elem with
    list-ap-complete {b = ⊤ → b} {fs = (λ x → λ { tt → x }) ∷ []} here elem
  ... | elem'  =
    (λ { tt → x }) , ((suc n) , elem') , funext (λ { {x} → refl} )

  ⊕-Cogen-Complete :
    ∀ {f₁ f₂ g : Reg}
    → ((i : RegInfo co𝔾 f₁) → CoComplete (deriveCogen {g = g} i) ×
        (∀ {a : Set} {x : ⟦ f₁ ⟧ (Fix g) → a} {gen : 𝔾 a}
          → Depth-Monotone (deriveCogen i gen) x (deriveCogen i gen)
      ))
    → ((i : RegInfo co𝔾 f₂) → CoComplete (deriveCogen {g = g} i) × 
        (∀ {a : Set} {x : ⟦ f₂ ⟧ (Fix g) → a} {gen : 𝔾 a}
          → Depth-Monotone (deriveCogen i gen) x (deriveCogen i gen)
      ))
    → (i : RegInfo co𝔾 (f₁ ⊕ f₂)) → CoComplete (deriveCogen {g = g} i)
  ⊕-Cogen-Complete {f₁} {f₂} {g = gᵣ} pₗ pᵣ (iₗ ⊕~ iᵣ) {b} σ {h} with ⊎-split h
  ⊕-Cogen-Complete {f₁} {f₂} {g = gᵣ} pₗ pᵣ (iₗ ⊕~ iᵣ) {b} σ {h} | f , g , eq
    rewrite sym eq with (proj₁ (pₗ iₗ)) σ {f}
  ... | .f , (zero  , () ) , refl
  ... | .f , (suc n , elₗ) , refl with
    (proj₁ (pᵣ iᵣ)) σ {g}
  ... | .g , (zero  , () ) , refl
  ... | .g , (suc m , elᵣ) , refl with
    list-ap-constr {c = ⟦ f₁ ⊕ f₂ ⟧ (Fix gᵣ) → b} {C = ⊎lift}
      (proj₂ (pₗ iₗ) (lemma-max₁ {n = suc n} {m = suc m}) elₗ)
      (proj₂ (pᵣ iᵣ) (lemma-max₂ {n = suc n} {m = suc m}) elᵣ)
  ... | apE = (λ { (inj₁ x) → f x ; (inj₂ y) → g y }) , (max (suc n) (suc m)
    , ∈x-rewr apE (funext λ { {inj₁ x} → refl ; {inj₂ y} → refl }))
    , funext λ { {inj₁ x} → refl ; {inj₂ y} → refl }

  cc→c : ∀ {a b : Set} → {cg : co𝔾 a} → (σ : Σ[ g ∈ 𝔾 b ] Complete g g)
         → CoComplete cg → Complete (cg (proj₁ σ)) (cg (proj₁ σ))
  cc→c σ cp {f} with cp σ {f}
  cc→c σ cp {f} | .f , elem , refl = elem 

  ⊗-Cogen-Complete :
    ∀ {f₁ f₂ g : Reg}
    → ((i : RegInfo co𝔾 f₁) → CoComplete (deriveCogen {g = g} i))
    → ((i : RegInfo co𝔾 f₂) → CoComplete (deriveCogen {g = g} i))
    → (i : RegInfo co𝔾 (f₁ ⊗ f₂)) → CoComplete (deriveCogen {g = g} i)
  ⊗-Cogen-Complete {f₁} {f₂} {g} pₗ pᵣ (iₗ ⊗~ iᵣ) {b} σ {h} with
    pₗ iₗ (deriveCogen {f = f₂} {g = g} iᵣ (proj₁ σ) , cc→c σ (pᵣ iᵣ)) {λ x y → h (x , y)}
  ... | f , (zero , ()) , snd
  ... | .(λ x y → h (x , y)) , (suc n , elem) , refl =
    h , ((suc n , list-ap-complete {fs = uncurry ∷ []} here elem) , refl)

  deriveCogen-Monotone :
    ∀ {f g : Reg}
    → (i₁ : RegInfo (λ a →
        Σ[ cg ∈ co𝔾 a ] ( ∀ {b : Set} {gen : 𝔾 b}
          → Complete (cg gen) (cg gen) ×
            (∀ {fₐ : a → b} → Depth-Monotone (cg gen) fₐ (cg gen)))
        ) g)
    → (i₂ : RegInfo (λ a →
        Σ[ cg ∈ co𝔾 a ] (∀ {b : Set} {gen : 𝔾 b}
          → Complete (cg gen) (cg gen) ×
            (∀ {fₐ : a → b} → Depth-Monotone (cg gen) fₐ (cg gen)))
        ) f)
    → ∀ {b : Set} {gen : 𝔾 b} {fᵣ : ⟦ f ⟧ (Fix g) → b}
        → Depth-Monotone (deriveCogen {g = g} (map-reginfo proj₁ i₂) gen)
            fᵣ (deriveCogen (map-reginfo proj₁ i₂) gen)
  deriveCogen-Monotone i₁ i₂ = {!!}

  deriveCogen-Complete :
    ∀ {f g : Reg} → (i₁ : RegInfo co𝔾 g) → (i₂ : RegInfo co𝔾 f) → CoComplete (deriveCogen {g = g} i₂)
  deriveCogen-Complete = {!!}
