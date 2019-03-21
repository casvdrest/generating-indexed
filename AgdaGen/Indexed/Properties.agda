{-# OPTIONS --type-in-type #-}

open import AgdaGen.Base
open import AgdaGen.Properties
open import AgdaGen.Data using (_∈_; here; there)
open import AgdaGen.Regular.Generic
open import AgdaGen.ListProperties
open import AgdaGen.Regular.Cogen
open import AgdaGen.Regular.Properties
open import AgdaGen.Monotonicity
open import AgdaGen.Indexed.Isomorphism hiding (cong₂)

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

  `-Monotone :
    ∀ {a t : Set} {g : Gen a a} {tg : Gen t t} {x : a}
    → Depth-Monotone g x g → Depth-Monotone (` g) x tg
  `-Monotone mt z≤n () 
  `-Monotone mt (s≤s leq) elem = mt (s≤s leq) elem

  Z-Cogen-Monotone :
    ∀ {g : Reg} → CoMonotone (deriveCogen {g = g} Z~)
  Z-Cogen-Monotone σ {f} = (λ()) , (λ leq elem → pure-monotone leq elem) , funext λ { {()} }

  U-Cogen-Monotone :
    ∀ {g : Reg} → CoMonotone (deriveCogen {g = g} U~)
  U-Cogen-Monotone σ {f}  with ⊤-split f
  ... | x , eq rewrite
    sym eq with proj₂ σ {x}
  ... | mt = (λ { tt → x })
      , constr-monotone {C = λ x → λ { tt → x}}
        (λ {x} {y} → λ { eq → cong (λ f → f tt) eq })
        (`-Monotone mt)
      , funext λ {x} → refl

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

  eq→ext : ∀ {a b : Set} {f g : a → b} → f ≡ g → ∀ {x} → f x ≡ g x
  eq→ext refl = refl

  ⊎-funeq-left :
    ∀ {a b c : Set} {f₁ f₂ : a → c} {g₁ g₂ : b → c}
    → (∀ {x} → ⊎lift f₁ g₁ (inj₁ x) ≡ ⊎lift f₂ g₂ (inj₁ x)) → (∀ {x} → f₁ x ≡ f₂ x)
  ⊎-funeq-left eq {x} rewrite eq {x} = refl

  ⊎-funeq-right :
    ∀ {a b c : Set} {f₁ f₂ : a → c} {g₁ g₂ : b → c}
    → (∀ {y} → ⊎lift f₁ g₁ (inj₂ y) ≡ ⊎lift f₂ g₂ (inj₂ y)) → ∀ {y} → g₁ y ≡ g₂ y
  ⊎-funeq-right eq {y} rewrite eq {y} = refl

  ⊎-funeq : ∀ {a b c : Set} {f₁ f₂ : a → c} {g₁ g₂ : b → c} → ⊎lift f₁ g₁ ≡ ⊎lift f₂ g₂ → f₁ ≡ f₂ × g₁ ≡ g₂
  ⊎-funeq {f₁ = f₁} {f₂} {g₁} {g₂} eq 
    = funext (λ {x} → ⊎-funeq-left  {g₁ = g₁} {g₂ = g₂} λ {x} → eq→ext eq {inj₁ x})
    , funext (λ {y} → ⊎-funeq-right {f₁ = f₁} {f₂ = f₂} λ {y} → eq→ext eq {inj₂ y})

  ⊕-Cogen-Monotone :
    ∀ {f₁ f₂ g : Reg}
    → ((i : RegInfo (λ a → Σ[ cg ∈ co𝔾 a ] (∀ {b : Set} {gen : 𝔾 b}
          → Complete (cg gen) (cg gen) ×
            (∀ {fₐ : a → b} → Depth-Monotone (cg gen) fₐ (cg gen)))
        ) f₁) → CoMonotone (deriveCogen {g = g} (map-reginfo proj₁ i)))
    → ((i : RegInfo (λ a → Σ[ cg ∈ co𝔾 a ] (∀ {b : Set} {gen : 𝔾 b}
          → Complete (cg gen) (cg gen) ×
            (∀ {fₐ : a → b} → Depth-Monotone (cg gen) fₐ (cg gen)))
        ) f₂) → CoMonotone (deriveCogen {g = g} (map-reginfo proj₁ i)))
    → (i : RegInfo (λ a → Σ[ cg ∈ co𝔾 a ] (∀ {b : Set} {gen : 𝔾 b}
         → Complete (cg gen) (cg gen) ×
           (∀ {fₐ : a → b} → Depth-Monotone (cg gen) fₐ (cg gen)))) (f₁ ⊕ f₂))
    → CoMonotone (deriveCogen {g = g} (map-reginfo proj₁ i))
  ⊕-Cogen-Monotone {f₁} {f₂} {gᵣ} pₗ pᵣ (iₗ ⊕~ iᵣ) {b} σ {h} with ⊎-split h
  ... | f , g , eq rewrite
    sym eq with pₗ iₗ σ {f}
  ... | .f , mtₗ , refl
    with pᵣ iᵣ σ {g}
  ... | .g , mtᵣ , refl
    with ⊛-monotone {t = ⟦ f₁ ⊕ f₂ ⟧ (Fix gᵣ) → b}
      {tg = deriveCogen (map-reginfo proj₁ (iₗ ⊕~ iᵣ)) (proj₁ σ)}
      {C = ⊎lift} ⊎-funeq (`-Monotone mtₗ) (`-Monotone mtᵣ)
  ... | mt₊ = ⊎lift f g , mt₊ , funext λ { {inj₁ x} → refl ; {inj₂ y} → refl }

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

  cm→mt : ∀ {a b : Set} → {cg : co𝔾 a}
          → (σ : Σ[ g ∈ 𝔾 b ] (∀ {y : b} → Depth-Monotone g y g))
          → CoMonotone cg
          → ∀ {f : a → b} → Depth-Monotone (cg (proj₁ σ)) f (cg (proj₁ σ))
  cm→mt σ cm {f} with cm σ {f}
  cm→mt σ cm {.f'} | f' , fst , refl =
    λ leq elem → fst leq elem

  ⊗-Cogen-Monotone :
    ∀ {f₁ f₂ g : Reg}
    → ((i : RegInfo (λ a → Σ[ cg ∈ co𝔾 a ] (∀ {b : Set} {gen : 𝔾 b}
          → Complete (cg gen) (cg gen) ×
            (∀ {fₐ : a → b} → Depth-Monotone (cg gen) fₐ (cg gen)))
        ) f₁) → CoMonotone (deriveCogen {g = g} (map-reginfo proj₁ i)))
    → ((i : RegInfo (λ a → Σ[ cg ∈ co𝔾 a ] (∀ {b : Set} {gen : 𝔾 b}
          → Complete (cg gen) (cg gen) ×
            (∀ {fₐ : a → b} → Depth-Monotone (cg gen) fₐ (cg gen)))
        ) f₂) → CoMonotone (deriveCogen {g = g} (map-reginfo proj₁ i)))
    → (i : RegInfo (λ a → Σ[ cg ∈ co𝔾 a ] (∀ {b : Set} {gen : 𝔾 b} 
          → Complete (cg gen) (cg gen) ×
          (∀ {fₐ : a → b} → Depth-Monotone (cg gen) fₐ (cg gen)))
        ) (f₁ ⊗ f₂)) → CoMonotone (deriveCogen {g = g} (map-reginfo proj₁ i))
  ⊗-Cogen-Monotone {f₁} {f₂} {gᵣ} pₗ pᵣ (iₗ ⊗~ iᵣ) {b} σ {h} with
    pₗ iₗ (deriveCogen {f = f₂} {g = gᵣ}
      (map-reginfo proj₁ iᵣ) (proj₁ σ)
    , cm→mt σ (pᵣ iᵣ)) {curry h}
  ... | .(curry h) , mt , refl =
    h , ( λ {  z≤n ()
            ; (s≤s leq) elem →
                list-ap-complete {fs = uncurry  ∷ []} here
                  (mt (s≤s leq) let h' , (elem , eq) = (ap-singleton elem) in
                  ∈x-rewr elem (funext λ {x} → cong (λ f y → f (x , y)) eq))
            }) , refl

  cc→c : ∀ {a b : Set} {cg : co𝔾 a} → (σ : Σ[ g ∈ 𝔾 b ] Complete g g)
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
    → ∀ {b : Set} {gen : 𝔾 b}
        → CoMonotone (deriveCogen {g = g} (map-reginfo proj₁ i₂))
  deriveCogen-Monotone {Z} {g} i₁ Z~ = Z-Cogen-Monotone {g = g}
  deriveCogen-Monotone {U} {g} i₁ i₂ = U-Cogen-Monotone {g = g}
  deriveCogen-Monotone {f₁ ⊕ f₂} {g} i₁ (iₗ ⊕~ iᵣ) {b} {gen} =
    ⊕-Cogen-Monotone
      (λ i σ → deriveCogen-Monotone i₁ i {b} {gen} σ)
      (λ i σ → deriveCogen-Monotone i₁ i {b} {gen} σ) (iₗ ⊕~ iᵣ)
  deriveCogen-Monotone {f₁ ⊗ f₂} {g} i₁ (iₗ ⊗~ iᵣ) {b} {gen} =
    ⊗-Cogen-Monotone
      (λ i σ → deriveCogen-Monotone i₁ i {b} {gen} σ)
      (λ i σ → deriveCogen-Monotone i₁ i {b} {gen} σ) (iₗ ⊗~ iᵣ)
  deriveCogen-Monotone {I} {g} i₁ i₂ σ = {!!} , {!!}
  deriveCogen-Monotone {K x} {g} i₁ (K~ x₁) = {!!}

  deriveCogen-Complete :
    ∀ {f g : Reg} → (i₁ : RegInfo co𝔾 g) → (i₂ : RegInfo co𝔾 f) → CoComplete (deriveCogen {g = g} i₂)
  deriveCogen-Complete = {!!}
