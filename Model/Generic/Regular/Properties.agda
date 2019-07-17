open import Model.Base
open import Model.Combinators
open import Model.Enumerate
open import Model.Data using (_∈_; here; there)

open import Model.Properties.Monotonicity
open import Model.Properties.General
open import Model.Properties.Completeness

open import Model.Generic.Isomorphism

open import Model.Generic.Regular.Universe
open import Model.Generic.Regular.Cogen
open import Model.Generic.Regular.Instances
open import Model.Generic.Regular.Generator

open import Data.Unit hiding (_≤_)
open import Data.Product using (proj₁; proj₂; _,_; Σ; Σ-syntax; _×_)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.List
open import Data.Maybe using (just; nothing; Maybe)

open import Function
open import Level hiding (suc; zero)

open import Category.Monad

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

module Model.Generic.Regular.Properties where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄

  ------ U Combinator (Unit) ------

  ugen-monotone :
    ∀ {g : Reg} {x : ⟦_⟧ {0ℓ} U (Fix g)} {gi : RegInfo (λ S → 𝔾 (λ _ → S) tt) g}
    → Depth-Monotone (deriveGen {g = g} U~) (λ { tt → deriveGen gi }) tt
  ugen-monotone z≤n ()
  ugen-monotone (s≤s leq) elem = elem 

  ugen-complete :
    ∀ {g : Reg} {gi : RegInfo (λ S → 𝔾 (λ _ → S) tt) g}
    → Complete (deriveGen {g = g} U~) (λ { tt → deriveGen gi })
  ugen-complete = 1 , here
  
  
  ------ ⊕ combinator (Coproduct) ------

  ⊕gen-monotone-left :
    ∀ {f₁ f₂ g : Reg {0ℓ}} {tg : 𝔾 (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {x : ⟦ f₁ ⟧ (Fix g)}
      {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
    → Depth-Monotone g₁ (λ _ → tg) x
    → Depth-Monotone (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) (λ _ → tg) (inj₁ x)
  ⊕gen-monotone-left {g₁ = g₁} {g₂ = g₂} =
    ∥-inj₁-monotone-left {g₁ = g₁} {g₂ = g₂}

  ⊕gen-monotone-right :
    ∀ {f₁ f₂ g : Reg {0ℓ}} {tg : 𝔾 (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {y : ⟦ f₂ ⟧ (Fix g)}
      {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
    → Depth-Monotone g₂ (λ _ → tg) y
    → Depth-Monotone (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) (λ _ → tg) (inj₂ y)
  ⊕gen-monotone-right {g₁ = g₁} {g₂ = g₂} =
    ∥-inj₁-monotone-right {g₁ = g₁} {g₂ = g₂}
  
 
  -- If 'x' is produced by a generator, 'inj₁ x' is produced by generator derived
  -- from the coproduct of that generator with any other generator
  ⊕gen-complete-left :
    ∀ {f₁ f₂ g : Reg {0ℓ}} {tg : 𝔾 (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {x : ⟦ f₁ ⟧ (Fix g)} → g₁ ∣ (λ _ → tg)  ↝ x
    → (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) ∣ (λ _ → tg) ↝ inj₁ x
  ⊕gen-complete-left {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-left {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₁} p)

  -- If 'y' is produced by a generator, 'inj₂ y' is produced by the generator
  -- derived from the coproduct of any generator with that generator. 
  ⊕gen-complete-right :
    ∀ {f₁ f₂ g : Reg {0ℓ}} {tg : 𝔾 (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
    → {y : ⟦ f₂ ⟧ (Fix g)} → g₂ ∣ (λ _ → tg) ↝ y
    → (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) ∣ (λ _ → tg) ↝ inj₂ y
  ⊕gen-complete-right {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-right {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₂} p)
   
  ------ ⊗ combinator (Product) ------

  ,-inv :
    ∀ {a b : Set} {x₁ x₂ : a} {y₁ y₂ : b}
    → (x₁ , y₁) ≡ (x₂ , y₂) → x₁ ≡ x₂ × y₁ ≡ y₂
  ,-inv refl = refl , refl
  
  ⊗gen-monotone :
    ∀ {f₁ f₂ g : Reg {0ℓ}} {x  : ⟦ f₁ ⟧ (Fix g)}
      {y : ⟦ f₂ ⟧ (Fix g)} {tg : 𝔾 (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
    → Depth-Monotone g₁ (λ _ → tg) x → Depth-Monotone g₂ (λ _ → tg) y
    → Depth-Monotone ⦇ g₁ , g₂ ⦈ (λ _ → tg) (x , y)
  ⊗gen-monotone {g₁ = g₁} {g₂} mt₁ mt₂ =
    ⊛-monotone {g₁ = g₁} {g₂ = g₂} ,-inv mt₁ mt₂

  -- If both operands are complete, the generator derived from a product
  -- is complete as well. 
  ⊗gen-complete :
    ∀ {f₁ f₂ g : Reg {0ℓ}} {tg : 𝔾 (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (λ _ → ⟦ g ⟧ (Fix g)) tt}
      {x : ⟦ f₁ ⟧ (Fix g)} {y : ⟦ f₂ ⟧ (Fix g)}
    → Depth-Monotone g₁ (λ _ → tg) x → Depth-Monotone g₂ (λ _ → tg) y
    → (p₁ : g₁ ∣ (λ _ → tg) ↝ x) → (p₂ : g₂ ∣ (λ _ → tg) ↝ y)
    → ⦇ g₁ , g₂ ⦈ ∣ (λ _ → tg) ↝ (x , y)
  ⊗gen-complete {g₁ = g₁} {g₂ = g₂} mt₁ mt₂ p1 p2 =
    ⊛-complete {f = g₁} {g = g₂} p1 p2 mt₁ mt₂
  
  In-elem :
    ∀ {f : Reg {0ℓ}} {x : ⟦ f ⟧ (Fix f)} {xs : List (⟦ f ⟧ (Fix f))}
    → In {f = f} x ∈ map In xs → x ∈ xs
  In-elem {xs = []} ()
  In-elem {xs = x ∷ xs} here         = here
  In-elem {xs = x ∷ xs} (there elem) =
    there (In-elem elem)


  --=====================================================--
  ------ Monotonicity theorem for derived generators ------
  --=====================================================--

  deriveGen-monotone :
    ∀ {f g : Reg} {x : ⟦ f ⟧ (Fix g)}
    → (info₁ : RegInfo (λ a → Σ[ gen ∈ 𝔾 (λ _ → a) tt ]
        (Complete gen (λ _ → gen)) × (∀ {x : a} → Depth-Monotone gen (λ _ → gen) x)) f)
    → (info₂ : RegInfo (λ a → Σ[ gen ∈ 𝔾 (λ _ → a) tt ]
        Complete gen (λ _ → gen) × (∀ {x : a} → Depth-Monotone (gen) (λ _ → gen) x)) g)
    → Depth-Monotone (deriveGen {g = g} (map-reginfo proj₁ info₁))
                      (λ _ → deriveGen (map-reginfo proj₁ info₂)) x
  deriveGen-monotone {U} {g} info₁ info₂                                               = -- (U-combinator)
    ugen-monotone {gi = map-reginfo proj₁ info₂}
  deriveGen-monotone {f₁ ⊕ f₂} {g} {inj₁ x} (infoₗ ⊕~ infoᵣ) info₂ (s≤s leq) elem      = -- (⊕-combinator)
    ⊕gen-monotone-left {f₁ = f₁} {f₂ = f₂} {g = g}
      {g₂ = deriveGen (map-reginfo proj₁ infoᵣ)}
      (deriveGen-monotone infoₗ info₂) (s≤s leq) elem 
  deriveGen-monotone {f₁ ⊕ f₂} {g} {inj₂ y} (infoₗ ⊕~ infoᵣ) info₂ (s≤s leq) elem      = -- (⊗-combinator)
    ⊕gen-monotone-right {f₁ = f₁} {f₂ = f₂} {g = g}
      {g₁ = deriveGen (map-reginfo proj₁ infoₗ)}
      (deriveGen-monotone infoᵣ info₂) (s≤s leq) elem
  deriveGen-monotone {f₁ ⊗ f₂} {g} {x = x₁ , x₂} (infoₗ ⊗~ infoᵣ) info₂ (s≤s leq) elem = -- (I-combinator)
    ⊗gen-monotone {f₁ = f₁} {f₂ = f₂} {g = g}
      (deriveGen-monotone infoₗ info₂)
      (deriveGen-monotone infoᵣ info₂) (s≤s leq) elem
  deriveGen-monotone {I} {g} {x = In x} I~ info₂ (s≤s leq) elem with
    deriveGen-monotone {x = x} info₂ info₂
  ... | rec = ++-elem-left {ys = []}
    (map-preserves-elem (rec leq (In-elem {f = g} (map-++-ident elem))))
  deriveGen-monotone {K x} {g} (K~ info₁) info₂ (s≤s leq) elem                         = -- (K-combinator)
    (proj₂ ∘ proj₂) info₁ (s≤s leq) elem 

 
  --=====================================================--
  ------ Completeness theorem for derived generators ------
  --=====================================================--

  deriveGen-complete :
    ∀ {f g : Reg} {x : ⟦ f ⟧ (Fix g)}
    → (info₁ : RegInfo (λ a → Σ[ gen ∈ 𝔾 (λ _ → a) tt ]
        Complete gen (λ _ → gen) × (∀ {x : a} → Depth-Monotone gen (λ _ → gen) x)) f
      )
    → (info₂ : RegInfo (λ a → Σ[ gen ∈ 𝔾 (λ _ → a) tt  ]
        Complete gen (λ _ → gen) × (∀ {x : a} → Depth-Monotone gen (λ _ → gen) x)) g
      )
    → deriveGen (map-reginfo proj₁ info₁) ∣ (λ _ → deriveGen (map-reginfo proj₁ info₂)) ↝ x
  deriveGen-complete {U} {g} _ info₂                              = -- (U-combinator)
    ugen-complete {gi = map-reginfo proj₁ info₂}
  deriveGen-complete {f₁ ⊕ f₂} {g} {inj₁ x} (iₗ ⊕~ iᵣ) info₂      =  -- (⊕-combinator)
    ⊕gen-complete-left {f₁ = f₁} {f₂ = f₂} (deriveGen-complete iₗ info₂) 
  deriveGen-complete {f₁ ⊕ f₂} {g} {inj₂ y} (iₗ ⊕~ iᵣ) info₂ =
    ⊕gen-complete-right {f₁ = f₁} {f₂ = f₂} (deriveGen-complete iᵣ info₂) 
  deriveGen-complete {f₁ ⊗ f₂} {g} {x = x₁ , x₂} (iₗ ⊗~ iᵣ) info₂ = -- (⊗-combinator)
    ⊗gen-complete {f₁ = f₁} {f₂ = f₂}
      (deriveGen-monotone iₗ info₂) (deriveGen-monotone iᵣ info₂)
      (deriveGen-complete iₗ info₂) (deriveGen-complete iᵣ info₂)
  deriveGen-complete {I} {g} {In x} I~ info₂                      = let -- (I-combinator)
      (n , elem) = deriveGen-complete {x = x} info₂ info₂
    in suc n , (++-elem-left (map-preserves-elem elem))
  deriveGen-complete {K x} {g} {val} (K~ (gen , (prf , mt))) info₂
    with prf {val}
  ... | suc n , elem                                              = suc n , elem -- (K-combinator)


  deriveGen-Complete :
    ∀ {f : Reg}
    → (info : RegInfo (λ a → Σ[ gen ∈ 𝔾 (λ _ → a) tt ]
        Complete gen (λ _ → gen) × (∀ {x : a} → Depth-Monotone gen (λ _ → gen) x) ) f)
    → Complete (deriveGen (map-reginfo proj₁ info))
               (λ _ → deriveGen (map-reginfo proj₁ info))
  deriveGen-Complete {f} info {x}
    with deriveGen-complete {f = f} {g = f} {x = x} (info) info
  ... | n , p = n , p


  --======================================================================--
  ------ Completeness theorem for generators derived from isomorphism ------
  --======================================================================--

  In⁻¹ : ∀ {f : Reg {0ℓ}} → Fix f → ⟦ f ⟧ (Fix f)
  In⁻¹ (In x) = x

  μ-iso₂ : ∀ {f : Reg} {y : Fix f} → In (In⁻¹ y) ≡ y
  μ-iso₂ {y = In x} = refl

  -- Establish that `μ is bijective
  μ-iso : ∀ {f : Reg} → ⟦ f ⟧ (Fix f) ≃ Fix f
  μ-iso = record { from = In ; to = In⁻¹ ; iso₁ = refl ; iso₂ = μ-iso₂ }

  -- applying a bijective function to a complete generator yields another complete generator
  lemma-≃-derive :
    ∀ {a : Set} {f : Reg} {gen : Gen (⟦ f ⟧ (Fix f)) (λ _ → ⟦ f ⟧ (Fix f)) tt }
    → (iso : a ≃ Fix f) → Complete gen (λ _ → gen)
    → Complete {I = ⊤} (⦇ (_≃_.to iso ∘ In) (Call tt λ { tt → gen }) ⦈)
               (λ { tt_ → ⦇ (_≃_.to iso ∘ In) (Call tt λ { tt → gen }) ⦈ })
  lemma-≃-derive {a} {f} {gen} iso p {x}
    with p {In⁻¹ (_≃_.from iso x)}
  ... | suc n , elem
    rewrite ap-pure-is-map {xs = ⟨ (λ _ → gen) ⟩ tt (suc n)} {C = _≃_.to iso ∘ In} =
    suc n , ++-elem-left {xs = map (_≃_.to iso ∘ In) (⟨ (λ _ → gen) ⟩ tt (suc n))}
      (∈-rewr' (_≃_.iso₁ (≃-transitive iso (≃-symmetric μ-iso)))
        (map-preserves-elem elem))

  isoGen-Complete :
    ∀ {a : Set} ⦃ p : Regular a ⦄
    → (info : RegInfo (λ a → Σ[ gen ∈ 𝔾 (λ _ → a) tt ]
        Complete gen (λ _ → gen) × (∀ {x : a} → Depth-Monotone gen (λ _ → gen) x)) (getPf p))
    → Complete (isoGen (λ _ → a) (map-reginfo proj₁ info))
               (λ _ → isoGen (λ _ → a) (map-reginfo proj₁ info))
  isoGen-Complete ⦃ p ⦄ info =
    lemma-≃-derive {gen = deriveGen (map-reginfo proj₁ info)}
      (proj₂ (Regular.W p)) (deriveGen-Complete info)
