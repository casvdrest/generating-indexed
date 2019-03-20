open import AgdaGen.Base
open import AgdaGen.Monotonicity
open import AgdaGen.ListProperties
open import AgdaGen.Properties
open import AgdaGen.Regular.Generic
open import AgdaGen.Regular.Cogen
open import AgdaGen.Regular.Isomorphism
open import AgdaGen.Data using (_∈_; here; there; Π)

open import Data.Unit hiding (_≤_)
open import Data.Product using (proj₁; proj₂; _,_; Σ; Σ-syntax; _×_)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.List
open import Data.Maybe using (just; nothing; Maybe)

open import Function

open import Category.Monad

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

module AgdaGen.Regular.Properties where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  ------ U Combinator (Unit) ------

  ugen-monotone : ∀ {g : Reg} {x : ⟦ U ⟧ (Fix g)} {gi : RegInfo 𝔾 g}
                  → Depth-Monotone (deriveGen {g = g} U~) x (deriveGen gi)
  ugen-monotone = pure-monotone

 
  ugen-complete : ∀ {g : Reg} {gi : RegInfo 𝔾 g}
                  ----------------------------------------------------------
                  → Complete (deriveGen {g = g} U~) (deriveGen gi)
  ugen-complete = 1 , here
  
  
  ------ ⊕ combinator (Coproduct) ------

  ⊕gen-monotone-left : ∀ {f₁ f₂ g : Reg} {tg : 𝔾 (⟦ g ⟧ (Fix g))}
                         {x : ⟦ f₁ ⟧ (Fix g)}
                         {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                         {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                       → Depth-Monotone g₁ x tg
                       ---------------------------------------
                       → Depth-Monotone (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) (inj₁ x) tg
  ⊕gen-monotone-left {g₁ = g₁} {g₂ = g₂} = ∥-inj₁-monotone-left {g₁ = g₁} {g₂ = g₂}

  
  ⊕gen-monotone-right : ∀ {f₁ f₂ g : Reg} {tg : 𝔾 (⟦ g ⟧ (Fix g))}
                          {y : ⟦ f₂ ⟧ (Fix g)}
                          {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                          {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                        → Depth-Monotone g₂ y tg
                        ---------------------------------------
                        → Depth-Monotone (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) (inj₂ y) tg
  ⊕gen-monotone-right {g₁ = g₁} {g₂ = g₂} = ∥-inj₂-monotone-right {g₁ = g₁} {g₂ = g₂}
  
  
  -- If 'x' is produced by a generator, 'inj₁ x' is produced by generator derived
  -- from the coproduct of that generator with any other generator
  ⊕gen-complete-left : ∀ {f₁ f₂ g : Reg} {tg : 𝔾 (⟦ g ⟧ (Fix g))}
                         {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                         {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                         {x : ⟦ f₁ ⟧ (Fix g)} → g₁ ∣ tg  ↝ x
                       --------------------------------------
                       → (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) ∣ tg ↝ inj₁ x
  ⊕gen-complete-left {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-left {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₁} p)
      
  
  -- If 'y' is produced by a generator, 'inj₂ y' is produced by the generator
  -- derived from the coproduct of any generator with that generator. 
  ⊕gen-complete-right : ∀ {f₁ f₂ g : Reg} {tg : 𝔾 (⟦ g ⟧ (Fix g))}
                          {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                          {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                        → {y : ⟦ f₂ ⟧ (Fix g)} → g₂ ∣ tg ↝ y
                        -------------------------------------
                        → (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) ∣ tg ↝ inj₂ y
  ⊕gen-complete-right {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-right {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₂} p)
  
  
  ------ ⊗ combinator (Product) ------

  ,-inv : ∀ {a b : Set} {x₁ x₂ : a} {y₁ y₂ : b} → (x₁ , y₁) ≡ (x₂ , y₂) → x₁ ≡ x₂ × y₁ ≡ y₂
  ,-inv refl = refl , refl

    
  ⊗gen-monotone : ∀ {f₁ f₂ g : Reg} {x  : ⟦ f₁ ⟧ (Fix g)}
                    {y : ⟦ f₂ ⟧ (Fix g)} {tg : 𝔾 (⟦ g ⟧ (Fix g))}
                    {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                    {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                  → Depth-Monotone g₁ x tg → Depth-Monotone g₂ y tg
                  -------------------------------------------------
                  → Depth-Monotone ⦇ g₁ , g₂ ⦈ (x , y) tg
  ⊗gen-monotone {g₁ = g₁} {g₂} mt₁ mt₂ = ⊛-monotone {g₁ = g₁} {g₂ = g₂} ,-inv mt₁ mt₂

  
  -- If both operands are complete, the generator derived from a product
  -- is complete as well. 
  ⊗gen-complete : ∀ {f₁ f₂ g : Reg} {tg : 𝔾 (⟦ g ⟧ (Fix g))}
                    {g₁ : Gen (⟦ f₁ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                    {g₂ : Gen (⟦ f₂ ⟧ (Fix g)) (⟦ g ⟧ (Fix g))}
                    {x : ⟦ f₁ ⟧ (Fix g)} {y : ⟦ f₂ ⟧ (Fix g)}
                  → Depth-Monotone g₁ x tg → Depth-Monotone g₂ y tg
                  → (p₁ : g₁ ∣ tg ↝ x) → (p₂ : g₂ ∣ tg ↝ y)
                  --------------------------------------
                  → ⦇ g₁ , g₂ ⦈ ∣ tg ↝ (x , y)
  ⊗gen-complete {g₁ = g₁} {g₂ = g₂} mt₁ mt₂ p1 p2 =
    ⊛-complete {f = g₁} {g = g₂} p1 p2 mt₁ mt₂

  
  In-elem : ∀ {f : Reg} {x : ⟦ f ⟧ (Fix f)} {xs : List (⟦ f ⟧ (Fix f))} → In {f = f} x ∈ map In xs → x ∈ xs
  In-elem {xs = []} ()
  In-elem {xs = x ∷ xs} here = here
  In-elem {xs = x ∷ xs} (there elem) = there (In-elem elem)

  --=====================================================--
  ------ Monotonicity theorem for derived generators ------
  --=====================================================--

  deriveGen-monotone :
    ∀ {f g : Reg} {x : ⟦ f ⟧ (Fix g)}
    → (info₁ : RegInfo (λ a → Σ[ gen ∈ 𝔾 a ]
        (Complete gen gen) × (∀ {x : a} → Depth-Monotone gen x gen)) f)
    → (info₂ : RegInfo (λ a → Σ[ gen ∈ 𝔾 a ]
        Complete gen gen × (∀ {x : a} → Depth-Monotone (gen) x gen)) g)
    → Depth-Monotone (deriveGen {g = g} (map-reginfo proj₁ info₁))
                      x (deriveGen (map-reginfo proj₁ info₂))
  deriveGen-monotone {U} {g} info₁ info₂ =
    ugen-monotone {gi = map-reginfo proj₁ info₂}
  deriveGen-monotone {f₁ ⊕ f₂} {g} {inj₁ x} (infoₗ ⊕~ infoᵣ) info₂ (s≤s leq) elem =
    ⊕gen-monotone-left {f₁ = f₁} {f₂ = f₂} {g = g}
      {g₂ = deriveGen (map-reginfo proj₁ infoᵣ)}
      (deriveGen-monotone infoₗ info₂) (s≤s leq) elem 
  deriveGen-monotone {f₁ ⊕ f₂} {g} {inj₂ y} (infoₗ ⊕~ infoᵣ) info₂ (s≤s leq) elem  =
    ⊕gen-monotone-right {f₁ = f₁} {f₂ = f₂} {g = g}
      {g₁ = deriveGen (map-reginfo proj₁ infoₗ)}
      (deriveGen-monotone infoᵣ info₂) (s≤s leq) elem
  deriveGen-monotone {f₁ ⊗ f₂} {g} {x = x₁ , x₂} (infoₗ ⊗~ infoᵣ) info₂ (s≤s leq) elem =
    ⊗gen-monotone {f₁ = f₁} {f₂ = f₂} {g = g}
      (deriveGen-monotone infoₗ info₂)
      (deriveGen-monotone infoᵣ info₂) (s≤s leq) elem
  deriveGen-monotone {I} {g} {x = In x} I~ info₂ (s≤s leq) elem with
    deriveGen-monotone {x = x} info₂ info₂
  ... | rec = ++-elem-left {ys = []}
    (map-preserves-elem (rec leq (In-elem {f = g} (map-++-ident elem))))
  deriveGen-monotone {K x} {g} (K~ info₁) info₂ (s≤s leq) elem =
    (proj₂ ∘ proj₂) info₁ (s≤s leq) elem 

  
  --=====================================================--
  ------ Completeness theorem for derived generators ------
  --=====================================================--

  deriveGen-complete :
    ∀ {f g : Reg} {x : ⟦ f ⟧ (Fix g)}
    → (info₁ : RegInfo (λ a → Σ[ gen ∈ 𝔾 a ]
        Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen)) f
      )
    → (info₂ : RegInfo (λ a → Σ[ gen ∈ 𝔾 a ]
        Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen)) g
      )
    → deriveGen (map-reginfo proj₁ info₁) ∣ deriveGen (map-reginfo proj₁ info₂) ↝ x
  deriveGen-complete {U} {g} _ info₂ =
    ugen-complete {gi = map-reginfo proj₁ info₂}
  deriveGen-complete {f₁ ⊕ f₂} {g} {inj₁ x} (iₗ ⊕~ iᵣ) info₂ =
    ⊕gen-complete-left {f₁ = f₁} {f₂ = f₂} (deriveGen-complete iₗ info₂) 
  deriveGen-complete {f₁ ⊕ f₂} {g} {inj₂ y} (iₗ ⊕~ iᵣ) info₂ =
    ⊕gen-complete-right {f₁ = f₁} {f₂ = f₂} (deriveGen-complete iᵣ info₂) 
  deriveGen-complete {f₁ ⊗ f₂} {g} {x = x₁ , x₂} (iₗ ⊗~ iᵣ) info₂ =
    ⊗gen-complete {f₁ = f₁} {f₂ = f₂}
      (deriveGen-monotone iₗ info₂) (deriveGen-monotone iᵣ info₂)
      (deriveGen-complete iₗ info₂) (deriveGen-complete iᵣ info₂)
  deriveGen-complete {I} {g} {In x} I~ info₂ = let
      (n , elem) = deriveGen-complete {x = x} info₂ info₂
    in suc n , (++-elem-left (map-preserves-elem elem))
  deriveGen-complete {K x} {g} {val} (K~ (gen , (prf , mt))) info₂ with prf {val}
  ... | suc n , elem = suc n , elem


  deriveGen-Complete :
    ∀ {f : Reg}
    → (info : RegInfo (λ a → Σ[ gen ∈ 𝔾 a ]
        Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen) ) f)
    → Complete (deriveGen (map-reginfo proj₁ info)) (deriveGen (map-reginfo proj₁ info))
  deriveGen-Complete {f} info {x}
    with deriveGen-complete {f = f} {g = f} {x = x} (info) info
  ... | n , p = n , p


  --======================================================================--
  ------ Completeness theorem for generators derived from isomorphism ------
  --======================================================================--

  In⁻¹ : ∀ {f : Reg} → Fix f → ⟦ f ⟧ (Fix f)
  In⁻¹ (In x) = x

  μ-iso₂ : ∀ {f : Reg} {y : Fix f} → In (In⁻¹ y) ≡ y
  μ-iso₂ {y = In x} = refl

  -- Establish that `μ is bijective
  μ-iso : ∀ {f : Reg} → ⟦ f ⟧ (Fix f) ≅ Fix f
  μ-iso = record { from = In ; to = In⁻¹ ; iso₁ = refl ; iso₂ = μ-iso₂ }

  -- applying a bijective function to a complete generator yields another complete generator
  lemma-≅-derive :
    ∀ {a : Set} {f : Reg} {gen : Gen (⟦ f ⟧ (Fix f)) (⟦ f ⟧ (Fix f)) }
    → (iso : a ≅ Fix f) → Complete gen gen → Complete (⦇ (_≅_.to iso ∘ In) (` gen) ⦈) (⦇ (_≅_.to iso ∘ In) (` gen) ⦈)
  lemma-≅-derive {a} {f} {gen} iso p {x} with p {In⁻¹ (_≅_.from iso x)}
  ... | suc n , elem rewrite ap-pure-is-map {xs = ⟨ gen ⟩ (suc n)} {C = _≅_.to iso ∘ In} =
    suc n , ++-elem-left {xs = map (_≅_.to iso ∘ In) (⟨ gen ⟩ (suc n))}
      (∈-rewr' (_≅_.iso₁ (≅-transitive iso (≅-symmetric μ-iso))) (map-preserves-elem elem))

  isoGen-Complete :
    ∀ {a : Set} ⦃ p : Regular a ⦄
    → (info : RegInfo (λ a → Σ[ gen ∈ 𝔾 a ]
        Complete gen gen × (∀ {x : a} → Depth-Monotone gen x gen)) (getPf p))
    → Complete (isoGen a (map-reginfo proj₁ info))
               (isoGen a (map-reginfo proj₁ info))
  isoGen-Complete ⦃ p ⦄ info =
    lemma-≅-derive {gen = deriveGen (map-reginfo proj₁ info)}
      (proj₂ (Regular.W p)) (deriveGen-Complete info)
