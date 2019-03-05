open import src.Gen.Base
open import src.Gen.Monotonicity
open import src.Gen.ListProperties
open import src.Gen.Properties
open import src.Gen.Regular.Generic
open import src.Gen.Regular.Isomorphism
open import src.Data using (_∈_; here; there; Π)

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

module src.Gen.Regular.Properties where

  open RawMonad ⦃...⦄ using (_⊛_; pure)

  ------ U Combinator (Unit) ------

  ugen-monotone : ∀ {g : Reg} {x : ⟦ U ⟧ (μ g)} {gi : RegInfo (λ a → ⟪ 𝔾 a ⟫) g}
                  → Depth-Monotone (deriveGen {f = U} {g = g} U~ ⟨ deriveGen gi ⟩) x
  ugen-monotone = pure-monotone

  ugen-complete : ∀ {g : Reg} {gi : RegInfo (λ a → ⟪ 𝔾 a ⟫) g}
                  ----------------------------------------------------------
                  → Complete (deriveGen {f = U} {g = g} U~ ⟨ deriveGen gi ⟩)
  ugen-complete = 1 , here
  
  
  ------ ⊕ combinator (Coproduct) ------

  ⊕gen-monotone-left : ∀ {a : Set} {f g : Reg}
                         {x : ⟦ f ⟧ a}
                         {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                         {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                       → Depth-Monotone g₁ x 
                       ---------------------------------------
                       → Depth-Monotone (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) (inj₁ x)
  ⊕gen-monotone-left {g₁ = g₁} {g₂ = g₂} = ∥-monotone-left {g₁ = g₁} {g₂ = g₂}

  ⊕gen-monotone-right : ∀ {a : Set} {f g : Reg}
                         {y : ⟦ g ⟧ a}
                         {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                         {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                       → Depth-Monotone g₂ y 
                       ---------------------------------------
                       → Depth-Monotone (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) (inj₂ y)
  ⊕gen-monotone-right {g₁ = g₁} {g₂ = g₂} = ∥-monotone-right {g₁ = g₁} {g₂ = g₂}
  
  
  -- If 'x' is produced by a generator, 'inj₁ x' is produced by generator derived
  -- from the coproduct of that generator with any other generator
  ⊕gen-complete-left : ∀ {a : Set} {f g : Reg}
                         {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                         {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                         {x : ⟦ f ⟧ a} → g₁ ↝ x
                       --------------------------------------
                       → (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) ↝ inj₁ x
  ⊕gen-complete-left {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-left {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₁} p)
      
  
  -- If 'y' is produced by a generator, 'inj₂ y' is produced by the generator
  -- derived from the coproduct of any generator with that generator. 
  ⊕gen-complete-right : ∀ {a : Set} {f g : Reg}
                          {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                          {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                        → {y : ⟦ g ⟧ a} → g₂ ↝ y
                        -------------------------------------
                        → (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈) ↝ inj₂ y
  ⊕gen-complete-right {g₁ = g₁} {g₂ = g₂} p =
    ∥-complete-right {f = ⦇ inj₁ g₁ ⦈} {g = ⦇ inj₂ g₂ ⦈}
      (constr-preserves-elem {g = g₂} p)

  
  -- Given that its operands are complete, the generator derived from
  -- a coproduct is complete
  ⊕gen-Complete : ∀ {a : Set} {f g : Reg}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                  → Complete g₁ → Complete g₂
                  ---------------------------------------
                  → Complete (⦇ inj₁ g₁ ⦈ ∥ ⦇ inj₂ g₂ ⦈)
  ⊕gen-Complete {f = f} {g = g} {g₁} {g₂} p₁ p₂ {inj₁ x} =
    ⊕gen-complete-left {f = f} {g = g} {g₁ = g₁} {g₂ = g₂} p₁
  ⊕gen-Complete {f = f} {g = g} {g₁} {g₂} p₁ p₂ {inj₂ y} =
    ⊕gen-complete-right {f = f} {g = g} {g₁ = g₁} {g₂ = g₂} p₂


  ------ ⊗ combinator (Product) ------

  ,-inv : ∀ {a b : Set} {x₁ x₂ : a} {y₁ y₂ : b} → (x₁ , y₁) ≡ (x₂ , y₂) → x₁ ≡ x₂ × y₁ ≡ y₂
  ,-inv refl = refl , refl
  
  ⊗gen-monotone : ∀ {a : Set} {f g : Reg} {x  : ⟦ f ⟧ a} {y : ⟦ g ⟧ a}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                  → Depth-Monotone g₁ x → Depth-Monotone g₂ y
                  --------------------------------------
                  → Depth-Monotone ⦇ g₁ , g₂ ⦈ (x , y)
  ⊗gen-monotone {g₁ = g₁} {g₂} mt₁ mt₂ = ⊛-monotone {g₁ = g₁} {g₂ = g₂} ,-inv mt₁ mt₂

  
  -- If both operands are complete, the generator derived from a product
  -- is complete as well. 
  ⊗gen-complete : ∀ {a : Set} {f g : Reg}
                    {g₁ : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ a) n}
                    {g₂ : ∀ {n : ℕ} → 𝔾 (⟦ g ⟧ a) n}
                    {x : ⟦ f ⟧ a} {y : ⟦ g ⟧ a}
                  → Depth-Monotone g₁ x → Depth-Monotone g₂ y
                  → (p₁ : g₁ ↝ x) → (p₂ : g₂ ↝ y)
                  --------------------------------------
                  → ⦇ g₁ , g₂ ⦈ ↝ (x , y)
  ⊗gen-complete {g₁ = g₁} {g₂ = g₂} mt₁ mt₂ p1 p2 =
    ⊛-complete {f = g₁} {g = g₂} p1 p2 mt₁ mt₂


  `μ-elem : ∀ {f : Reg} {x : ⟦ f ⟧ (μ f)} {xs : List (⟦ f ⟧ (μ f))} → `μ {f = f} x ∈ map `μ xs → x ∈ xs
  `μ-elem {xs = []} ()
  `μ-elem {xs = x ∷ xs} here = here
  `μ-elem {xs = x ∷ xs} (there elem) = there (`μ-elem elem)

  ≤-eq? : ∀ {n m : ℕ} → n ≤ m → Maybe (n ≡ m)
  ≤-eq? z≤n = nothing
  ≤-eq? (s≤s p) = Data.Maybe.map (cong suc) (≤-eq? p)

  ------ Generator Derivation ------

  --=====================================================--
  ------ Monotonicity theorem for derived generators ------
  --=====================================================--
  
  fix-step : ∀  {a : Set} {x : a} {g : ⟪ 𝔾 a ⟫} → Depth-Monotone (g ⟨ g ⟩) x → Depth-Monotone (⟨ g ⟩) x
  fix-step {g = g} prf z≤n ()
  fix-step {g = g} prf (s≤s leq) elem = prf leq elem

  deriveGen-monotone :
    ∀ {f g : Reg} {x : ⟦ f ⟧ (μ g)}
    → (info₁ : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ]
        Complete ⟨ gen ⟩ × (∀ {x : a} → Depth-Monotone (⟨ gen ⟩) x)) f)
    → (info₂ : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ]
        Complete ⟨ gen ⟩ × (∀ {x : a} → Depth-Monotone (⟨ gen ⟩) x)) g)
    → Depth-Monotone (deriveGen {f = f} {g = g} (map-reginfo proj₁ info₁)
        ⟨ deriveGen {f = g} {g = g} (map-reginfo proj₁ info₂) ⟩) x
  deriveGen-monotone {U} {g} info₁ info₂ = ugen-monotone {gi = map-reginfo proj₁ info₂}
  deriveGen-monotone {f₁ ⊕ f₂} {g} {inj₁ x} (infoₗ ⊕~ infoᵣ) info₂ =
    ⊕gen-monotone-left {f = f₁} {g = f₂}
      {g₁ = deriveGen (map-reginfo proj₁ infoₗ)
        ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩
      } {g₂ = deriveGen (map-reginfo proj₁ infoᵣ)
        ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩
      } (deriveGen-monotone infoₗ info₂)
  deriveGen-monotone {f₁ ⊕ f₂} {g} {inj₂ y} (infoₗ ⊕~ infoᵣ) info₂ =
    ⊕gen-monotone-right {f = f₁} {g = f₂}
      {g₁ = deriveGen (map-reginfo proj₁ infoₗ)
        ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩
      } {g₂ = deriveGen (map-reginfo proj₁ infoᵣ)
        ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩
      } (deriveGen-monotone infoᵣ info₂) 
  deriveGen-monotone {f₁ ⊗ f₂} {g} {x = x₁ , x₂} (infoₗ ⊗~ infoᵣ) info₂ =
    ⊗gen-monotone {f = f₁} {g = f₂}
      {g₁ = deriveGen (map-reginfo proj₁ infoₗ)
        ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩}
      {g₂ = deriveGen (map-reginfo proj₁ infoᵣ)
        ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩}
      (deriveGen-monotone infoₗ info₂)
      (deriveGen-monotone infoᵣ info₂)
  deriveGen-monotone {I} {g} {x = `μ x} I~ info₂ =
    constr-monotone {g = ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩}
      (λ { refl → refl }) (fix-step (deriveGen-monotone {x = x} info₂ info₂))
  deriveGen-monotone {K x} {g} (K~ info₁) info₂ = (proj₂ ∘ proj₂) info₁

  
  --=====================================================--
  ------ Completeness theorem for derived generators ------
  --=====================================================--

  deriveGen-complete :
    ∀ {f g : Reg} {x : ⟦ f ⟧ (μ g)}
    → (info₁ : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ]
        Complete ⟨ gen ⟩ × (∀ {x : a} → Depth-Monotone (⟨ gen ⟩) x)) f
      )
    → (info₂ : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ]
        Complete ⟨ gen ⟩ × (∀ {x : a} → Depth-Monotone (⟨ gen ⟩) x)) g
      )
    → (deriveGen {f = f} {g = g} (map-reginfo proj₁ info₁)
        ⟨ deriveGen {f = g} {g = g} (map-reginfo proj₁ info₂) ⟩
      ) ↝ x
  deriveGen-complete {U} {g} _ info₂ =
    ugen-complete {gi = map-reginfo proj₁ info₂}
  deriveGen-complete {f₁ ⊕ f₂} {g} {inj₁ x} (iₗ ⊕~ iᵣ) info₂ =
    ⊕gen-complete-left {f = f₁} {g = f₂}
      {g₁ = deriveGen {f = f₁} {g = g}
      (map-reginfo proj₁ iₗ)
        ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩}
      {g₂ = deriveGen {f = f₂} {g = g}
        (map-reginfo proj₁ iᵣ)
          ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩}
      {x = x} (deriveGen-complete iₗ info₂)
  deriveGen-complete {f₁ ⊕ f₂} {g} {inj₂ y} (iₗ ⊕~ iᵣ) info₂ =
    ⊕gen-complete-right {f = f₁} {g = f₂}
      {g₁ = deriveGen {f = f₁} {g = g}
        (map-reginfo proj₁ iₗ)
          ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩}
      {g₂ = deriveGen {f = f₂} {g = g}
        (map-reginfo proj₁ iᵣ)
          ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩}
      {y = y} (deriveGen-complete iᵣ info₂)
  deriveGen-complete {f₁ ⊗ f₂} {g} {x = x₁ , x₂} (iₗ ⊗~ iᵣ) info₂ =
    ⊗gen-complete {f = f₁} {g = f₂}
      {g₁ = deriveGen (map-reginfo proj₁ iₗ)
        ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩}
      {g₂ = deriveGen (map-reginfo proj₁ iᵣ)
        ⟨ deriveGen (map-reginfo proj₁ info₂) ⟩}
      (deriveGen-monotone iₗ info₂) (deriveGen-monotone iᵣ info₂)
      (deriveGen-complete iₗ info₂) (deriveGen-complete iᵣ info₂)
  deriveGen-complete {I} {g} {`μ x} I~ info₂ = let
      (n , elem) = deriveGen-complete {x = x} info₂ info₂
    in suc n , (++-elem-left (map-preserves-elem elem))
  deriveGen-complete {K x} {g} (K~ info₁) info₂ = (proj₁ ∘ proj₂) info₁
  
  deriveGen-Complete :
    ∀ {f : Reg}
    → (info : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ]
        Complete ⟨ gen ⟩ × (∀ {x : a} → Depth-Monotone (⟨ gen ⟩) x) ) f)
    → Complete ⟨ deriveGen {f = f} {g = f} (map-reginfo proj₁ info) ⟩
  deriveGen-Complete {f} info {x}
    with deriveGen-complete {f = f} {g = f} {x = x} (info) info
  ... | n , p = suc n , p


  --======================================================================--
  ------ Completeness theorem for generators derived from isomorphism ------
  --======================================================================--

  `μ⁻¹ : ∀ {f : Reg} → μ f → ⟦ f ⟧ (μ f)
  `μ⁻¹ (`μ x) = x

  μ-iso₂ : ∀ {f : Reg} {y : μ f} → `μ (`μ⁻¹ y) ≡ y
  μ-iso₂ {y = `μ x} = refl

  -- Establish that `μ is bijective
  μ-iso : ∀ {f : Reg} → ⟦ f ⟧ (μ f) ≅ μ f
  μ-iso = record { from = `μ ; to = `μ⁻¹ ; iso₁ = refl ; iso₂ = μ-iso₂ }

  -- applying a bijective function to a complete generator yields another complete generator
  lemma-≅-derive :
    ∀ {a : Set} {f : Reg} {gen : ∀ {n : ℕ} → 𝔾 (⟦ f ⟧ (μ f)) n }
    → (iso : a ≅ μ f) → Complete gen → Complete ⦇ (_≅_.to iso ∘ `μ) gen ⦈
  lemma-≅-derive {a} {f} {gen} iso p {x} with p {(`μ⁻¹ ∘ _≅_.from iso) x}
  ... | n , snd rewrite
    sym (_≅_.iso₂ (≅-transitive μ-iso (≅-symmetric iso)) {y = x})
    = n , ++-elem-left {ys = []}
      (map-preserves-elem (∈-rewr'
        (_≅_.iso₁ (≅-transitive μ-iso (≅-symmetric iso))) snd))
  
  isoGen-Complete :
    ∀ {a : Set} ⦃ p : Regular a ⦄
    → (info : RegInfo (λ a → Σ[ gen ∈ ⟪ 𝔾 a ⟫ ]
        Complete ⟨ gen ⟩ × (∀ {x : a} → Depth-Monotone (⟨ gen ⟩) x)) (getPf p))
    → Complete (isoGen a (map-reginfo proj₁ info))
  isoGen-Complete ⦃ p ⦄ info =
    lemma-≅-derive {gen = ⟨ deriveGen (map-reginfo proj₁ info) ⟩}
      (proj₂ (Regular.W p)) (deriveGen-Complete info)


