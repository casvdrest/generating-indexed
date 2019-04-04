open import Data.Product

module AgdaGen.Misc where

  Σ-map : ∀ {a : Set} {P Q : a → Set}
          → (∀ {y : a} → (P y → Q y))
          -------------------------------------
          → Σ[ x ∈ a ] P x → Σ[ x ∈ a ] Q x
  Σ-map f (fst , snd) = fst , f snd
          
  Σ-bimap : ∀ {a b : Set} {P : a → Set} {Q : b → Set}       
            → (f : a → b) → (∀ {y : a} → P y → Q (f y))
            -------------------------------------------
            → Σ[ x ∈ a ] P x → Σ[ x ∈ b ] Q x
  Σ-bimap f g (fst , snd) = f fst , g snd

  Σ₁ : ∀ {a : Set} {P : a → Set} → Σ[ x ∈ a ] P x → a
  Σ₁ (fst , _) = fst

  Σ₂ : ∀ {a : Set} {P : a → Set} → (p : Σ[ x ∈ a ] P x) → P (Σ₁ p)
  Σ₂ (_ , snd) = snd
