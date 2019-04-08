open import AgdaGen.BaseI

module AgdaGen.CombinatorsI where

  genᵢMap : ∀ {ℓ k} {i : Set k} {f g t : i → Set ℓ} {x : i} → (f x → g x) → Genᵢ f t x → Genᵢ g t x
  genᵢMap f g = Apᵢ (Pureᵢ f) g

  genᵢPure : ∀ {ℓ k} {i : Set k} {f t : i → Set ℓ} {x : i} → f x → Genᵢ f t x
  genᵢPure = Pureᵢ

  genᵢAp : ∀ {ℓ k} {i : Set k} {f g t : i → Set ℓ} {x : i} {y : i} → Genᵢ (λ _ → f x → g y) t y → Genᵢ f t x → Genᵢ g t y
  genᵢAp f g = Apᵢ f g

  
