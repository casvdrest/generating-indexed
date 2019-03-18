{-# OPTIONS --type-in-type #-}

open import src.Gen.Indexed.Signature
open import src.Gen.Regular.Generic
open import src.Gen.Regular.Isomorphism 
open import src.Gen.Base
open import src.Gen.Indexed.PiGen

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Data.List
open import Data.Vec hiding (_>>=_)

open import Data.Fin hiding (toℕ)

open import Category.Functor
open import Category.Monad

open import Codata.Musical.Notation

open import Function

module src.Gen.Indexed.Generic where

  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawMonad ⦃...⦄ using (_>>_; _>>=_; return; pure)

  Gen-Σ : ∀ {i : Set} {P : i → Set} → 𝔾 i → 𝔾ᵢ P → 𝔾 (Σ[ x ∈ i ] P x)
  Gen-Σ g₁ g₂ = (` g₁) >>= λ x → (` g₂ x) >>= λ y → Pure (x , y)

  {-# TERMINATING #-}
  deriveGenᵢ :
    ∀ {i : Set} {Σ : Sig i}
    → ((x : i) → RegInfo (λ op → 𝔾 op × Π𝔾 op) (Sig.Op Σ x))
    → ((x : i) → (op : Fix (Sig.Op Σ x)) → RegInfo (λ ar → 𝔾 ar × Π𝔾 ar) (Sig.Ar Σ op))
    → 𝔾ᵢ (⟦ Σ ⟧ₛ (Fixₛ Σ))
  deriveGenᵢ {i} {Op ◃ Ar ∣ Ty} sig₁ sig₂ x =
    Gen-Σ (⦇ In (` deriveGen (map-reginfo proj₁ (sig₁ x))) ⦈)
      λ { (In op) → ⦇ (λ { π (In y) → π y })
        (` derivePiGen (map-reginfo proj₂ (sig₂ x (In op)))
           λ ar → ⦇ Inₛ (μ[ deriveGenᵢ sig₁ sig₂ , Ty (In ar) ]) ⦈
        )
      ⦈} 
