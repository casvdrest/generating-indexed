{-# OPTIONS --type-in-type #-}

open import Model.Base hiding (μ)
open import Model.Combinators
open import Model.Enumerate hiding (⟨_⟩)
open import Model.Generic.Isomorphism
open import Model.Generic.Indexed.IDesc.Universe
open import Model.Generic.Indexed.IDesc.Generator

open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Nat
open import Data.Unit
open import Data.Fin hiding (lift; _+_)
open import Data.List hiding (fromMaybe)
open import Data.Maybe hiding (fromMaybe)

open import Level 
    renaming ( zero to zeroL 
             ; suc to sucL ) 

open import Relation.Binary.PropositionalEquality

module Model.Generic.Indexed.IDesc.STree where

  open GApplicative ⦃...⦄
  open GAlternative ⦃...⦄
  open GMonad       ⦃...⦄

  data STree : ℕ → Set where
    Leaf : STree 0
    Node : ∀ {n m} → STree n → STree m → STree (suc (n + m))


  STreeD : func zeroL ℕ ℕ
  STreeD = func.mk
    λ { zero    → `σ 1 λ { ∙ → `1 }
      ; (suc n) → `σ 1 λ { ∙ → `Σ (Σ[ t ∈ ℕ × ℕ ] proj₁ t + proj₂ t ≡ n) λ { ((n , m) , refl) → `var n `× `var m } }
      }

  STree' : ℕ → Set
  STree' n = μ STreeD n

  size : ∀ {n : ℕ} → STree n → ℕ
  size {n} _ = n
  
  fromSTree : ∀ {n : ℕ} → STree n → STree' n
  fromSTree Leaf                 = ⟨ (∙ , lift tt) ⟩
  fromSTree {suc n} (Node nₗ nᵣ) = ⟨ ∙ , (((size nₗ) , (size nᵣ)) , refl) , (fromSTree nₗ) , (fromSTree nᵣ) ⟩

  toSTree : ∀ {n : ℕ} → STree' n → STree n
  toSTree {zero} ⟨ fst , snd ⟩                                = Leaf
  toSTree {suc .(sl + sr)} ⟨ ∙ , ((sl , sr) , refl) , l , r ⟩ =
    Node (toSTree l) (toSTree r)

  STree-iso₁ : ∀ {n : ℕ} {t : STree n} → toSTree (fromSTree t) ≡ t
  STree-iso₁ {zero } {Leaf}       = refl
  STree-iso₁ {suc n} {Node nₗ nᵣ} =
    cong₂ Node STree-iso₁ STree-iso₁

  STree-iso₂ : ∀ {n : ℕ} {t : STree' n} → fromSTree (toSTree t) ≡ t
  STree-iso₂ {zero} {⟨ ∙ , snd ⟩}                                  = refl
  STree-iso₂ {suc .(sl + sr)} {⟨ ∙ , ((sl , sr) , refl) , l , r ⟩} =
    cong₂ (λ l r → ⟨ (∙ , ((sl , sr) , refl) , l , r) ⟩) STree-iso₂ STree-iso₂

  instance
    STree-≅IDesc : ≅IDesc STree
    STree-≅IDesc = record { W = STreeD , ≅-transitive (≅-symmetric ≅lift) (record { from = fromSTree ; to = toSTree ; iso₁ = STree-iso₁ ; iso₂ = STree-iso₂ }) }

  genSTree : ((n : ℕ) → IDescM 𝔾 (func.out STreeD n)) → (n : ℕ) → 𝔾ᵢ (λ x → Lift zeroL (STree x)) n
  genSTree m n = IDesc-isoGen n m

  +-inv : (n : ℕ) → 𝔾 (Σ[ t ∈ ℕ × ℕ ] proj₁ t + proj₂ t ≡ n)
  +-inv zero    = ⦇ ((0 , 0) , refl) ⦈
  +-inv (suc n) = pure ((0 , suc n) , refl) ∥ (
    do (n' , m') , refl ← ` (+-inv n)
       pure ((suc n' , m') , refl))

  STreeM : (n : ℕ) → IDescM 𝔾 (func.out STreeD n)
  STreeM zero =
    `σ~ (λ { ∙ → `1~
           })
  STreeM (suc n) =
    `σ~ (λ { ∙ → `Σ~ (+-inv n) λ { ((n , m) , refl) → `var~ `×~ `var~ }
           })

  prop : ⟨_⟩ᵢ {f = λ n → Lift zeroL (STree n)} (genSTree STreeM) 3 5 ≡
    lift (Node Leaf (Node Leaf (Node Leaf Leaf))) ∷
    lift (Node Leaf (Node (Node Leaf Leaf) Leaf)) ∷
    lift (Node (Node Leaf Leaf) (Node Leaf Leaf)) ∷
    lift (Node (Node Leaf (Node Leaf Leaf)) Leaf) ∷
    lift (Node (Node (Node Leaf Leaf) Leaf) Leaf) ∷ []
  prop = refl

  data STree₂ : ℕ → Set where
    Leaf₂ : STree₂ 1
    Node₂ : ∀ {n m : ℕ} → STree₂ n → STree₂ m → STree₂ (n + m)

  STree₂D : func 0ℓ ℕ ℕ
  STree₂D = func.mk
   λ n → `σ 2 λ
     { ∙     → `Σ (n ≡ 1) λ { refl → `1 }
     ; (▻ ∙) → `Σ (Σ (ℕ × ℕ) λ { (n' , m') → n ≡ n' + m' }) λ { ((n' , m') , refl) → `var n' `× `var m' }
     }

  size₂ : ∀ {n : ℕ} → STree₂ n → ℕ
  size₂ {n} _ = n

  fromSTree₂ : ∀ {n : ℕ} → STree₂ n → μ STree₂D n
  fromSTree₂ {.1} Leaf₂ = ⟨ ∙ , refl , lift tt ⟩
  fromSTree₂ {n} (Node₂ t₁ t₂) =
    ⟨ ((▻ ∙) , ((size₂ t₁ , size₂ t₂) , refl) , fromSTree₂ t₁ , fromSTree₂ t₂) ⟩

  toSTree₂ : ∀ {n : ℕ} → μ STree₂D n → STree₂ n
  toSTree₂ {.1} ⟨ ∙ , refl , lift tt ⟩ = Leaf₂
  toSTree₂ {.(n' + m')} ⟨ ▻ ∙ , ((n' , m') , refl) , t₁ , t₂ ⟩ =
    Node₂ (toSTree₂ t₁)  (toSTree₂ t₂)

  STree₂-iso₁ : ∀ {n : ℕ} {t : STree₂ n} → toSTree₂ (fromSTree₂ t) ≡ t
  STree₂-iso₁ {.1} {Leaf₂} = refl
  STree₂-iso₁ {n} {Node₂ t t₁} =
    cong₂ Node₂ STree₂-iso₁ STree₂-iso₁

  STree₂-iso₂ : ∀ {n : ℕ} {t : μ STree₂D n} → fromSTree₂ (toSTree₂ t) ≡ t
  STree₂-iso₂ {.1} {⟨ ∙ , refl , lift tt ⟩} = refl
  STree₂-iso₂ {.(n' + m')} {⟨ ▻ ∙ , ((n' , m') , refl) , fst , snd ⟩} =
    cong₂ (λ x y → ⟨ ((▻ ∙) , ((n' , m') , refl) , x , y) ⟩) STree₂-iso₂ STree₂-iso₂
