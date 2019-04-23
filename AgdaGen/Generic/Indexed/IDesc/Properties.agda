{-# OPTIONS --type-in-type #-}

open import AgdaGen.Data using (here ; there ; _∈_)
open import AgdaGen.Base hiding (μ)
open import AgdaGen.Combinators
open import AgdaGen.Properties.General
open import AgdaGen.Properties.Completeness
open import AgdaGen.Properties.Monotonicity
open import AgdaGen.Generic.Indexed.IDesc.Generator
open import AgdaGen.Generic.Indexed.IDesc.Universe

open import AgdaGen.Enumerate

open import Data.Nat
open import Data.List
open import Data.Product

open import Function
open import Level renaming (zero to zeroL; suc to sucL)

open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

module AgdaGen.Generic.Indexed.IDesc.Properties where

  open GMonad ⦃...⦄

  postulate
   bind-Complete :
     ∀ {I : Set} {a t b : I → Set} {x y : I}
       {g : Genᵢ a t x} {g' : a x → Genᵢ b t y}
       {tg : (i : I) → 𝔾ᵢ t i}
     → Completeᵢ g tg → ((v : a x) → Completeᵢ (g' v) tg)
     → Completeᵢ (g >>= g') tg

  -- The selector's generator is complete
  sl-gen-Complete : ∀ {n : ℕ} → Completeᵢ (Sl-gen (lift n)) Sl-gen
  sl-gen-Complete {suc n} {∙} = 1 , here
  sl-gen-Complete {suc n} {▻ x} with sl-gen-Complete {n} {x}
  ... | depth , elem  =
    ∥ᵢ-complete-left (constrᵢ-preserves-elem ((suc depth) , elem))

  ℂ : ∀ {I : Set} {t : I → Set} → ((i : I) → 𝔾ᵢ t i) → Set
  ℂ {I} g = ∀ {i : I} → Completeᵢ (g i) g

  δsubst :
    ∀ {I : Set} {δ δ' : IDesc 0ℓ I} {P : Set → Set₁}
    → δ ≡ δ' → IDescM P δ → IDescM P δ'
  δsubst refl δ = δ

  postulate
    ⟦P⟧subst :
      ∀ {I : Set} {φ φ' : func 0ℓ I I} {δ : IDesc 0ℓ I}
        {δm : IDescM ((λ S →
          Σ[ gen ∈ 𝔾 S ]
            (Complete gen gen ×
            (∀ {s : S} → Depth-Monotone gen s gen))))
          δ} {i : I}
        {m₁ : (ix : I) →
          IDescM (λ S →
            Σ[ gen ∈ 𝔾 S ]
              (Complete gen gen ×
              (∀ {s : S} → Depth-Monotone gen s gen)))
          (func.out φ ix)}
        {m₂ : (ix : I) →
          IDescM (λ S →
            Σ[ gen ∈ 𝔾 S ]
              (Complete gen gen ×
              (∀ {s : S} → Depth-Monotone gen s gen)))
          (func.out φ' ix)}
        → (φout≡δ : func.out φ i ≡ δ)
        → m₁ i ≡ δsubst (sym φout≡δ) δm
        → Completeᵢ
            (IDesc-gen {φ₁ = mk (λ _ → δ)} {φ₂ = φ'} i (mapm proj₁ δm))
            ((λ ix → IDesc-gen {φ₁ = φ'} {φ₂ = φ'}
              ix (mapm proj₁ (m₂ ix))))
        → Completeᵢ
            (IDesc-gen {φ₁ = φ} {φ₂ = φ'} i (mapm proj₁ (m₁ i)))
            ((λ ix →
              IDesc-gen {φ₁ = φ'} {φ₂ = φ'}
                ix (mapm proj₁ (m₂ ix))))

  proj₁' :
    ∀ {S : Set}
    → Σ[ gen ∈ 𝔾 S ]
        (Complete gen gen ×
        (∀ {s : S} → Depth-Monotone gen s gen))
    → 𝔾 S
  proj₁' (x , _) = x

  fix-lemma :
    ∀ {I : Set} {t : I → Set} {i : I}
      {g : (i : I) → 𝔾ᵢ t i} {n : ℕ}
    → interpretᵢ g i (g i) n ≡ interpretᵢ g i (μᵢ i) (suc n)
  fix-lemma {n = zero} = refl
  fix-lemma {n = suc n} = refl

  `var-gen-Complete :
    ∀ {I : Set} {φ₂ : func 0ℓ I I} {i i' : I}
      {m₂ : (ix : I) →
        IDescM (λ S →
          Σ[ gen ∈ 𝔾 S ]
            (Complete gen gen ×
            (∀ {s : S} → Depth-Monotone gen s gen)))
        (func.out φ₂ ix)}
    → Completeᵢ
        (IDesc-gen {φ₁ = φ₂} {φ₂ = φ₂} i' (mapm proj₁ (m₂ i')))
        (λ ix → IDesc-gen {φ₁ = φ₂} ix (mapm proj₁ (m₂ ix)))
    → Completeᵢ
        (IDesc-gen {φ₁ = mk λ _ → `var i'} {φ₂ = φ₂} i (mapm proj₁' `var~))
        λ ix → IDesc-gen {φ₁ = φ₂} ix (mapm proj₁ (m₂ ix))
  `var-gen-Complete {φ₂ = φ₂} {i' = i'} {m₂} rec {μ.⟨ x ⟩} with rec {x}
  ... | n , elem =
    constrᵢ-preserves-elem {f = μ.⟨_⟩}
      (suc n , ∈-rewr
        (fix-lemma {g = λ i → IDesc-gen {φ₁ = φ₂}
          i (mapm proj₁ (m₂ i))} {n = n}) elem)
  
  `1-gen-Complete :
    ∀ {I : Set} {φ₂ : func 0ℓ I I} {i : I}
      {m₂ : (ix : I) →
        IDescM ((λ S →
          Σ[ gen ∈ 𝔾 S ]
            (Complete gen gen ×
            (∀ {s : S} → Depth-Monotone gen s gen))))
        (func.out φ₂ ix)}
    → Completeᵢ (IDesc-gen {φ₁ = mk λ _ → `1} {φ₂ = φ₂} i (mapm proj₁' `1~))
    (λ ix → IDesc-gen {φ₁ = φ₂} ix (mapm (λ {s} → proj₁) (m₂ ix)))
  `1-gen-Complete = 1 , here

  inspectφ :
    ∀ {ℓ} {I : Set} {P : Set ℓ → Set (sucL ℓ)}
    → (φ : func ℓ I I) → (m : (i : I) → IDescM P (func.out φ i)) → (i : I)
    → Σ[ δ ∈ IDesc ℓ I ]
        Σ[ δm ∈ IDescM P δ ]
          Σ[ φout≡δ ∈ (func.out φ i ≡ δ) ] m i ≡ δsubst (sym φout≡δ) δm
  inspectφ φ m i = (func.out φ i) , m i , refl , refl

  IDesc-gen-Complete :
    ∀ {I : Set} {ix : I} {φ₁ φ₂  : func 0ℓ I I}
    → (m₁ : (i : I) →
        IDescM (λ S →
          Σ[ gen ∈ 𝔾 S ]
            (Complete gen gen ×
            (∀ {s : S} → Depth-Monotone gen s gen)))
          (func.out φ₁ i))
    → (m₂ : (i : I) →
        IDescM (λ S →
          Σ[ gen ∈ 𝔾 S ]
            (Complete gen gen ×
            (∀ {s : S} → Depth-Monotone gen s gen)))
        (func.out φ₂ i))
    → Completeᵢ
        (IDesc-gen {φ₁ = φ₁} {φ₂ = φ₂} ix (mapm proj₁ (m₁ ix)))
        (λ i → (IDesc-gen {φ₁ = φ₂} {φ₂ = φ₂} i (mapm proj₁ (m₂ i))))
  IDesc-gen-Complete {I} {ix} {φ₁} {φ₂} m₁ m₂ {x} =
    case inspectφ φ₁ m₁ ix of
      λ { (`var i   , `var~       , φ≡`var , m≡`var~) →
            ⟦P⟧subst {φ = φ₁} {φ' = φ₂}
              {δ = `var i} {δm = `var~} {m₁ = m₁}
              φ≡`var m≡`var~
              (`var-gen-Complete {!!})
        ; (`1       , `1~         , φ≡`1   , m≡`1~  ) →
            ⟦P⟧subst {φ = φ₁} {φ' = φ₂}
              {δ = `1} {δm = `1~} {m₁ = m₁}
              φ≡`1 m≡`1~
              (`1-gen-Complete {m₂ = m₂})
        ; (δₗ `× δᵣ , (mₗ `×~ mᵣ) , φ≡`×   , m≡`×~  ) → {!!}
        ; (`σ n T   , `σ~ x       , φ≡`σ   , m≡`σ~  ) → {!!}
        ; (`Σ S T   , `Σ~ x x₁    , φ≡`Σ   , m≡`Σ~  ) → {!!}
        }
