module AgdaGen.Examples.SystemF.Type where

  open import AgdaGen.Generic.Indexed.IDesc.Universe renaming (μ to μ' ; ∙ to ∘)
  open import AgdaGen.Generic.Isomorphism

  open import Level renaming (suc to sucL ; zero to zeroL)
  open import Data.Product
  open import Data.Unit
  open import Data.Sum

  open import Relation.Binary.PropositionalEquality

  infix 20 _⇒_

  data Kind : Set where
    *   : Kind
    _⇒_ : Kind → Kind → Kind

  infix 18 _,*_

  data Ctx* : Set where
    ∅    : Ctx*
    _,*_ : Ctx* → Kind → Ctx*

  infix 16 _∋*_

  data _∋*_ : Ctx* → Kind → Set where
  
    [top*] : ∀ {φ K}
             -----------
           → φ ,* K ∋* K

    [pop*] : ∀ {φ J K} → φ ∋* K
             -------------------
           → φ ,* J ∋* K

  ∋*-Desc : func 0ℓ (Ctx* × Kind) (Ctx* × Kind)
  ∋*-Desc = mk λ
    { (∅ , J)      → `σ 0 λ()
    ; (φ ,* K , J) → `σ 2 λ
         { ∘     → `Σ (J ≡ K) λ { refl → `1 }
         ; (▻ ∘) → `var (φ , J)
         } }

  from∋* : ∀ {φ J} → φ ∋* J → μ' ∋*-Desc (φ , J)
  from∋* [top*]     = ⟨ (∘ , refl , lift tt) ⟩
  from∋* ([pop*] p) = ⟨ ( ▻ ∘ , from∋* p) ⟩

  to∋* : ∀ {φ J} → μ' ∋*-Desc (φ , J) → φ ∋* J
  to∋* {∅}      ⟨ () , _ ⟩
  to∋* {φ ,* J} ⟨ ∘ , refl , lift tt ⟩ = [top*]
  to∋* {φ ,* J} ⟨ ▻ ∘ , p ⟩            = [pop*] (to∋* p)

  iso∋*₁ : ∀ {φ J} {p : φ ∋* J} → to∋* (from∋* p) ≡ p
  iso∋*₁ {p = [top*]}   = refl
  iso∋*₁ {p = [pop*] _} = cong [pop*] iso∋*₁

  iso∋*₂ : ∀ {φ J} → {p : μ' ∋*-Desc (φ , J)} → from∋* (to∋* p) ≡ p
  iso∋*₂ {∅}      {p = ⟨ () , _ ⟩}
  iso∋*₂ {φ ,* J} {p = ⟨ ∘ , refl , lift tt ⟩} = refl
  iso∋*₂ {φ ,* J} {p = ⟨ ▻ ∘ , _ ⟩}            = cong (λ x → ⟨ (▻ ∘ , x) ⟩) iso∋*₂

  ∋*≅ : ∀ {φ J} → (φ ∋* J) ≅ μ' ∋*-Desc (φ , J)
  ∋*≅ = record { from = from∋* ; to = to∋* ; iso₁ = iso∋*₁ ; iso₂ = iso∋*₂ }

  infix 14 _⊢*_

  data _⊢*_ (φ : Ctx*) : Kind → Set where
  
    `_  : ∀ {J} → φ ∋* J
          ---------------
        → φ ⊢* J

    ƛ_  : ∀ {K J} → φ ,* K ⊢* J
          ----------------------
        → φ ⊢* K ⇒ J

    _∙_ : ∀ {K J} → φ ⊢* K ⇒ J → φ ⊢* K
          ------------------------------
        → φ ⊢* J

    _⇒_ : φ ⊢* * → φ ⊢* *
          ----------------
        → φ ⊢* *

    Π   : ∀ {K} → φ ,* K ⊢* *
          --------------------
        → φ ⊢* *

    μ  : φ ,* * ⊢* *
         -----------
       → φ ⊢* *

  ⊢*-Desc : func 0ℓ (Ctx* × Kind) (Ctx* × Kind)
  ⊢*-Desc = mk (
    λ { (φ , *)     → `σ 5 λ
           { ∘           → `Σ (φ ∋* *) λ _ → `1
           ; (▻ ∘)       → `Σ Kind λ K → `var (φ , K ⇒ *) `× `var (φ , K)
           ; (▻ ▻ ∘)     → `var (φ , *) `× `var (φ , *)
           ; (▻ ▻ ▻ ∘)   → `Σ Kind λ K → `var (φ ,* K , *)
           ; (▻ ▻ ▻ ▻ ∘) → `var (φ ,* * , *)
           }
      ; (φ , K ⇒ J) → `σ 3 λ
           { ∘       → `Σ (φ ∋* K ⇒ J) λ _ → `1
           ; (▻ ∘)   → `var (φ ,* K , J)
           ; (▻ ▻ ∘) → `Σ Kind λ K' → `var (φ , K' ⇒ (K ⇒ J)) `× `var (φ , K') 
           }
      })

  from⊢* : ∀ {φ J} → φ ⊢* J → μ' ⊢*-Desc (φ , J)
  from⊢* {J = *}     (` x)            = ⟨ ∘ , (x , lift tt) ⟩
  from⊢* {J = *}     (_∙_ {K} pₗ pᵣ)  = ⟨ (▻ ∘ , K , from⊢* pₗ , from⊢* pᵣ) ⟩
  from⊢* {J = *}     (pₗ ⇒ pᵣ)        = ⟨ ((▻ ▻ ∘) , from⊢* pₗ , from⊢* pᵣ) ⟩
  from⊢* {J = *}     (Π {K} p)        = ⟨ ((▻ ▻ ▻ ∘) , K , from⊢* p) ⟩
  from⊢* {J = *}     (μ p)            = ⟨ (▻ ▻ ▻ ▻ ∘ , from⊢* p) ⟩
  from⊢* {J = K ⇒ J} (` x)            = ⟨ (∘ , (x , lift tt)) ⟩
  from⊢* {J = K ⇒ J} (ƛ p)            = ⟨ ((▻ ∘) , (from⊢* p)) ⟩
  from⊢* {J = K ⇒ J} (_∙_ {K'} pₗ pᵣ) = ⟨ (▻ ▻ ∘) , (K' , from⊢* pₗ , from⊢* pᵣ) ⟩

  to⊢* : ∀ {φ J} → μ' ⊢*-Desc (φ , J) → φ ⊢* J
  to⊢* {J = *} ⟨ ∘ , φ∋* , lift tt ⟩        = ` φ∋*
  to⊢* {J = *} ⟨ ▻ ∘ , K , pₗ , pᵣ ⟩        = to⊢* pₗ ∙ to⊢* pᵣ
  to⊢* {J = *} ⟨ ▻ ▻ ∘ , pₗ , pᵣ ⟩          = to⊢* pₗ ⇒ to⊢* pᵣ
  to⊢* {J = *} ⟨ ▻ ▻ ▻ ∘ , K , p ⟩          = Π (to⊢* p)
  to⊢* {J = *} ⟨ ▻ ▻ ▻ ▻ ∘ , p ⟩            = μ (to⊢* p)
  to⊢* {J = J ⇒ J₁} ⟨ ∘ , φ∋* , lift tt ⟩   = ` φ∋*
  to⊢* {J = J ⇒ J₁} ⟨ ▻ ∘ , p ⟩             = ƛ to⊢* p
  to⊢* {J = J ⇒ J₁} ⟨ ▻ ▻ ∘ , K , pₗ , pᵣ ⟩ = to⊢* pₗ ∙ to⊢* pᵣ

  iso⊢*₁ : ∀ {φ J} {p : φ ⊢* J} → to⊢* (from⊢* p) ≡ p
  iso⊢*₁ {J = *} {` _} = refl
  iso⊢*₁ {J = *} {_ ∙ _} = cong₂ _∙_ iso⊢*₁ iso⊢*₁
  iso⊢*₁ {J = *} {_ ⇒ _} = cong₂ _⇒_ iso⊢*₁ iso⊢*₁
  iso⊢*₁ {J = *} {Π _} = cong Π iso⊢*₁
  iso⊢*₁ {J = *} {μ _} = cong μ iso⊢*₁
  iso⊢*₁ {J = J ⇒ J₁} {` _} = refl
  iso⊢*₁ {J = J ⇒ J₁} {ƛ _} = cong ƛ_ iso⊢*₁
  iso⊢*₁ {J = J ⇒ J₁} {p_ ∙ _} = cong₂ _∙_ iso⊢*₁ iso⊢*₁

  iso⊢*₂ : ∀ {φ J} {p : μ' ⊢*-Desc (φ , J)} → from⊢* (to⊢* p) ≡ p
  iso⊢*₂ {J = *} {⟨ ∘         , φ∋** , _ ⟩}   = refl
  iso⊢*₂ {J = *} {⟨ ▻ ∘       , K , _ , _ ⟩}  = cong₂ (λ x y → ⟨ (▻ ∘) , K , x , y ⟩) iso⊢*₂ iso⊢*₂
  iso⊢*₂ {J = *} {⟨ ▻ ▻ ∘     , _ , _ ⟩}      = cong₂ (λ x y → ⟨ ▻ ▻ ∘ , x , y ⟩) iso⊢*₂ iso⊢*₂
  iso⊢*₂ {J = *} {⟨ ▻ ▻ ▻ ∘   , K  , _ ⟩}     = cong (λ x → ⟨ ((▻ ▻ ▻ ∘) , K , x ) ⟩) iso⊢*₂ 
  iso⊢*₂ {J = *} {⟨ ▻ ▻ ▻ ▻ ∘ , _ ⟩}          = cong (λ x → ⟨ ((▻ ▻ ▻ ▻ ∘) , x) ⟩) iso⊢*₂
  iso⊢*₂ {J = K ⇒ J} {⟨ ∘ , φ⊢* , _ ⟩}        = refl
  iso⊢*₂ {J = K ⇒ J} {⟨ ▻ ∘ , _ ⟩}            = cong (λ x → ⟨ ((▻ ∘) , x) ⟩) iso⊢*₂
  iso⊢*₂ {J = K ⇒ J} {⟨ ▻ ▻ ∘ , K' , _ , _ ⟩} = cong₂ (λ x y → ⟨ ((▻ ▻ ∘) , (K' , x , y)) ⟩) iso⊢*₂ iso⊢*₂

  ⊢*≅ : ∀ {φ J} → (φ ⊢* J) ≅ μ' ⊢*-Desc (φ , J)
  ⊢*≅ = record { from = from⊢* ; to = to⊢* ; iso₁ = iso⊢*₁ ; iso₂ = iso⊢*₂ }

  Ren* : Ctx* → Ctx* → Set
  Ren* φ ψ = ∀ {J} → φ ∋* J → ψ ∋* J

  lift* : ∀ {φ ψ} → Ren* φ ψ → ∀ {K} → Ren* (φ ,* K) (ψ ,* K)
  lift* ρ [top*]     = [top*]
  lift* ρ ([pop*] α) = [pop*] (ρ α)

  ren* : ∀ {φ ψ} → Ren* φ ψ → ∀ {J} → φ ⊢* J → ψ ⊢* J
  ren* ρ (` α)    = ` ρ α
  ren* ρ (ƛ B)    = ƛ ren* (lift* ρ) B
  ren* ρ (A ∙ B)  = ren* ρ A ∙ ren* ρ B
  ren* ρ (A ⇒ B)  = ren* ρ A ⇒ ren* ρ B
  ren* ρ (Π B)    = Π (ren* (lift* ρ) B)
  ren* ρ (μ B)    = μ (ren* (lift* ρ) B)

  weaken* : ∀ {φ J K} → φ ⊢* J → φ ,* K ⊢* J
  weaken* = ren* [pop*]

  Sub* : Ctx* → Ctx* → Set
  Sub* φ ψ = ∀ {J} → φ ∋* J → ψ ⊢* J

  lifts* : ∀ {φ ψ} → Sub* φ ψ → ∀ {K} → Sub* (φ ,* K) (ψ ,* K)
  lifts* σ [top*]     = ` [top*]
  lifts* σ ([pop*] α) = weaken* (σ α)

  sub* : ∀ {φ ψ} → Sub* φ ψ → ∀ {K} → φ ⊢* K → ψ ⊢* K
  sub* σ (` α)    = σ α
  sub* σ (ƛ B)    = ƛ sub* (lifts* σ) B
  sub* σ (A ∙ B)  = sub* σ A ∙ sub* σ B
  sub* σ (A ⇒ B)  = sub* σ A ⇒ sub* σ B
  sub* σ (Π B)    = Π (sub* (lifts* σ) B)
  sub* σ (μ B)    = μ (sub* (lifts* σ) B)

  extend* : ∀ {φ ψ} → Sub* φ ψ → ∀ {J} → ψ ⊢* J → Sub* (φ ,* J) ψ
  extend* σ A [top*] = A
  extend* σ A ([pop*] α) = σ α

  _[_]* : ∀ {φ J K} → φ ,* K ⊢* J → φ ⊢* K → φ ⊢* J
  B [ A ]* = sub* (extend* `_ A) B

  data _≡β_ {Γ} : ∀ {J} → Γ ⊢* J → Γ ⊢* J → Set where
    β≡β : ∀ {K J} → (B : Γ ,* J ⊢* K) → (A : Γ ⊢* J) → ((ƛ B) ∙ A) ≡β (B [ A ]*) 


    
