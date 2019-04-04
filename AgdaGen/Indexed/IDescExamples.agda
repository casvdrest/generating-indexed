open import AgdaGen.Base hiding (⟨_⟩; μ)
open import AgdaGen.Combinators
open import AgdaGen.Indexed.IDesc

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

module AgdaGen.Indexed.IDescExamples where

  BoolD : func zeroL ⊤ ⊤
  BoolD = func.mk λ { tt → 
    `σ 2 (λ {  ∙    → `1 
            ; (▻ ∙) → `1
            }) }

  Bool' : Set 
  Bool' = μ BoolD tt

  boolGen : 𝔾 Bool'
  boolGen = ⦇ ⟨_⟩ (`
             ( ⦇ (∙   , lift tt) ⦈
             ∥ ⦇ (▻ ∙ , lift tt) ⦈ )
            )⦈
  
  fromBool : Bool → Bool'
  fromBool false = ⟨ (∙   , (lift tt)) ⟩
  fromBool true  = ⟨ (▻ ∙ , (lift tt)) ⟩

  toBool : Bool' → Bool
  toBool ⟨ ∙      , lift tt ⟩ = false
  toBool ⟨ ▻ ∙    , lift tt ⟩ = true

  Bool-iso₁ : ∀ {b : Bool} → toBool (fromBool b) ≡ b
  Bool-iso₁ {false} = refl
  Bool-iso₁ {true } = refl

  Bool-iso₂ : ∀ {b : Bool'} → fromBool (toBool b) ≡ b
  Bool-iso₂ {⟨ ∙      , lift tt ⟩} = refl
  Bool-iso₂ {⟨ ▻ ∙    , lift tt ⟩} = refl
  
  NatD : func zeroL ⊤ ⊤
  NatD = func.mk λ { tt →
    `σ 2 (λ {  ∙     → `1
            ; (▻ ∙ ) → `var tt
            })}

  Nat : Set
  Nat = μ NatD tt

  z : Nat 
  z = ⟨ ∙ , lift tt ⟩

  s : Nat → Nat
  s n = ⟨ (▻ ∙ , n) ⟩

  toNat : ℕ → Nat
  toNat zero    = z
  toNat (suc n) = s (toNat n)

  fromNat : Nat → ℕ
  fromNat ⟨ ∙   , lift tt ⟩ = 0
  fromNat ⟨ ▻ ∙ , rec     ⟩ = suc (fromNat rec)
  
  Nat-iso₁ : ∀ {n : ℕ} → fromNat (toNat n) ≡ n
  Nat-iso₁ {zero } = refl
  Nat-iso₁ {suc n} = cong suc Nat-iso₁

  Nat-iso₂ : ∀ {n : Nat} → toNat (fromNat n) ≡ n
  Nat-iso₂ {⟨ ∙   , snd ⟩} = refl
  Nat-iso₂ {⟨ ▻ ∙ , snd ⟩} = cong (λ x → ⟨ ▻ ∙ , x ⟩) Nat-iso₂

  OptionD : (a : Set) → func zeroL ⊤ ⊤
  OptionD a = func.mk λ { tt →
    `σ 2 λ {  ∙    → `1
           ; (▻ ∙) → `Σ a λ _ → `1
           } }

  Option : Set → Set
  Option a = μ (OptionD a) tt

  nothing' : ∀ {a : Set} → Option a
  nothing' = ⟨ ∙ , lift tt ⟩

  just' : ∀ {a : Set} → a → Option a
  just' x = ⟨ ▻ ∙ , x , lift tt ⟩

  fromMaybe : ∀ {a : Set} → Maybe a → Option a
  fromMaybe (just x) = just' x
  fromMaybe nothing  = nothing'

  toMaybe : ∀ {a : Set} → Option a → Maybe a
  toMaybe ⟨ ∙       , lift tt ⟩ = nothing
  toMaybe ⟨ ▻ ∙ , x , lift tt ⟩ = just x

  Maybe-iso₁ : ∀ {a : Set} {m : Maybe a} → toMaybe (fromMaybe m) ≡ m
  Maybe-iso₁ {_} {just x } = refl
  Maybe-iso₁ {_} {nothing} = refl

  Maybe-iso₂ : ∀ {a : Set} {o : Option a} → fromMaybe (toMaybe o) ≡ o
  Maybe-iso₂ {_} {⟨ ∙       , lift tt ⟩} = refl
  Maybe-iso₂ {_} {⟨ ▻ ∙ , x , lift tt ⟩} = refl

  FinD : func zeroL ℕ ℕ
  FinD = func.mk
    λ { zero     → `σ 0 λ ()
      ; (suc ix) → `σ 2
        λ {  ∙    → `1
          ; (▻ ∙) → `var ix
          } }

  Fin' : ℕ →  Set
  Fin' n = μ FinD n

  fz : ∀ {n : ℕ} → Fin' (suc n)
  fz = ⟨ ∙ , lift tt ⟩

  fs : ∀ {n : ℕ} → Fin' n → Fin' (suc n)
  fs n = ⟨ (▻ ∙ , n) ⟩

  toFin' : ∀ {n : ℕ} → Fin n → Fin' n
  toFin' zero     = fz
  toFin' (suc fn) = fs (toFin' fn)

  fromFin' : ∀ {n : ℕ} → Fin' n → Fin n
  fromFin' {suc n} ⟨ ∙   , lift tt ⟩ = zero
  fromFin' {suc n} ⟨ ▻ ∙ , rec     ⟩ = suc (fromFin' rec)

  Fin'-iso₁ : ∀ {n : ℕ} {fn : Fin n} → fromFin' (toFin' fn) ≡ fn
  Fin'-iso₁ {.(suc _)} {zero  } = refl
  Fin'-iso₁ {.(suc _)} {suc fn} = cong suc Fin'-iso₁


  Fin'-iso₂ : ∀ {n : ℕ} {fn : Fin' n} → toFin' (fromFin' fn) ≡ fn
  Fin'-iso₂ {suc n} {⟨ ∙   , lift tt ⟩} = refl
  Fin'-iso₂ {suc n} {⟨ ▻ ∙ , rec     ⟩} =
    cong (λ x → ⟨ (▻ ∙ , x) ⟩) Fin'-iso₂

  data STree : ℕ → Set where
    Leaf : STree 0
    Node : ∀ {n m} → STree n → STree m → STree (suc (n + m))


  STreeD : func zeroL ℕ ℕ
  STreeD = func.mk
    λ { zero    → `σ 1 λ { ∙ → `1 }
      ; (suc n) → `σ 1 λ { ∙ → `Σ (ℕ × ℕ) λ { (l , r ) →
          `Σ (l + r ≡ n) λ { refl → `var l `× `var r }} }
      }

  STree' : ℕ → Set
  STree' n = μ STreeD n

  size : ∀ {n : ℕ} → STree n → ℕ
  size {n} _ = n
  
  fromSTree : ∀ {n : ℕ} → STree n → STree' n
  fromSTree Leaf                 = ⟨ (∙ , lift tt) ⟩
  fromSTree {suc n} (Node nₗ nᵣ) =
    ⟨ (∙ , (size nₗ , size nᵣ) , refl , fromSTree nₗ , fromSTree nᵣ) ⟩

  toSTree : ∀ {n : ℕ} → STree' n → STree n
  toSTree {zero} ⟨ fst , snd ⟩                                = Leaf
  toSTree {suc .(sl + sr)} ⟨ ∙ , (sl , sr) , refl , nₗ , nᵣ ⟩ =
    Node (toSTree nₗ) (toSTree nᵣ)

  STree-iso₁ : ∀ {n : ℕ} {t : STree n} → toSTree (fromSTree t) ≡ t
  STree-iso₁ {zero } {Leaf}       = refl
  STree-iso₁ {suc n} {Node nₗ nᵣ} =
    cong₂ Node STree-iso₁ STree-iso₁

  STree-iso₂ : ∀ {n : ℕ} {t : STree' n} → fromSTree (toSTree t) ≡ t
  STree-iso₂ {zero} {⟨ ∙ , snd ⟩}                                  = refl
  STree-iso₂ {suc .(sl + sr)} {⟨ ∙ , (sl , sr) , refl , nₗ , nᵣ ⟩} =
    cong₂ (λ r₁ r₂ → ⟨ ∙ , (sl , sr) , refl , (r₁ , r₂) ⟩) STree-iso₂ STree-iso₂

  data _∈_ {a : Set} (x : a) : List a →  Set where
    here  : ∀ {xs : List a} → x ∈ (x ∷ xs)
    there : ∀ {y : a} {xs : List a} → x ∈ xs → x ∈ (y ∷ xs)

  ∈D : ∀ {a : Set} → a → func zeroL (List a) (List a)
  ∈D {a} v = func.mk
    λ { []       → `σ 0 λ ()
      ; (x ∷ xs) → `σ 2
           λ {  ∙    → `Σ (x ≡ v) λ { refl → `1 }
             ; (▻ ∙) → `var xs
             }
      }

  _∈'_ : ∀ {a : Set} → a → List a → Set
  x ∈' xs = μ (∈D x) xs

  from∈ : ∀ {a : Set} {x : a} {xs : List a} → x ∈ xs → x ∈' xs
  from∈ here         = ⟨ ∙   , refl , lift tt ⟩
  from∈ (there elem) = ⟨ ▻ ∙ , from∈ elem     ⟩

  to∈ : ∀ {a : Set} {x : a} {xs : List a} → x ∈' xs → x ∈ xs
  to∈ {xs = x ∷ xs} ⟨ ∙   , refl , lift tt ⟩ = here
  to∈ {xs = x ∷ xs} ⟨ ▻ ∙        , rec     ⟩ = there (to∈ rec)

  ∈-iso₁ : ∀ {a : Set} {x : a} {xs : List a} {elem : x ∈ xs} → to∈ (from∈ elem) ≡ elem
  ∈-iso₁ {elem = here}       = refl
  ∈-iso₁ {elem = there elem} = cong there ∈-iso₁

  ∈-iso₂ : ∀ {a : Set} {x : a} {xs : List a} {elem : x ∈' xs} → from∈ (to∈ elem) ≡ elem
  ∈-iso₂ {xs = x ∷ xs} {⟨ ∙   , refl , lift tt ⟩} = refl
  ∈-iso₂ {xs = x ∷ xs} {⟨ ▻ ∙        , _       ⟩} =
    cong (λ v → ⟨ ((▻ ∙) , v) ⟩) ∈-iso₂

  data Ty : Set where
    `τ   : Ty
    _`→_ : Ty → Ty → Ty

  Id : Set
  Id = ℕ

  data Ctx : Set where
    ∅     : Ctx
    _,_∶_ : Ctx → Id → Ty → Ctx

  data [_↦_]_ (α : Id) (τ : Ty) : Ctx → Set where

    TOP : ∀ {Γ : Ctx}
        -----------------------
        → [ α ↦ τ ] (Γ , α ∶ τ)

    POP : ∀ {Γ : Ctx} {β : Id} {σ : Ty}
        → [ α ↦ τ ] Γ
        -------------------------------
        → [ α ↦ τ ] (Γ , β ∶ σ)

  ↦D : Id → Ty → func zeroL Ctx Ctx
  ↦D α τ = func.mk
    λ { ∅             → `σ 0 λ ()
      ; (Γ , β ∶ σ)   → `σ 2
          λ {  ∙    → `Σ (α ≡ β) λ { refl → `Σ (τ ≡ σ) λ { refl → `1 } }
            ; (▻ ∙) → `var Γ
            } }

  [_↦_]'_ : Id → Ty → Ctx → Set
  [ α ↦ τ ]' Γ = μ (↦D α τ) Γ

  from↦ : ∀ {α : Id} {τ : Ty} {Γ : Ctx} → [ α ↦ τ ] Γ → [ α ↦ τ ]' Γ
  from↦ TOP      = ⟨ ∙   , refl , refl , lift tt ⟩
  from↦ (POP jd) = ⟨ ▻ ∙ , from↦ jd              ⟩

  to↦ : ∀ {α : Id} {τ : Ty} {Γ : Ctx} → ([ α ↦ τ ]' Γ → [ α ↦ τ ] Γ)
  to↦ {Γ = Γ , β ∶ σ} ⟨ ∙ , refl , refl , lift tt ⟩ = TOP
  to↦ {Γ = Γ , β ∶ σ} ⟨ ▻ ∙ , rec                 ⟩ = POP (to↦ rec)

  ↦-iso₁ : ∀ {α : Id} {τ : Ty} {Γ : Ctx} {jd : [ α ↦ τ ] Γ} → to↦ (from↦ jd) ≡ jd
  ↦-iso₁ {jd = TOP}    = refl
  ↦-iso₁ {jd = POP jd} = cong POP ↦-iso₁
  
  ↦-iso₂ : ∀ {α : Id} {τ : Ty} {Γ : Ctx} {jd : [ α ↦ τ ]' Γ} → from↦ (to↦ jd) ≡ jd
  ↦-iso₂ {Γ = Γ , β ∶ τ} {⟨ ∙ , refl , refl , lift tt ⟩} = refl
  ↦-iso₂ {Γ = Γ , β ∶ τ} {⟨ ▻ ∙ , _                   ⟩} =
    cong (λ x → ⟨ ((▻ ∙) , x) ⟩) ↦-iso₂

  data Tm : Set where
    $_  : Id → Tm
    Λ_⇒_ : Id → Tm → Tm
    _⊚_  : Tm → Tm → Tm

  data _⊢_∶_ (Γ : Ctx) : Tm → Ty → Set where

    VAR : ∀ {α τ} → [ α ↦ τ ] Γ
          ---------------------
        → Γ ⊢ $ α ∶ τ

    
    ABS : ∀ {α τ σ t} → (Γ , α ∶ σ) ⊢ t ∶ τ
          ----------------------------------
        → Γ ⊢ Λ α ⇒ t ∶ (σ `→ τ)

    
    APP : ∀ {t₁ t₂ τ σ} → Γ ⊢ t₁ ∶ (σ `→ τ) → Γ ⊢ t₂ ∶ σ
          ------------------------------------------------
        → Γ ⊢ t₁ ⊚ t₂ ∶ τ
 
  ⊢D : func zeroL (Ctx × Tm × Ty) (Ctx × Tm × Ty)
  ⊢D = func.mk
    λ { (Γ , ($ α) , τ)     → `σ 1
          (λ { ∙ → `Σ ([ α ↦ τ ] Γ) λ _ → `1 })
      ; (Γ , (Λ α ⇒ t) , `τ      ) → `σ 0 λ ()
      ; (Γ , (Λ α ⇒ t) , (σ `→ τ)) → `σ 1
          (λ { ∙ → `var ((Γ , α ∶ σ) , t , τ) } )
      ; (Γ , (t₁ ⊚ t₂) , τ)  → `σ 1
          (λ { ∙ → `Σ Ty λ σ →
               `var (Γ , t₁ , σ `→ τ) `× `var (Γ , t₂ , σ) })
      }

  _⊢'_∶_ : Ctx → Tm → Ty → Set
  Γ ⊢' t ∶ τ = μ ⊢D (Γ , t , τ)
  
  ⊢→Ty : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} → Γ ⊢ t ∶ τ → Ty
  ⊢→Ty {τ = τ} _ = τ

  from⊢ : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} → Γ ⊢ t ∶ τ → Γ ⊢' t ∶ τ
  from⊢ (VAR x)       = ⟨ (∙ , x , lift tt) ⟩
  from⊢ (ABS jd)      = ⟨ (∙ , from⊢ jd) ⟩
  from⊢ (APP jd₁ jd₂) = ⟨ (∙ , ⊢→Ty jd₂ , from⊢ jd₁ , from⊢ jd₂) ⟩

  to⊢ : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} → Γ ⊢' t ∶ τ → Γ ⊢ t ∶ τ
  to⊢ {t = $ α    } {τ      } ⟨ ∙ , var , lift tt ⟩ = VAR var
  to⊢ {t = Λ α ⇒ t} {τ `→ τ₁} ⟨ ∙ , rec           ⟩ = ABS (to⊢ rec)
  to⊢ {t = t ⊚ t₁ } {τ      } ⟨ ∙ , _ , jd₁ , jd₂ ⟩ = APP (to⊢ jd₁) (to⊢ jd₂)

  ⊢-iso₁ : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} {jd : Γ ⊢ t ∶ τ} → to⊢ (from⊢ jd) ≡ jd
  ⊢-iso₁ {jd = VAR _  } = refl
  ⊢-iso₁ {jd = ABS _  } = cong ABS ⊢-iso₁
  ⊢-iso₁ {jd = APP _ _} = cong₂ APP ⊢-iso₁ ⊢-iso₁

  ⊢-iso₂ : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} {jd : Γ ⊢' t ∶ τ} → from⊢ (to⊢ jd) ≡ jd
  ⊢-iso₂ {t = $ α    } {τ      } {⟨ ∙ , _ , lift tt ⟩  } = refl
  ⊢-iso₂ {t = Λ α ⇒ t} {τ `→ τ₁} {⟨ ∙ , jd ⟩           } =
    cong (λ x → ⟨ (∙ , x) ⟩) ⊢-iso₂
  ⊢-iso₂ {t = t ⊚ t₁ } {τ      } {⟨ ∙ , σ , jd₁ , jd₂ ⟩} =
    cong₂ (λ x y → ⟨ (∙ , σ , (x , y)) ⟩) ⊢-iso₂ ⊢-iso₂

