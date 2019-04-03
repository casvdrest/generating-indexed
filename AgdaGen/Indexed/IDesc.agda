module AgdaGen.Indexed.IDesc where

  open import Level 
    renaming ( zero to zeroL 
             ; suc to sucL )

  open import Data.Unit 
  open import Data.Nat hiding (_⊔_)
  open import Data.Fin hiding (lift; _+_)
  open import Data.Product

  open import Relation.Binary.PropositionalEquality

  infixr 5 _⇒_

  Pow : ∀{ℓ} → Set ℓ → Set (sucL ℓ)
  Pow {ℓ} I = I → Set ℓ

  _⇒_ : ∀{ℓ}{I : Set ℓ} → (P Q : Pow I) → Set ℓ
  P ⇒ Q = {i : _} → P i → Q i

  data _⁻¹_ {ℓ : Level}{A B : Set ℓ}(f : A → B) : Pow B where
    inv : (a : A) → f ⁻¹ (f a)

  T : ∀{ℓ}{I : Set ℓ} → I → Set ℓ
  T {ℓ} _ =  Lift ℓ ⊤

  infixr 30 _`×_

  data IDesc {k : Level}(ℓ : Level)(I : Set k) : Set (k ⊔ (sucL ℓ)) where
    `var : (i : I) → IDesc ℓ I
    `1 : IDesc ℓ I
    _`×_ : (A B : IDesc ℓ I) → IDesc ℓ I
    `σ : (n : ℕ)(T : Fin n → IDesc ℓ I) → IDesc ℓ I
    `Σ : (S : Set ℓ)(T : S → IDesc ℓ I) → IDesc ℓ I
    `Π : (S : Set ℓ)(T : S → IDesc ℓ I) → IDesc ℓ I

  ⟦_⟧ : ∀{k ℓ}{I : Set k} → IDesc ℓ I → (I → Set ℓ) → Set ℓ
  ⟦ `var i ⟧ X = X i
  ⟦_⟧ {ℓ = ℓ} `1  X = Lift ℓ ⊤
  ⟦ A `× B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
  ⟦ `σ n T ⟧ X = Σ[ k ∈ Fin n ] ⟦ T k ⟧ X
  ⟦ `Σ S T ⟧ X = Σ[ s ∈ S ] ⟦ T s ⟧ X
  ⟦ `Π S T ⟧ X = (s : S) → ⟦ T s ⟧ X

  ⟦_⟧map : ∀{ℓ I X Y} → (D : IDesc ℓ I) → (f : X ⇒ Y) →  ⟦ D ⟧ X → ⟦ D ⟧ Y
  ⟦_⟧map (`var i) f xs = f xs
  ⟦_⟧map `1 f (lift tt) = lift tt
  ⟦_⟧map (A `× B) f (a , b) = ⟦ A ⟧map f a , ⟦ B ⟧map f b
  ⟦_⟧map (`σ n T) f (k , xs) = k , ⟦ T k ⟧map f xs
  ⟦_⟧map (`Σ S T) f (s , xs) = s , ⟦ T s ⟧map f xs
  ⟦_⟧map (`Π S T) f xs = λ s → ⟦ T s ⟧map f (xs s)

  record func {k : Level}(ℓ : Level)(I J : Set k) : Set (k ⊔ (sucL ℓ)) where
    constructor mk
    field
      out : J → IDesc ℓ I

  ⟦_⟧func : ∀{k ℓ}{I J : Set k} → func ℓ I J → (I → Set ℓ) → (J → Set ℓ)
  ⟦ D ⟧func X j = ⟦ func.out D j ⟧ X 

  ⟦_⟧fmap : ∀{ℓ I J X Y} → (D : func ℓ I J) → (f : X ⇒ Y) →  ⟦ D ⟧func X ⇒ ⟦ D ⟧func Y
  ⟦ D ⟧fmap f {j} xs = ⟦ func.out D j ⟧map f xs

  data μ {ℓ} {I : Set} (D : func ℓ I I)(i : I) : Set ℓ where
    ⟨_⟩ : ⟦ D ⟧func (μ D) i → μ D i

  BoolD : func zeroL ⊤ ⊤
  BoolD = func.mk λ { tt → 
    `σ 2 (λ { zero → `1 
            ; (suc zero) → `1 
            ; (suc (suc ())) }) }

  Bool : Set 
  Bool = μ BoolD tt

  true : Bool
  true = ⟨ zero , lift tt ⟩

  false : Bool
  false = ⟨ suc zero ,  lift tt ⟩

  NatD : func zeroL ⊤ ⊤
  NatD = func.mk λ { tt →
    `σ 2 (λ { zero       → `1
            ; (suc zero) → `var tt
            ; (suc (suc ()))
            })}

  Nat : Set
  Nat = μ NatD tt

  z : Nat 
  z = ⟨ zero , lift tt ⟩

  s : Nat → Nat
  s n = ⟨ ((suc zero) , n) ⟩

  toNat : ℕ → Nat
  toNat zero    = z
  toNat (suc n) = s (toNat n)

  fromNat : Nat → ℕ
  fromNat ⟨ zero , snd ⟩ = 0
  fromNat ⟨ suc zero , snd ⟩ = suc (fromNat snd)
  fromNat ⟨ suc (suc ()) , snd ⟩

  Nat-iso₁ : ∀ {n : ℕ} → fromNat (toNat n) ≡ n
  Nat-iso₁ {zero} = refl
  Nat-iso₁ {suc n} = cong suc Nat-iso₁

  Nat-iso₂ : ∀ {n : Nat} → toNat (fromNat n) ≡ n
  Nat-iso₂ {⟨ zero , snd ⟩} = refl
  Nat-iso₂ {⟨ suc zero , snd ⟩} = cong (λ x → ⟨ (suc zero , x) ⟩) Nat-iso₂
  Nat-iso₂ {⟨ suc (suc ()) , snd ⟩}

  OptionD : (a : Set) → func zeroL ⊤ ⊤
  OptionD a = func.mk λ { tt →
    `σ 2 λ { zero       → `1
           ; (suc zero) → `Σ a λ _ → `1
           ; (suc (suc ()))} }

  Option : Set → Set
  Option a = μ (OptionD a) tt

  nothing : ∀ {a : Set} → Option a
  nothing = ⟨ zero , lift tt ⟩

  just : ∀ {a : Set} → a → Option a
  just x = ⟨ suc zero , x , lift tt ⟩

  FinD : func zeroL ℕ ℕ
  FinD = func.mk
    λ { zero     → `σ 0 λ ()
      ; (suc ix) → `σ 2
        λ { zero       → `1
          ; (suc zero) → `var ix
          ; (suc (suc ()))
          } }

  Fin' : ℕ →  Set
  Fin' n = μ FinD n

  fz : ∀ {n : ℕ} → Fin' (suc n)
  fz = ⟨ zero , lift tt ⟩

  fs : ∀ {n : ℕ} → Fin' n → Fin' (suc n)
  fs n = ⟨ (suc zero , n) ⟩

  toFin' : ∀ {n : ℕ} → Fin n → Fin' n
  toFin' zero = fz
  toFin' (suc fn) = fs (toFin' fn)

  fromFin' : ∀ {n : ℕ} → Fin' n → Fin n
  fromFin' {zero} ⟨ () , snd ⟩
  fromFin' {suc n} ⟨ zero , snd ⟩ = zero
  fromFin' {suc n} ⟨ suc zero , snd ⟩ = suc (fromFin' snd)
  fromFin' {suc n} ⟨ suc (suc ()) , snd ⟩

  Fin'-iso₁ : ∀ {n : ℕ} {fn : Fin n} → fromFin' (toFin' fn) ≡ fn
  Fin'-iso₁ {.(suc _)} {zero} = refl
  Fin'-iso₁ {.(suc _)} {suc fn} = cong suc Fin'-iso₁

  Fin'-iso₂ : ∀ {n : ℕ} {fn : Fin' n} → toFin' (fromFin' fn) ≡ fn
  Fin'-iso₂ {zero} {⟨ () , snd ⟩}
  Fin'-iso₂ {suc n} {⟨ zero , snd ⟩} = refl
  Fin'-iso₂ {suc n} {⟨ suc zero , snd ⟩} =
    cong (λ x → ⟨ (suc zero , x) ⟩) Fin'-iso₂
  Fin'-iso₂ {suc n} {⟨ suc (suc ()) , snd ⟩}

  data STree : ℕ → Set where
    Leaf : STree 0
    Node : ∀ {n m} → STree n → STree m → STree (suc (n + m))
  
  STreeD : func zeroL ℕ ℕ
  STreeD = func.mk
    λ { zero    → `σ 1
           λ { zero → `1
             ; (suc ()) }
      ; (suc n) → `σ 1
           λ { zero → `Σ (ℕ × ℕ) λ { (l , r ) →
                      `Σ (l + r ≡ n) λ { refl →
                         `var l `× `var r }} 
             ; (suc ()) }
      }

  STree' : ℕ → Set
  STree' n = μ STreeD n

  size : ∀ {n : ℕ} → STree n → ℕ
  size {n} _ = n
  
  fromSTree : ∀ {n : ℕ} → STree n → STree' n
  fromSTree Leaf = ⟨ (zero , lift tt) ⟩
  fromSTree {suc n} (Node nₗ nᵣ) = ⟨ (zero , (size nₗ , size nᵣ) , refl , fromSTree nₗ , fromSTree nᵣ) ⟩

  toSTree : ∀ {n : ℕ} → STree' n → STree n
  toSTree {zero} ⟨ fst , snd ⟩ = Leaf
  toSTree {suc .(sl + sr)} ⟨ zero , (sl , sr) , refl , nₗ , nᵣ ⟩ =
    Node (toSTree nₗ) (toSTree nᵣ)
  toSTree {suc n} ⟨ suc () , snd ⟩

  STree-iso₁ : ∀ {n : ℕ} {t : STree n} → toSTree (fromSTree t) ≡ t
  STree-iso₁ {zero} {Leaf} = refl
  STree-iso₁ {suc n} {Node nₗ nᵣ} =
    cong₂ Node STree-iso₁ STree-iso₁

  STree-iso₂ : ∀ {n : ℕ} {t : STree' n} → fromSTree (toSTree t) ≡ t
  STree-iso₂ {zero} {⟨ zero , snd ⟩} = refl
  STree-iso₂ {zero} {⟨ suc () , snd ⟩}
  STree-iso₂ {suc .(sl + sr)} {⟨ zero , (sl , sr) , refl , nₗ , nᵣ ⟩}
    = cong₂ (λ r₁ r₂ → ⟨ zero , (sl , sr) , refl , (r₁ , r₂) ⟩) STree-iso₂ STree-iso₂
  STree-iso₂ {suc n} {⟨ suc () , snd ⟩}

  open import Data.List

  data _∈_ {a : Set} (x : a) : List a →  Set where
    here  : ∀ {xs : List a} → x ∈ (x ∷ xs)
    there : ∀ {y : a} {xs : List a} → x ∈ xs → x ∈ (y ∷ xs)

  ∈D : ∀ {a : Set} → a → func zeroL (List a) (List a)
  ∈D {a} v = func.mk
    λ { []       → `σ 0 λ ()
      ; (x ∷ xs) → `σ 2
           λ { zero      → `Σ (x ≡ v) λ { refl → `1 }
             ; (suc zero) → `var xs
             ; (suc (suc ())) }
      }

  _∈'_ : ∀ {a : Set} → a → List a → Set
  x ∈' xs = μ (∈D x) xs

  from∈ : ∀ {a : Set} {x : a} {xs : List a} → x ∈ xs → x ∈' xs
  from∈ here         = ⟨ (zero , refl , lift tt) ⟩
  from∈ (there elem) = ⟨ suc zero , from∈ elem ⟩

  to∈ : ∀ {a : Set} {x : a} {xs : List a} → x ∈' xs → x ∈ xs
  to∈ {xs = []    } ⟨ () , snd ⟩
  to∈ {xs = x ∷ xs} ⟨ zero , refl , lift tt ⟩ = here
  to∈ {xs = x ∷ xs} ⟨ suc zero , snd ⟩        = there (to∈ snd)
  to∈ {xs = x ∷ xs} ⟨ suc (suc ()) , snd ⟩

  ∈-iso₁ : ∀ {a : Set} {x : a} {xs : List a} {elem : x ∈ xs} → to∈ (from∈ elem) ≡ elem
  ∈-iso₁ {elem = here}       = refl
  ∈-iso₁ {elem = there elem} = cong there ∈-iso₁

  ∈-iso₂ : ∀ {a : Set} {x : a} {xs : List a} {elem : x ∈' xs} → from∈ (to∈ elem) ≡ elem
  ∈-iso₂ {xs = []} {⟨ () , snd ⟩}
  ∈-iso₂ {xs = x ∷ xs} {⟨ zero , refl , lift tt ⟩} = refl
  ∈-iso₂ {xs = x ∷ xs} {⟨ suc zero , snd ⟩} =
    cong (λ v → ⟨ ((suc zero) , v) ⟩) ∈-iso₂
  ∈-iso₂ {xs = x ∷ xs} {⟨ suc (suc ()) , snd ⟩}

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
          λ { zero       → `Σ (α ≡ β)
              λ { refl → `Σ (τ ≡ σ) λ { refl → `1 } }
            ; (suc zero) → `var Γ
            ; (suc (suc ())) } }


  [_↦_]'_ : Id → Ty → Ctx → Set
  [ α ↦ τ ]' Γ = μ (↦D α τ) Γ

  from↦ : ∀ {α : Id} {τ : Ty} {Γ : Ctx} → [ α ↦ τ ] Γ → [ α ↦ τ ]' Γ
  from↦ TOP      = ⟨ (zero , refl , refl , (lift tt)) ⟩
  from↦ (POP jd) = ⟨ ((suc zero) , from↦ jd) ⟩

  to↦ : ∀ {α : Id} {τ : Ty} {Γ : Ctx} → ([ α ↦ τ ]' Γ → [ α ↦ τ ] Γ)
  to↦ {Γ = ∅} ⟨ () , snd ⟩
  to↦ {Γ = Γ , β ∶ σ} ⟨ zero , refl , refl , lift tt ⟩ = TOP
  to↦ {Γ = Γ , β ∶ σ} ⟨ suc zero , snd ⟩               = POP (to↦ snd)
  to↦ {Γ = Γ , β ∶ σ} ⟨ suc (suc ()) , snd ⟩

  ↦-iso₁ : ∀ {α : Id} {τ : Ty} {Γ : Ctx} {jd : [ α ↦ τ ] Γ} → to↦ (from↦ jd) ≡ jd
  ↦-iso₁ {jd = TOP}    = refl
  ↦-iso₁ {jd = POP jd} = cong POP ↦-iso₁
  
  ↦-iso₂ : ∀ {α : Id} {τ : Ty} {Γ : Ctx} {jd : [ α ↦ τ ]' Γ} → from↦ (to↦ jd) ≡ jd
  ↦-iso₂ {Γ = ∅} {⟨ () , snd ⟩}
  ↦-iso₂ {Γ = Γ , β ∶ τ} {⟨ zero , refl , refl , lift tt ⟩} = refl
  ↦-iso₂ {Γ = Γ , β ∶ τ} {⟨ suc zero , snd ⟩} =
    cong (λ x → ⟨ ((suc zero) , x) ⟩) ↦-iso₂
  ↦-iso₂ {Γ = Γ , β ∶ τ} {⟨ suc (suc ()) , snd ⟩}

  data Tm : Set where
    $_  : Id → Tm
    Λ_⇒_ : Id → Tm → Tm
    _∙_  : Tm → Tm → Tm

  data _⊢_∶_ (Γ : Ctx) : Tm → Ty → Set where

    VAR : ∀ {α τ} → [ α ↦ τ ] Γ
          ---------------------
        → Γ ⊢ $ α ∶ τ

    
    ABS : ∀ {α τ σ t} → (Γ , α ∶ σ) ⊢ t ∶ τ
          ----------------------------------
        → Γ ⊢ Λ α ⇒ t ∶ (σ `→ τ)

    
    APP : ∀ {t₁ t₂ τ σ} → Γ ⊢ t₁ ∶ (σ `→ τ) → Γ ⊢ t₂ ∶ σ
          ------------------------------------------------
        → Γ ⊢ t₁ ∙ t₂ ∶ τ
  

  ⊢D : func zeroL (Ctx × Tm × Ty) (Ctx × Tm × Ty)
  ⊢D = func.mk
    λ { (Γ , ($ α) , τ)     → `σ 1
          (λ { zero → `Σ ([ α ↦ τ ] Γ) λ _ → `1
             ; (suc ()) })
      ; (Γ , (Λ α ⇒ t) , `τ      ) → `σ 0 λ ()
      ; (Γ , (Λ α ⇒ t) , (σ `→ τ)) → `σ 1
          (λ { zero → `var ((Γ , α ∶ σ) , t , τ)
             ; (suc ()) } )
      ; (Γ , (t₁ ∙ t₂) , τ)  → `σ 1
          (λ { zero → `Σ Ty λ σ →
               `var (Γ , t₁ , σ `→ τ) `× `var (Γ , t₂ , σ)
             ; (suc ()) })
      }

  _⊢'_∶_ : Ctx → Tm → Ty → Set
  Γ ⊢' t ∶ τ = μ ⊢D (Γ , t , τ)

  ⊢→Ty : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} → Γ ⊢ t ∶ τ → Ty
  ⊢→Ty {τ = τ} _ = τ

  from⊢ : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} → Γ ⊢ t ∶ τ → Γ ⊢' t ∶ τ
  from⊢ (VAR x)       = ⟨ (zero , x , lift tt) ⟩
  from⊢ (ABS jd)      = ⟨ (zero , from⊢ jd) ⟩
  from⊢ (APP jd₁ jd₂) = ⟨ (zero , ⊢→Ty jd₂ , from⊢ jd₁ , from⊢ jd₂) ⟩

  to⊢ : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} → Γ ⊢' t ∶ τ → Γ ⊢ t ∶ τ
  to⊢ {t = $ α} {τ} ⟨ zero , fst , lift tt ⟩ = VAR fst
  to⊢ {t = $ α} {τ} ⟨ suc () , snd ⟩
  to⊢ {t = Λ α ⇒ t} {`τ} ⟨ () , snd ⟩
  to⊢ {t = Λ α ⇒ t} {τ `→ τ₁} ⟨ zero , snd ⟩ = ABS (to⊢ snd)
  to⊢ {t = Λ α ⇒ t} {τ `→ τ₁} ⟨ suc () , snd ⟩
  to⊢ {t = t ∙ t₁} {τ} ⟨ zero , _ , jd₁ , jd₂ ⟩ = APP (to⊢ jd₁) (to⊢ jd₂)
  to⊢ {t = t ∙ t₁} {τ} ⟨ suc () , snd ⟩

  ⊢-iso₁ : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} {jd : Γ ⊢ t ∶ τ} → to⊢ (from⊢ jd) ≡ jd
  ⊢-iso₁ {jd = VAR _}   = refl
  ⊢-iso₁ {jd = ABS _}   = cong ABS ⊢-iso₁
  ⊢-iso₁ {jd = APP _ _} = cong₂ APP ⊢-iso₁ ⊢-iso₁

  ⊢-iso₂ : ∀ {Γ : Ctx} {t : Tm} {τ : Ty} {jd : Γ ⊢' t ∶ τ} → from⊢ (to⊢ jd) ≡ jd
  ⊢-iso₂ {t = $ α} {τ} {⟨ zero , _ , lift tt ⟩} = refl
  ⊢-iso₂ {t = $ α} {τ} {⟨ suc () , snd ⟩}
  ⊢-iso₂ {t = Λ α ⇒ t} {`τ} {⟨ () , snd ⟩}
  ⊢-iso₂ {t = Λ α ⇒ t} {τ `→ τ₁} {⟨ zero , jd ⟩} =
    cong (λ x → ⟨ (zero , x) ⟩) ⊢-iso₂
  ⊢-iso₂ {t = Λ α ⇒ t} {τ `→ τ₁} {⟨ suc () , snd ⟩}
  ⊢-iso₂ {t = t ∙ t₁} {τ} {⟨ zero , σ , jd₁ , jd₂ ⟩} =
    cong₂ (λ x y → ⟨ (zero , σ , (x , y)) ⟩) ⊢-iso₂ ⊢-iso₂
  ⊢-iso₂ {t = t ∙ t₁} {τ} {⟨ suc () , snd ⟩}
