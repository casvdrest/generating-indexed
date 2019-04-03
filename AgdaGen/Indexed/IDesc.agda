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

  
