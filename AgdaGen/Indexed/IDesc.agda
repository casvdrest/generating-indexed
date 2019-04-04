module AgdaGen.Indexed.IDesc where

  open import Level 
    renaming ( zero to zeroL 
             ; suc to sucL )

  open import Data.Unit 
  open import Data.Nat hiding (_⊔_)
  open import Data.Fin hiding (lift; _+_)
  open import Data.Product
  
  open import Data.Bool
  open import Data.List

  open import Function

  open import Relation.Binary.PropositionalEquality

  open import AgdaGen.Base hiding (μ ; ⟨_⟩)
  open import AgdaGen.Combinators

  infixr 30 _`×_
  infixr 5  ▻_

  data Sl {ℓ} : ℕ → Set ℓ where
    ∙  : ∀ {n} → Sl (suc n)
    ▻_ : ∀ {n} → Sl {ℓ} n → Sl (suc n)
  
  data IDesc {k : Level}(ℓ : Level)(I : Set k) : Set (k ⊔ (sucL ℓ)) where
    `var : (i : I) → IDesc ℓ I
    `1 : IDesc ℓ I
    _`×_ : (A B : IDesc ℓ I) → IDesc ℓ I
    `σ : (n : ℕ)(T : Sl {ℓ} n → IDesc ℓ I) → IDesc ℓ I
    `Σ : (S : Set ℓ)(T : S → IDesc ℓ I) → IDesc ℓ I

  data IDescM {k : Level} {ℓ : Level} {I : Set k} (P : Set ℓ → Set ℓ)
       : IDesc ℓ I → Set (k ⊔ (sucL ℓ)) where
  
    `var~ : ∀ {i : I} → IDescM P (`var i)
    
    `1~ : IDescM P `1
    
    _`×~_ : ∀ {d₁ d₂ : IDesc ℓ I} → IDescM P d₁
          → IDescM P d₂ → IDescM P (d₁ `× d₂)
    
    `σ~ : ∀ {n : ℕ} {T : Sl n → IDesc ℓ I}
        → ((fn : Sl n) → IDescM P (T fn))
        → IDescM P (`σ n T)
        
    `Σ~ : ∀ {S : Set ℓ} {T : S → IDesc ℓ I} → P S
        → ((s : S) → IDescM P (T s))
        → IDescM P (`Σ S T)

  ⟦_⟧ : ∀{k ℓ}{I : Set k} → IDesc ℓ I → (I → Set ℓ) → Set ℓ
  ⟦ `var i ⟧ X = X i
  ⟦_⟧ {ℓ = ℓ} `1  X = Lift ℓ ⊤
  ⟦ A `× B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
  ⟦ `σ n T ⟧ X = Σ[ k ∈ Sl n ] ⟦ T k ⟧ X
  ⟦ `Σ S T ⟧ X = Σ[ s ∈ S ] ⟦ T s ⟧ X

  record func {k : Level}(ℓ : Level)(I J : Set k) : Set (k ⊔ (sucL ℓ)) where
    constructor mk
    field
      out : J → IDesc ℓ I

  ⟦_⟧func : ∀{k ℓ}{I J : Set k} → func ℓ I J → (I → Set ℓ) → (J → Set ℓ)
  ⟦ D ⟧func X j = ⟦ func.out D j ⟧ X 

  data μ {ℓ} {I : Set} (D : func ℓ I I)(i : I) : Set ℓ where
    ⟨_⟩ : ⟦ D ⟧func (μ D) i → μ D i
  
