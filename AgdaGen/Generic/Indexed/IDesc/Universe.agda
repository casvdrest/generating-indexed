-- Mostly taken from : Dagand, P. E. (2013). A Cosmology of Datatypes, chapter 5 & 6

open import Level 
  renaming ( zero to zeroL 
           ; suc to sucL )

open import Data.Empty
open import Data.Unit 
open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift; _+_)
open import Data.Product
open import Data.Bool
open import Data.List

open import Function
open import Relation.Binary.PropositionalEquality

module AgdaGen.Generic.Indexed.IDesc.Universe where

  infixr 30 _`×_
  infixr 5  ▻_

  -- Universe polymorphic version of 'Fin'
  data Sl {ℓ} : ℕ → Set ℓ where
    ∙  : ∀ {n} → Sl (suc n)
    ▻_ : ∀ {n} → Sl {ℓ} n → Sl (suc n)

  -- Descriptions of indexed datatypes
  --
  -- We purposefully leave out the '`Π' combinator, as it is not needed to
  -- describe any of our example datatypes..
  data IDesc {k : Level}(ℓ : Level)(I : Set k) : Set (k ⊔ (sucL ℓ)) where
    `var : (i : I) → IDesc ℓ I
    `1 : IDesc ℓ I
    _`×_ : (A B : IDesc ℓ I) → IDesc ℓ I
    `σ : (n : ℕ)(T : Sl {ℓ} n → IDesc ℓ I) → IDesc ℓ I
    `Σ : (S : Set ℓ)(T : S → IDesc ℓ I) → IDesc ℓ I

  -- Metadata structure containing additional information about the
  -- '`Σ' nodes in a description
  --
  -- '`Σ` nodes may refer to arbitrary sets in their first components,
  -- hence we likely need to be able to supply additional information
  -- about these nodes when defining generic functions for the IDesc
  -- datatype. 
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

  -- Interpretation of Indexed descriptions 
  ⟦_⟧ : ∀{k ℓ}{I : Set k} → IDesc ℓ I → (I → Set ℓ) → Set ℓ
  ⟦ `var i ⟧ X = X i
  ⟦_⟧ {ℓ = ℓ} `1 X = Lift ℓ ⊤
  ⟦ A `× B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
  ⟦ `σ n T ⟧ X = Σ[ k ∈ Sl n ] ⟦ T k ⟧ X
  ⟦ `Σ S T ⟧ X = Σ[ s ∈ S ] ⟦ T s ⟧ X

  -- 
  record func {k : Level}(ℓ : Level)(I J : Set k) : Set (k ⊔ (sucL ℓ)) where
    constructor mk
    field
      out : J → IDesc ℓ I

  -- Lift the interpretation function to values of 'func'
  ⟦_⟧func : ∀{k ℓ}{I J : Set k} → func ℓ I J → (I → Set ℓ) → (J → Set ℓ)
  ⟦ D ⟧func X j = ⟦ func.out D j ⟧ X 

  -- Fixed-point combinator for interpretations of indexed
  -- descriptions
  data μ {ℓ} {I : Set} (D : func ℓ I I)(i : I) : Set ℓ where
    ⟨_⟩ : ⟦ D ⟧func (μ D) i → μ D i
