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
  data Sl {ℓ} : Lift ℓ ℕ → Set ℓ where
    ∙  : ∀ {n} → Sl (lift (suc n))
    ▻_ : ∀ {n} → Sl {ℓ} (lift n) → Sl (lift (suc n))

  -- Descriptions of indexed datatypes
  --
  -- We purposefully leave out the '`Π' combinator, as it is not needed to
  -- describe any of our example datatypes..
  data IDesc {k : Level}(ℓ : Level)(I : Set k) : Set ((sucL k) ⊔ (sucL ℓ)) where
    `var : (i : I) → IDesc ℓ I
    `1 : IDesc ℓ I
    _`×_ : (A B : IDesc ℓ I) → IDesc ℓ I
    `σ : (n : ℕ)(T : Sl {ℓ} (lift n) → IDesc ℓ I) → IDesc ℓ I
    `Σ : (S : Set ℓ)(T : S → IDesc ℓ I) → IDesc ℓ I

  -- Metadata structure containing additional information about the
  -- '`Σ' nodes in a description
  --
  -- '`Σ` nodes may refer to arbitrary sets in their first components,
  -- hence we likely need to be able to supply additional information
  -- about these nodes when defining generic functions for the IDesc
  -- datatype. 
  data IDescM {k : Level} {ℓ : Level} {I : Set k} (P : Set ℓ → Set (sucL ℓ))
       : IDesc ℓ I → Set (k ⊔ (sucL ℓ)) where
  
    `var~ : ∀ {i : I} → IDescM P (`var i)
    
    `1~ : IDescM P `1
    
    _`×~_ : ∀ {d₁ d₂ : IDesc ℓ I} → IDescM P d₁
          → IDescM P d₂ → IDescM P (d₁ `× d₂)
    
    `σ~ : ∀ {n : ℕ} {T : Sl (lift n) → IDesc ℓ I}
        → ((fn : Sl (lift n)) → IDescM P (T fn))
        → IDescM P (`σ n T)
        
    `Σ~ : ∀ {S : Set ℓ} {T : S → IDesc ℓ I} → P S
        → ((s : S) → IDescM P (T s))
        → IDescM P (`Σ S T)

  -- Interpretation of Indexed descriptions 
  ⟦_⟧ : ∀{k ℓ}{I : Set k} → IDesc ℓ I → (I → Set (ℓ ⊔ k)) → Set (ℓ ⊔ k)
  ⟦ `var i ⟧ X = X i
  ⟦_⟧ {k} {ℓ} `1 X = Lift (k ⊔ ℓ) ⊤
  ⟦ A `× B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
  ⟦ `σ n T ⟧ X = Σ[ k ∈ Sl (lift n) ] ⟦ T k ⟧ X
  ⟦ `Σ S T ⟧ X = Σ[ s ∈ S ] ⟦ T s ⟧ X

  -- 
  record func {k : Level}(ℓ : Level)(I J : Set k) : Set (sucL k ⊔ (sucL ℓ)) where
    constructor mk
    field
      out : J → IDesc ℓ I

  -- Lift the interpretation function to values of 'func'
  ⟦_⟧func : ∀{k ℓ}{I J : Set k} → func ℓ I J → (I → Set (ℓ ⊔ k)) → (J → Set (ℓ ⊔ k))
  ⟦ D ⟧func X j = ⟦ func.out D j ⟧ X 

  -- Fixed-point combinator for interpretations of indexed
  -- descriptions
  data μ {ℓ k} {I : Set k} (φ : func ℓ I I) (i : I) : Set (ℓ ⊔ k) where
    ⟨_⟩ : ⟦ φ ⟧func (μ φ) i → μ φ i

  data Fix {ℓ k} {I : Set k} (φ : I → IDesc ℓ I) (i : I) : Set (ℓ ⊔ k) where
    In : ⟦ φ i ⟧ (Fix φ) → Fix φ i

  mapm : ∀ {ℓ k} {I : Set k} {δ : IDesc ℓ I} {P Q : Set ℓ → Set (sucL ℓ)}
       → (∀ {s : Set ℓ} → P s → Q s) → IDescM P δ → IDescM Q δ
  mapm f `var~ = `var~
  mapm f `1~ = `1~
  mapm f (dₗ `×~ dᵣ) = (mapm f dₗ) `×~ mapm f dᵣ
  mapm f (`σ~ fd) = `σ~ (mapm f ∘ fd)
  mapm f (`Σ~ s fd) = `Σ~ (f s) (mapm f ∘ fd)

  +⁻¹ : (n : ℕ) → ℕ → List (Σ (ℕ × ℕ) λ {(n' , m') → n' + m' ≡ n }) 
