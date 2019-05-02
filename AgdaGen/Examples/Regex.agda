open import Data.Char
open import Data.List
open import Data.Nat using (suc; zero; ℕ)
open import Data.Product

open import AgdaGen.Base
open import AgdaGen.Combinators
open import AgdaGen.Examples.Regular

open import Relation.Nullary
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym )

open import Function

module AgdaGen.Examples.Regex where

  open GAlternative ⦃...⦄
  open GApplicative ⦃...⦄
  open GNullable    ⦃...⦄

  String : Set
  String = List Char

  ε : String
  ε = []

  oneOf : ∀ {a : Set} → List a → 𝔾 a
  oneOf []       = empty
  oneOf (x ∷ xs) = pure x ∥ oneOf xs

  char : 𝔾 Char
  char = pure 'a' ∥ pure 'b' ∥ pure 'c' ∥ pure 'd' ∥ pure 'e' ∥ pure 'f' ∥ pure 'g' ∥ pure 's' 

  string : 𝔾 String
  string = list char 


  splits' : (s : String) → List (Σ[ sp ∈ (String × String) ] ((proj₁ sp ++ proj₂ sp) ≡ s))
  splits' [] = [ ([] , []) , refl ]
  splits' (x ∷ s) = (([] , x ∷ s) , refl) ∷ Data.List.map (λ sp → (x ∷ proj₁ (proj₁ sp)  , proj₂ (proj₁ sp)) , cong (_∷_ x) (proj₂ sp)) (splits' s)

  splits-test : splits' ('a' ∷ 'b' ∷ 'c' ∷ [])
    ≡ (([] , 'a' ∷ 'b' ∷ 'c' ∷ []) , refl) ∷
      (('a' ∷ [] , 'b' ∷ 'c' ∷ []) , refl) ∷
      (('a' ∷ 'b' ∷ [] , 'c' ∷ []) , refl) ∷
      (('a' ∷ 'b' ∷ 'c' ∷ [] , []) , refl) ∷ []
  splits-test = refl


  splits : (s : String) → 𝔾 (Σ[ sp ∈ (String × String) ] ((proj₁ sp ++ proj₂ sp) ≡ s))
  splits s = oneOf (splits' s)

  data Regex : Set where 
    `c   : Char → Regex
    zero : Regex
    one  : Regex
    _`+_  : Regex → Regex → Regex
    _`∙_  : Regex → Regex → Regex
    _*   : Regex → Regex


  *-neq : ∀ {r r' : Regex} → ¬ r ≡ r' → ¬ r * ≡ r' *
  *-neq contra refl = contra refl

  +-left-neq : ∀ {r r' r'' r'''} → ¬ r ≡ r' → ¬ r `+ r'' ≡ r' `+ r'''
  +-left-neq contra refl = contra refl

  +-right-neq : ∀ {r r' r'' r'''} → ¬ r ≡ r' → ¬ r'' `+ r ≡ r''' `+ r'
  +-right-neq contra refl = contra refl

  ∙-left-neq : ∀ {r r' r'' r'''} → ¬ r ≡ r' → ¬ r `∙ r'' ≡ r' `∙ r'''
  ∙-left-neq contra refl = contra refl

  ∙-right-neq : ∀ {r r' r'' r'''} → ¬ r ≡ r' → ¬ r'' `∙ r ≡ r''' `∙ r'
  ∙-right-neq contra refl = contra refl

  c-eq : ∀ {c c'} → `c c ≡ `c c' → c ≡ c'
  c-eq refl = refl

  c-neq : ∀ {c c'} → ¬ c ≡ c' → ¬ `c c ≡ `c c'
  c-neq contra refl = contra refl

  postulate char-nat-eq : ∀ {c c' : Char} → toNat c ≡ toNat c' → c ≡ c'
  postulate char-nat-neq : ∀ {c c' : Char} → ¬ toNat c ≡ toNat c' → ¬ c ≡ c'

  _≟_ : Decidable {A = Regex} _≡_
  `c x ≟ `c x₁ with Data.Nat._≟_ (toNat x) (toNat x₁)
  (`c x ≟ `c x₁) | yes p = yes (cong `c (char-nat-eq p))
  (`c x ≟ `c x₁) | no ¬p = no (char-nat-neq ¬p ∘ c-eq)
  `c x ≟ zero = no λ()
  `c x ≟ one = no λ()
  `c x ≟ (r' `+ r'') = no λ()
  `c x ≟ (r' `∙ r'') = no λ()
  `c x ≟ (r' *) = no λ()
  zero ≟ `c x = no λ()
  zero ≟ zero = yes refl
  zero ≟ one = no λ()
  zero ≟ (r' `+ r'') = no λ()
  zero ≟ (r' `∙ r'') = no λ()
  zero ≟ (r' *) = no λ()
  one ≟ `c x = no λ()
  one ≟ zero = no λ()
  one ≟ one = yes refl
  one ≟ (r' `+ r'') = no λ()
  one ≟ (r' `∙ r'') = no λ()
  one ≟ (r' *) = no λ()
  (r `+ r₁) ≟ `c x = no λ()
  (r `+ r₁) ≟ zero = no λ()
  (r `+ r₁) ≟ one = no λ()
  (r `+ r₁) ≟ (r' `+ r'') with r ≟ r'
  ((r `+ r₁) ≟ (r' `+ r'')) | yes p with r₁ ≟ r''
  ((r `+ r₁) ≟ (.r `+ .r₁)) | yes refl | yes refl = yes refl
  ((r `+ r₁) ≟ (r' `+ r'')) | yes p | no ¬p = no (+-right-neq ¬p)
  ((r `+ r₁) ≟ (r' `+ r'')) | no ¬p = no (+-left-neq ¬p)
  (r `+ r₁) ≟ (r' `∙ r'') = no λ()
  (r `+ r₁) ≟ (r' *) = no λ()
  (r `∙ r₁) ≟ `c x = no λ()
  (r `∙ r₁) ≟ zero = no λ()
  (r `∙ r₁) ≟ one = no λ()
  (r `∙ r₁) ≟ (r' `+ r'') = no λ()
  (r `∙ r₁) ≟ (r' `∙ r'') with r ≟ r'
  ((r `∙ r₁) ≟ (r' `∙ r'')) | yes p with r₁ ≟ r''
  ((r `∙ r₁) ≟ (.r `∙ .r₁)) | yes refl | yes refl = yes refl
  ((r `∙ r₁) ≟ (r' `∙ r'')) | yes p | no ¬p = no (∙-right-neq ¬p)
  ((r `∙ r₁) ≟ (r' `∙ r'')) | no ¬p = no (∙-left-neq ¬p) 
  (r `∙ r₁) ≟ (r' *) = no λ()
  (r *) ≟ `c x = no λ()
  (r *) ≟ zero = no λ()
  (r *) ≟ one = no λ()
  (r *) ≟ (r' `+ r'') = no λ()
  (r *) ≟ (r' `∙ r'') = no λ()
  (r *) ≟ (r' *) with r ≟ r'
  ((r *) ≟ (.r *)) | yes refl = yes refl
  ((r *) ≟ (r' *)) | no ¬p = no (*-neq ¬p)

  regexGen : 𝔾 Regex
  regexGen = ⦇ `c (` char) ⦈
           ∥ ⦇ zero ⦈
           ∥ ⦇ one ⦈
           ∥ ⦇ μ `+ μ ⦈
           ∥ ⦇ μ `∙ μ ⦈
           ∥ ⦇ μ * ⦈

  data ∈ᵣ : Regex → Set where

    [Char] : ∀ {c}
             ----------
           → ∈ᵣ (`c c)

    [One] : ------
            ∈ᵣ one

    [Left] : ∀ {r r'} → ∈ᵣ r
             ---------------
           → ∈ᵣ (r `+ r')

    [Right] : ∀ {r r'} → ∈ᵣ r'
              ----------------
            → ∈ᵣ (r `+ r')

    [Seq] : ∀ {r r'} → ∈ᵣ r → ∈ᵣ r'
            -----------------------
          → ∈ᵣ (r `∙ r')

    [Step] : ∀ {r} → ∈ᵣ r → ∈ᵣ (r *)
             -----------------------
           → ∈ᵣ (r *)

    [Stop] : ----------------
             ∀ {r} → ∈ᵣ (r *)
