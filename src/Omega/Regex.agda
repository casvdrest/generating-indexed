open import Data.Char
open import Data.List
open import Data.Nat using (suc; zero)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import src.Omega.Base
open import src.Omega.Indexed
open import src.Omega.Examples

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Function

module src.Omega.Regex where

  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawMonad ⦃...⦄ using (_>>_; _>>=_; return; pure)

  String : Set
  String = List Char

  ε : String
  ε = []

  char : ω Char
  char _ = map fromNat (foldr (λ x xs → x ∷ map suc xs) [] (replicate 256 zero))

  string : ω String
  string = ⟨ list char ⟩

  data Regex : Set where 
    `c   : Char → Regex
    zero : Regex
    one  : Regex
    _+_  : Regex → Regex → Regex
    _∙_  : Regex → Regex → Regex
    _*   : Regex → Regex

  L[_] : Regex → Regex
  L[ r ] = r

  data _∈_ : String → Regex → Set where

    CHAR : --------------------------------
           ∀ {c : Char} → [ c ] ∈ L[ `c c ]

    ONE : -----------
          ε ∈ L[ one ]

    LEFT : ∀ {r r' xs} → xs ∈ L[ r ]
           -------------------------
           → xs ∈ L[ r + r' ]

    RIGHT : ∀ {r' r xs} → xs ∈ L[ r ]
            -------------------------
            → xs ∈ L[ r' + r ]

    SEQ : ∀ {r r' xs ys} → xs ∈ L[ r ] → ys ∈ L[ r' ]
          -------------------------------------------
          → (xs ++ ys) ∈ L[ r ∙ r' ]

    STEP : ∀ {r xs ys} → xs ∈ L[ r ] → ys ∈ L[ r * ]
           -----------------------------------------
           → (xs ++ ys) ∈ L[ r * ]

    STOP : ---------------------
           ∀ {r} → ε ∈ L[ r * ]

  regex : ⟪ ωᵢ (λ r → Σ[ s ∈ String ] s ∈ L[ r ]) ⟫
  regex μ (`c x) = ⦇ ([ x ] , CHAR) ⦈
  regex μ zero = uninhabited
  regex μ one  = ⦇ (ε , ONE) ⦈
  regex μ (r + r') = 
    (
      do left ← μ r
         return (Σ₁ left , LEFT (Σ₂ left))
    ) ∥ (
      do right ← μ r'
         return (Σ₁ right , RIGHT (Σ₂ right))
    )
  regex μ (r ∙ r') =
    do hd ← μ r
       tl ← μ r'
       return (Σ₁ hd ++ Σ₁ tl , SEQ (Σ₂ hd) (Σ₂ tl))
  regex μ (r *) = pure (ε , STOP) ∥
    ( do hd ← μ r
         tl ← μ (r *)
         return (Σ₁ hd ++ Σ₁ tl , STEP (Σ₂ hd) (Σ₂ tl))
    )

  match-cas : Regex
  match-cas = `c 'c' ∙ (`c 'a' ∙ (`c 's' ∙ one))

  match-agda : Regex
  match-agda = `c 'a' ∙ (`c 'g' ∙ (`c 'd' ∙ (`c 'a' ∙ one)))

  regex_test1 : ⟨ regex ⟩ᵢ match-cas 4
    ≡ [ ('c' ∷ 'a' ∷ 's' ∷ [] , SEQ CHAR (SEQ CHAR (SEQ CHAR ONE))) ]
  regex_test1 = refl

  regex_test2 : ⟨ regex ⟩ᵢ match-agda 5
    ≡ [ 'a' ∷ 'g' ∷ 'd' ∷ 'a' ∷ [] , SEQ CHAR (SEQ CHAR (SEQ CHAR (SEQ CHAR ONE))) ]
  regex_test2 = refl

  regex_test3 : ⟨ regex ⟩ᵢ (match-agda + match-cas) 6
    ≡ ('a' ∷ 'g' ∷ 'd' ∷ 'a' ∷ [] , LEFT (SEQ CHAR (SEQ CHAR (SEQ CHAR (SEQ CHAR ONE))))) ∷
      ('c' ∷ 'a' ∷ 's' ∷ [] , RIGHT (SEQ CHAR (SEQ CHAR (SEQ CHAR ONE)))) ∷
    []
  regex_test3 = refl
    
  regex_test5 : ⟨ regex ⟩ᵢ (`c 'a' *) 5
    ≡ (ε , STOP) ∷
      ('a' ∷ [] ,                   STEP CHAR STOP) ∷
      ('a' ∷ 'a' ∷ [] ,             STEP CHAR (STEP CHAR STOP)) ∷
      ('a' ∷ 'a' ∷ 'a' ∷ [] ,       STEP CHAR (STEP CHAR (STEP CHAR STOP))) ∷
      ('a' ∷ 'a' ∷ 'a' ∷ 'a' ∷ [] , STEP CHAR (STEP CHAR (STEP CHAR (STEP CHAR STOP)))) ∷ []
  regex_test5 = refl

  regex_test6 : ⟨ regex ⟩ᵢ ((`c 'a' ∙ `c 'b') *) 5
    ≡ (ε , STOP) ∷
      ('a' ∷ 'b' ∷ [] , STEP (SEQ CHAR CHAR) STOP) ∷
      ('a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ [] , STEP (SEQ CHAR CHAR) (STEP (SEQ CHAR CHAR) STOP)) ∷
      ('a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ [] , STEP (SEQ CHAR CHAR) (STEP (SEQ CHAR CHAR) (STEP (SEQ CHAR CHAR) STOP))) ∷ []
  regex_test6 = refl
