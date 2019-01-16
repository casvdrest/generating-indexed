open import Data.Char
open import Data.List
open import Data.Nat using (suc; zero)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import src.Data using (_⊗_; _,_; fst; snd)
open import src.Omega.Base
open import src.Omega.Indexed
open import src.Omega.Examples

open import Category.Functor
open import Category.Applicative
open import Category.Monad

open import Relation.Nullary
open import Relation.Binary 
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym )

open import Function

module src.Omega.Regex where

  open RawFunctor ⦃...⦄ using (_<$>_)
  open RawMonad ⦃...⦄ using (_>>_; _>>=_; return; pure)

  String : Set
  String = List Char

  ε : String
  ε = []

  char : ω Char
  char _ = 'a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ 'e' ∷ 'f' ∷ 'g' ∷ 's' ∷ []

  string : ω String
  string = ⟨ list char ⟩

  splits' : (s : String) → List (Σ[ sp ∈ (String ⊗ String) ] ((fst sp ++ snd sp) ≡ s))
  splits' [] = [ ([] , []) , refl ]
  splits' (x ∷ s) = (([] , x ∷ s) , refl) ∷ map (λ sp → (x ∷ fst (Σ₁ sp)  , snd (Σ₁ sp)) , cong (_∷_ x) (Σ₂ sp)) (splits' s)

  splits-test : splits' ('a' ∷ 'b' ∷ 'c' ∷ [])
    ≡ (([] , 'a' ∷ 'b' ∷ 'c' ∷ []) , refl) ∷
      (('a' ∷ [] , 'b' ∷ 'c' ∷ []) , refl) ∷
      (('a' ∷ 'b' ∷ [] , 'c' ∷ []) , refl) ∷
      (('a' ∷ 'b' ∷ 'c' ∷ [] , []) , refl) ∷ []
  splits-test = refl

  splits : (s : String) → ω (Σ[ sp ∈ (String ⊗ String) ] ((fst sp ++ snd sp) ≡ s))
  splits s _ = splits' s

  data Regex : Set where 
    `c   : Char → Regex
    zero : Regex
    one  : Regex
    _+_  : Regex → Regex → Regex
    _∙_  : Regex → Regex → Regex
    _*   : Regex → Regex

  *-neq : ∀ {r r' : Regex} → ¬ r ≡ r' → ¬ r * ≡ r' *
  *-neq contra refl = contra refl

  +-left-neq : ∀ {r r' r'' r'''} → ¬ r ≡ r' → ¬ r + r'' ≡ r' + r'''
  +-left-neq contra refl = contra refl

  +-right-neq : ∀ {r r' r'' r'''} → ¬ r ≡ r' → ¬ r'' + r ≡ r''' + r'
  +-right-neq contra refl = contra refl

  ∙-left-neq : ∀ {r r' r'' r'''} → ¬ r ≡ r' → ¬ r ∙ r'' ≡ r' ∙ r'''
  ∙-left-neq contra refl = contra refl

  ∙-right-neq : ∀ {r r' r'' r'''} → ¬ r ≡ r' → ¬ r'' ∙ r ≡ r''' ∙ r'
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
  `c x ≟ (r' + r'') = no λ()
  `c x ≟ (r' ∙ r'') = no λ()
  `c x ≟ (r' *) = no λ()
  zero ≟ `c x = no λ()
  zero ≟ zero = yes refl
  zero ≟ one = no λ()
  zero ≟ (r' + r'') = no λ()
  zero ≟ (r' ∙ r'') = no λ()
  zero ≟ (r' *) = no λ()
  one ≟ `c x = no λ()
  one ≟ zero = no λ()
  one ≟ one = yes refl
  one ≟ (r' + r'') = no λ()
  one ≟ (r' ∙ r'') = no λ()
  one ≟ (r' *) = no λ()
  (r + r₁) ≟ `c x = no λ()
  (r + r₁) ≟ zero = no λ()
  (r + r₁) ≟ one = no λ()
  (r + r₁) ≟ (r' + r'') with r ≟ r'
  ((r + r₁) ≟ (r' + r'')) | yes p with r₁ ≟ r''
  ((r + r₁) ≟ (.r + .r₁)) | yes refl | yes refl = yes refl
  ((r + r₁) ≟ (r' + r'')) | yes p | no ¬p = no (+-right-neq ¬p)
  ((r + r₁) ≟ (r' + r'')) | no ¬p = no (+-left-neq ¬p)
  (r + r₁) ≟ (r' ∙ r'') = no λ()
  (r + r₁) ≟ (r' *) = no λ()
  (r ∙ r₁) ≟ `c x = no λ()
  (r ∙ r₁) ≟ zero = no λ()
  (r ∙ r₁) ≟ one = no λ()
  (r ∙ r₁) ≟ (r' + r'') = no λ()
  (r ∙ r₁) ≟ (r' ∙ r'') with r ≟ r'
  ((r ∙ r₁) ≟ (r' ∙ r'')) | yes p with r₁ ≟ r''
  ((r ∙ r₁) ≟ (.r ∙ .r₁)) | yes refl | yes refl = yes refl
  ((r ∙ r₁) ≟ (r' ∙ r'')) | yes p | no ¬p = no (∙-right-neq ¬p)
  ((r ∙ r₁) ≟ (r' ∙ r'')) | no ¬p = no (∙-left-neq ¬p) 
  (r ∙ r₁) ≟ (r' *) = no λ()
  (r *) ≟ `c x = no λ()
  (r *) ≟ zero = no λ()
  (r *) ≟ one = no λ()
  (r *) ≟ (r' + r'') = no λ()
  (r *) ≟ (r' ∙ r'') = no λ()
  (r *) ≟ (r' *) with r ≟ r'
  ((r *) ≟ (.r *)) | yes refl = yes refl
  ((r *) ≟ (r' *)) | no ¬p = no (*-neq ¬p)

  L[_] : Regex → Regex
  L[ r ] = r

  regexGen : ⟪ ω Regex ⟫
  regexGen μ = ⦇ `c char ⦈
             ∥ ⦇ zero    ⦈
             ∥ ⦇ one     ⦈
             ∥ ⦇ μ + μ   ⦈
             ∥ ⦇ μ ∙ μ   ⦈
             ∥ ⦇ μ *     ⦈

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

  str-eq : ∀ {s s' r} → s ≡ s' → s ∈ L[ r ] → s' ∈ L[ r ]
  str-eq refl p  = p

  regex-eq : ∀ {s r r'} → r ≡ r' → s ∈ L[ r ] → s ∈ L[ r' ]
  regex-eq refl p = p 

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

  tail-eq : ∀ {a : Set} {x : a} {xs ys : List a} → xs ≡ ys → x ∷ xs ≡ x ∷ ys
  tail-eq {x = x} p = cong (_∷_ x) p

  regex' : ⟪ ωᵢ (λ s → Σ[ r ∈ Regex ] s ∈ L[ r ]) ⟫
  regex' μ [] = (pure (one , ONE) ∥ ( do r ← ⟨ regexGen ⟩ 
                                         return (r * , STOP) ))
              ∥ ( do r  ← μ []
                     r' ← ⟨ regexGen ⟩
                     return ((Σ₁ r + r') , LEFT (Σ₂ r)) )
              ∥ ( do r  ← μ []
                     r' ← ⟨ regexGen ⟩
                     return ((r' + Σ₁ r) , RIGHT (Σ₂ r)) )
              ∥ ( do (xs , ys) , p ← splits []
                     r  ← μ xs
                     r' ← μ ys
                     ((return ((Σ₁ r ∙ Σ₁ r') , str-eq p (SEQ (Σ₂ r) (Σ₂ r'))))) )
  regex' μ (x ∷ s) = (char-ap x s)
                   ∥ ( do r  ← μ (x ∷ s)
                          r' ← ⟨ regexGen ⟩
                          return ((Σ₁ r + r') , LEFT (Σ₂ r)) )
                   ∥ ( do r  ← μ (x ∷ s)
                          r' ← ⟨ regexGen ⟩
                          return ((r' + Σ₁ r) , RIGHT (Σ₂ r)) )
                   ∥ ( do (xs , ys) , p ← splits (x ∷ s)
                          r  ← μ xs
                          r' ← μ ys
                          eqp ← step-eq (Σ₁ r) (Σ₂ r')
                          ((return ((Σ₁ r ∙ Σ₁ r') , str-eq p (SEQ (Σ₂ r) (Σ₂ r')))) ∥
                           (return ((Σ₁ r) * , str-eq p (STEP (Σ₂ r) (regex-eq eqp (Σ₂ r')))))) )
                   where step-eq : ∀ {ys r'} → (r : Regex) → ys ∈ r' → ω (r' ≡ r *)
                         step-eq {r' = r'} r p with r' ≟ (r *)
                         step-eq {r' = r'} r p | yes p₁ = pure p₁
                         step-eq {r' = r'} r p | no ¬p = uninhabited

                         char-ap : (c : Char) → (s : String) → ω (Σ[ r ∈ Regex ] ((c ∷ s) ∈ L[ r ]))
                         char-ap c [] = pure (`c c , CHAR)
                         char-ap c (x ∷ s) = uninhabited

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
      ('c' ∷ 'a' ∷ 's' ∷ [] ,       RIGHT (SEQ CHAR (SEQ CHAR (SEQ CHAR ONE)))) ∷
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
      ('a' ∷ 'b' ∷ [] ,                         STEP (SEQ CHAR CHAR) STOP) ∷
      ('a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ [] ,             STEP (SEQ CHAR CHAR) (STEP (SEQ CHAR CHAR) STOP)) ∷
      ('a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ [] , STEP (SEQ CHAR CHAR) (STEP (SEQ CHAR CHAR) (STEP (SEQ CHAR CHAR) STOP))) ∷ []
  regex_test6 = refl

  regex'_test1 : take 10 (⟨ regex' ⟩ᵢ ('a' ∷ []) 2)
    ≡ ((`c 'a') , CHAR) ∷
      ((`c 'a' + `c 'a') , LEFT CHAR) ∷
      ((`c 'a' + `c 'a') , RIGHT CHAR) ∷
      ((`c 'a' + zero) , LEFT CHAR) ∷
      ((zero + `c 'a') , RIGHT CHAR) ∷
      ((`c 'a' + `c 'b') , LEFT CHAR) ∷
      ((`c 'b' + `c 'a') , RIGHT CHAR) ∷
      ((`c 'a' + one) , LEFT CHAR) ∷ 
      ((one + `c 'a') , RIGHT CHAR) ∷
      ((`c 'a' + `c 'c') , LEFT CHAR) ∷ []
  regex'_test1 = refl
