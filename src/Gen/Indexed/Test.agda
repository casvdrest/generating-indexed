open import src.Data
open import src.Gen.Base
open import src.Gen.Regular.Examples
open import src.Gen.Indexed.Examples
open import src.Gen.Indexed.Regex
open import src.Gen.Indexed.Lambda

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat using (ℕ; suc; zero; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec using (_∷_; [])
open import Data.Bool 
open import Data.Product using (_,_)
open import Data.List using ([_]; []; _∷_; take)  

module src.Gen.Indexed.Test where 

  ------------------------------------------ R E G E X  ----------------------------------------

  match-cas : Regex
  match-cas = `c 'c' ∙ (`c 'a' ∙ (`c 's' ∙ one))

  match-agda : Regex
  match-agda = `c 'a' ∙ (`c 'g' ∙ (`c 'd' ∙ (`c 'a' ∙ one)))
  
  regex_test1 : 𝔾-runᵢ regex match-cas 4
    ≡ [ ('c' ∷ 'a' ∷ 's' ∷ [] , SEQ CHAR (SEQ CHAR (SEQ CHAR ONE))) ]
  regex_test1 = refl

  regex_test2 : 𝔾-runᵢ regex match-agda 5
    ≡ [ 'a' ∷ 'g' ∷ 'd' ∷ 'a' ∷ [] , SEQ CHAR (SEQ CHAR (SEQ CHAR (SEQ CHAR ONE))) ]
  regex_test2 = refl

  regex_test3 : 𝔾-runᵢ regex (match-agda + match-cas) 6
    ≡ ('a' ∷ 'g' ∷ 'd' ∷ 'a' ∷ [] , LEFT (SEQ CHAR (SEQ CHAR (SEQ CHAR (SEQ CHAR ONE))))) ∷
      ('c' ∷ 'a' ∷ 's' ∷ [] ,       RIGHT (SEQ CHAR (SEQ CHAR (SEQ CHAR ONE)))) ∷
    []
  regex_test3 = refl
    
  regex_test5 : 𝔾-runᵢ regex (`c 'a' *) 5
    ≡ (ε , STOP) ∷
      ('a' ∷ [] ,                   STEP CHAR STOP) ∷
      ('a' ∷ 'a' ∷ [] ,             STEP CHAR (STEP CHAR STOP)) ∷
      ('a' ∷ 'a' ∷ 'a' ∷ [] ,       STEP CHAR (STEP CHAR (STEP CHAR STOP))) ∷
      ('a' ∷ 'a' ∷ 'a' ∷ 'a' ∷ [] , STEP CHAR (STEP CHAR (STEP CHAR (STEP CHAR STOP)))) ∷ []
  regex_test5 = refl

  regex_test6 : 𝔾-runᵢ regex ((`c 'a' ∙ `c 'b') *) 5
    ≡ (ε , STOP) ∷
      ('a' ∷ 'b' ∷ [] ,                         STEP (SEQ CHAR CHAR) STOP) ∷
      ('a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ [] ,             STEP (SEQ CHAR CHAR) (STEP (SEQ CHAR CHAR) STOP)) ∷
      ('a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ [] , STEP (SEQ CHAR CHAR) (STEP (SEQ CHAR CHAR) (STEP (SEQ CHAR CHAR) STOP))) ∷ []
  regex_test6 = refl

  regex'_test1 : 𝔾-runᵢ regex' ('a' ∷ []) 2
    ≡ ((`c 'a') , CHAR) ∷
      ((`c 'a' + zero) , LEFT CHAR) ∷
      ((zero + `c 'a') , RIGHT CHAR) ∷
      ((`c 'a' + one) , LEFT CHAR) ∷
      ((one + `c 'a') , (RIGHT CHAR)) ∷ []
  regex'_test1 = refl


  ------------------------------------------ L A M B D A  C A L C U L U S ----------------------------------------

  λ-test1 : 𝔾-runᵢ λ-calculus (`ℕ `→ `ℕ , 0 ↦ `ℕ ∷ ∅) 4
    ≡ (Λ 1 ⇒ $ 1 , ABS (VAR TOP)) ∷
      (let` 1 := $ 0 in` Λ 2 ⇒ $ 2 , LET (VAR TOP) (ABS (VAR TOP))) ∷
      (Λ 1 ⇒ let` 2 := $ 1 in` $ 2 , ABS (LET (VAR TOP) (VAR TOP))) ∷
      (let` 1 := (let` 1 := $ 0 in` $ 1) in` Λ 2 ⇒ $ 2 , LET (LET (VAR TOP) (VAR TOP)) (ABS (VAR TOP))) ∷
      (Λ 1 ⇒ $ 0 , ABS (VAR (POP TOP))) ∷
      (let` 1 := (Λ 1 ⇒ $ 1) in` (Λ 2 ⇒ $ 2) , LET (ABS (VAR TOP)) (ABS (VAR TOP))) ∷ []
  λ-test1 = refl
  
  λ-test'1 : 𝔾-runᵢ λ-calculus' ($ 0 , 0 ↦ `ℕ ∷ ∅) 2 ≡ ((`ℕ , VAR TOP) ∷ [])
  λ-test'1 = refl

  λ-test'2 : 𝔾-runᵢ λ-calculus' ((Λ 0 ⇒ $ 0) ∙ ($ 0) , 0 ↦ `ℕ ∷ ∅) 4 ≡ (`ℕ , APP (ABS (VAR TOP)) (VAR TOP)) ∷ []
  λ-test'2 = refl

  λ-test'3 : take 5 (𝔾-runᵢ λ-calculus' (Λ 0 ⇒ (Λ 1 ⇒ (($ 0) ∙ ($ 1))) , ∅) 6)
    ≡ (((`ℕ `→ `ℕ) `→ (`ℕ `→ `ℕ)) , ABS (ABS (APP (VAR (POP TOP)) (VAR TOP)))) ∷
      (((`ℕ `→ (`ℕ `→ `ℕ)) `→ (`ℕ `→ (`ℕ `→ `ℕ))) , (ABS (ABS (APP (VAR (POP TOP)) (VAR TOP))))) ∷
      (((`ℕ `→ (`ℕ `→ (`ℕ `→ `ℕ))) `→ (`ℕ `→ (`ℕ `→ (`ℕ `→ `ℕ)))) , (ABS (ABS (APP (VAR (POP TOP)) (VAR TOP))))) ∷
      (((`ℕ `→ (`ℕ `→ (`ℕ `→ (`ℕ `→ `ℕ)))) `→ (`ℕ `→ (`ℕ `→ (`ℕ `→ (`ℕ `→ `ℕ))))) , (ABS (ABS (APP (VAR (POP TOP)) (VAR TOP))))) ∷
      (((`ℕ `→ (`ℕ `→ ((`ℕ `→ `ℕ) `→ `ℕ))) `→ (`ℕ `→ (`ℕ `→ ((`ℕ `→ `ℕ) `→ `ℕ)))) , (ABS (ABS (APP (VAR (POP TOP)) (VAR TOP))))) ∷ []
  λ-test'3 = refl


  ------------------------------------------ M I S C ----------------------------------------

  prop : 𝔾-runᵢ fin 10 10  ≡
      zero ∷ suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero))
    ∷ suc (suc (suc (suc zero))) ∷ suc (suc (suc (suc (suc zero))))
    ∷ suc (suc (suc (suc (suc (suc zero))))) ∷ suc (suc (suc (suc (suc (suc (suc zero))))))
    ∷ suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    ∷ suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ∷ []
  prop = refl

  prop1' : 𝔾-runᵢ ≤m (1 , 2) 10 ≡ [ s≤s z≤n ]
  prop1' = refl

  prop2' : 𝔾-runᵢ ≤m (2 , 1) 10 ≡ []
  prop2' = refl

  prop3' : 𝔾-runᵢ ≤n+k (1 , 1) 10 ≡ [ s≤s z≤n ]
  prop3' = refl

  prop4' : 𝔾-runᵢ  ≤n+k (3 , 0) 10 ≡ [ s≤s (s≤s (s≤s z≤n)) ]
  prop4' = refl

  prop5 : 𝔾-runᵢ (vec bool) 2 5 ≡
    (true  ∷ true ∷ []) ∷ (true  ∷ false ∷ []) ∷
    (false ∷ true ∷ []) ∷ (false ∷ false ∷ []) ∷ []
  prop5 = refl

  prop6 : 𝔾-runᵢ sortedₛ (1 ∷ 2 ∷ 3 ∷ []) 15 ≡ step (s≤s z≤n) (step (s≤s (s≤s z≤n)) single) ∷ []
  prop6 = refl

  prop7 : 𝔾-runᵢ sortedₛ (3 ∷ 2 ∷ 1 ∷ []) 15 ≡ []
  prop7 = refl
