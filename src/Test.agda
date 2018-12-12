module src.Test where

  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Agda.Builtin.Coinduction

  open import src.Colist
  open import src.Enumerable
  open import src.Indexed

  open import Data.Nat
  open import Data.Bool
  open import Data.Fin
  open import Data.List
  open import Data.Vec

  enumBool_test1 : take' 2 (inhabitants Bool) ≡ false ∷ (true ∷ [])
  enumBool_test1 = refl

  enumℕ_test1 : take' 0 (inhabitants ℕ) ≡ []
  enumℕ_test1 = refl

  enumℕ_test2 : take' 10 (inhabitants ℕ)
    ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷
      5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] 
  enumℕ_test2 = refl

  enumPair_test1 : take' 1 (inhabitants (ℕ ⊗ ℕ)) ≡ 0 , 0 ∷ []
  enumPair_test1 = refl

  enumPair_test2 : take' 10 (inhabitants (ℕ ⊗ ℕ)) -- == ℚ
    ≡ 0 , 0 ∷ 0 , 1 ∷ 1 , 0 ∷
      0 , 2 ∷ 1 , 1 ∷ 2 , 0 ∷
      0 , 3 ∷ 1 , 2 ∷ 2 , 1 ∷
      3 , 0 ∷ []
  enumPair_test2 = refl

  enumListBool_test : take' 10 (inhabitants (List Bool))
    ≡ [] ∷ (false ∷ []) ∷ (false ∷ false ∷ []) ∷ (true ∷ []) ∷
       (false ∷ false ∷ false ∷ []) ∷ (true ∷ false ∷ []) ∷
      (false ∷ true ∷ []) ∷ (true ∷ false ∷ false ∷ []) ∷
      (false ∷ false ∷ false ∷ false ∷ []) ∷ (true ∷ true ∷ []) ∷ []
  enumListBool_test = refl

  enumListℕ_test : take' 25 (inhabitants (List ℕ))
    ≡ [] ∷ (0 ∷ []) ∷ (0 ∷ 0 ∷ []) ∷ (1 ∷ []) ∷ (0 ∷ 0 ∷ 0 ∷ []) ∷
      (1 ∷ 0 ∷ []) ∷ (2 ∷ []) ∷ (0 ∷ 1 ∷ []) ∷ (1 ∷ 0 ∷ 0 ∷ []) ∷
      (2 ∷ 0 ∷ []) ∷ (3 ∷ []) ∷ (0 ∷ 0 ∷ 0 ∷ 0 ∷ []) ∷ (1 ∷ 1 ∷ []) ∷
      (2 ∷ 0 ∷ 0 ∷ []) ∷ (3 ∷ 0 ∷ []) ∷ (4 ∷ []) ∷ (0 ∷ 1 ∷ 0 ∷ []) ∷
      (1 ∷ 0 ∷ 0 ∷ 0 ∷ []) ∷ (2 ∷ 1 ∷ []) ∷ (3 ∷ 0 ∷ 0 ∷ []) ∷ (4 ∷ 0 ∷ []) ∷
      (5 ∷ []) ∷ (0 ∷ 2 ∷ []) ∷ (1 ∷ 1 ∷ 0 ∷ []) ∷ (2 ∷ 0 ∷ 0 ∷ 0 ∷ []) ∷ []
  enumListℕ_test = refl

  enumFin_test1 : take' 10 ((inhabitants' Fin) 0) ≡ []
  enumFin_test1 = refl

  enumFin_test2 : take' 5 ((inhabitants' Fin) 5)
    ≡ zero ∷ suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero)) ∷
      suc (suc (suc (suc zero))) ∷ []
  enumFin_test2 = refl

  enumVec_test1 : take' 8 ((inhabitants' (Vec Bool)) 3)
    ≡ (false ∷ false ∷ (false ∷ [])) ∷ ((false ∷ false ∷ (true ∷ []))) ∷
      ((true ∷ false ∷ (false ∷ []))) ∷ ((false ∷ true ∷ (false ∷ []))) ∷
      ((true ∷ false ∷ (true ∷ []))) ∷ ((false ∷ true ∷ (true ∷ []))) ∷
      ((true ∷ true ∷ (false ∷ []))) ∷ ((true ∷ true ∷ (true ∷ []))) ∷ []
  enumVec_test1 = refl

  

  
  

  
