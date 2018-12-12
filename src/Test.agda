module src.Test where

  open import Relation.Binary.PropositionalEquality hiding ([_])
  open import Agda.Builtin.Coinduction
  
  open import src.Enumerable
  open import src.Indexed
  open import src.Data
  open import src.Product

  open import Data.Nat
  open import Data.Bool
  open import Data.Fin
  open import Data.List
  open import Data.Vec

  enumBool_test1 : prefix 2 (inhabitants Bool) ≡ true ∷ (false ∷ [])
  enumBool_test1 = refl

  enumℕ_test1 : prefix 0 (inhabitants ℕ) ≡ []
  enumℕ_test1 = refl

  enumℕ_test2 : prefix 10 (inhabitants ℕ)
    ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷
      5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ [] 
  enumℕ_test2 = refl

  {-
  enumListBool_test : prefix 10 (inhabitants (List Bool))
    ≡ [] ∷ (false ∷ []) ∷ (false ∷ false ∷ []) ∷ (true ∷ []) ∷
       (false ∷ false ∷ false ∷ []) ∷ (true ∷ false ∷ []) ∷
      (false ∷ true ∷ []) ∷ (true ∷ false ∷ false ∷ []) ∷
      (false ∷ false ∷ false ∷ false ∷ []) ∷ (true ∷ true ∷ []) ∷ []
  enumListBool_test = refl
  

  enumListℕ_test : prefix 25 (inhabitants (List ℕ))
    ≡ [] ∷ (0 ∷ []) ∷ (0 ∷ 0 ∷ []) ∷ (1 ∷ []) ∷ (0 ∷ 0 ∷ 0 ∷ []) ∷
      (1 ∷ 0 ∷ []) ∷ (2 ∷ []) ∷ (0 ∷ 1 ∷ []) ∷ (1 ∷ 0 ∷ 0 ∷ []) ∷
      (2 ∷ 0 ∷ []) ∷ (3 ∷ []) ∷ (0 ∷ 0 ∷ 0 ∷ 0 ∷ []) ∷ (1 ∷ 1 ∷ []) ∷
      (2 ∷ 0 ∷ 0 ∷ []) ∷ (3 ∷ 0 ∷ []) ∷ (4 ∷ []) ∷ (0 ∷ 1 ∷ 0 ∷ []) ∷
      (1 ∷ 0 ∷ 0 ∷ 0 ∷ []) ∷ (2 ∷ 1 ∷ []) ∷ (3 ∷ 0 ∷ 0 ∷ []) ∷ (4 ∷ 0 ∷ []) ∷
      (5 ∷ []) ∷ (0 ∷ 2 ∷ []) ∷ (1 ∷ 1 ∷ 0 ∷ []) ∷ (2 ∷ 0 ∷ 0 ∷ 0 ∷ []) ∷ []
  enumListℕ_test = refl
  -}

  enumFin_test1 : prefix 10 ((inhabitants' Fin) 0) ≡ []
  enumFin_test1 = refl

  enumFin_test2 : prefix 5 ((inhabitants' Fin) 5)
    ≡ zero ∷ suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero)) ∷
      suc (suc (suc (suc zero))) ∷ []
  enumFin_test2 = refl

  {-
  enumVec_test1 : prefix 8 ((inhabitants' (Vec Bool)) 3)
    ≡ (true ∷ true ∷ true ∷ []) ∷ []
  enumVec_test1 = refl
  -}
  
  --   | 0 1 2 3 4 5 
  -- --+------------
  -- 0 | ↗ ↗ ↗ ↗ . . 
  -- 1 | ↗ ➚ ↗ . . .
  -- 2 | ➚ ➚ ↗ . . .
  -- 3 | ➚ ↗ . . . .
  -- 4 | ↗ . . . . .
  -- 5 | . . . . . .
  prop1 : prefix 13 (inhabitants (ℕ ⊗ ℕ))
    ≡  0 , 0 ∷ 1 , 0 ∷ 0 , 1 ∷ 2 , 0 ∷ 1 , 1 ∷
       0 , 2 ∷ 3 , 0 ∷ 2 , 1 ∷ 1 , 2 ∷ 0 , 3 ∷
       4 , 0 ∷ 3 , 1 ∷ 2 , 2 ∷ []
  prop1 = refl

  --   | t f 
  -- --+----
  -- t | ↗ ↗ 
  -- f | ↗ ↗
  prop2 : prefix 4 (inhabitants (Bool ⊗ Bool))
    ≡ true , true  ∷ false , true  ∷
      true , false ∷ false , false ∷ []
  prop2 = refl

  --   | 0 1 2 3 4 5 6 7 
  -- --+----------------
  -- t | ↗ ↗ ↗ ↗ ↗ ↗ ↗ .
  -- f | ↗ ➚ ↗ ↗ ↗ ↗ . .
  prop3 : prefix 11 (inhabitants (Bool ⊗ ℕ))
    ≡ (true , 0) ∷ (false , 0) ∷ (true , 1) ∷ (false , 1) ∷
      (true , 2) ∷ (false , 2) ∷ (true , 3) ∷ (false , 3) ∷
      (true , 4) ∷ (false , 4) ∷ (true , 5) ∷ []
  prop3 = refl

  --   | t f 
  -- --+----
  -- 0 | ↗ ↗ 
  -- 1 | ↗ ↗
  -- 2 | ↗ ↗ 
  -- 3 | ↗ ↗ 
  -- 4 | ↗ ↗ 
  -- 5 | ↗ ↗ 
  -- 6 | ↗ .
  -- 7 | . .
  prop4 : prefix 11 (inhabitants (ℕ ⊗ Bool))
    ≡ (0 , true)  ∷ (1 , true) ∷ (0 , false) ∷ (2 , true) ∷
      (1 , false) ∷ (3 , true) ∷ (2 , false) ∷ (4 , true) ∷
      (3 , false) ∷ (5 , true) ∷ (4 , false) ∷ []
  prop4 = refl

  
