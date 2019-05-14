{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Data where 

  import GHC.Generics
  import Depth

  -- | Natural numbers
  data Nat = Zero 
           | Suc Nat 
           deriving (Show, Eq, Generic, DepthCalc)

  -- | The empty type. There exists no value of type 'E'
  data E

  -- | Finite sets. Inhabited by exactly as many 
  --   inhabitants as it's index. 
  -- 
  -- > Fs Fz :: Fin (Suc (Suc Zero)) 
  data Fin (n :: Nat) where
    Fz :: Fin (Suc n)
    Fs :: Fin n -> Fin (Suc n)

  infixr 5 :::

  -- | Lists indexed with their length (Vectors). 
  -- 
  -- > [True, False, True] :: Vec Bool (Suc (Suc (Suc Zero)))
  data Vec (a :: *) :: Nat -> * where
    VNil :: Vec a Zero
    (:::) :: a -> Vec a n -> Vec a (Suc n)

  -- | Equality proofs
  -- 
  --   'Refl :: a :~: b' is inhabited iff a ~ b 
  --   Note: since ':~:' is kind-polymorphic, the kinds of 
  --   respectively 'a' and 'b' need to be equal as well. 
  --   In this case, polymorphic kinds are required to be 
  --   able to construct equality proofs ranging over promoted
  --   data constructors. 
  data (:~:) (a :: k1) (b :: k2) where 
    Refl :: forall (k :: *) (ty :: k) . ty :~: ty  
  
  -- | Coerce values using an equality proof
  eqConv :: a :~: b -> a -> b 
  eqConv Refl x = x 
  
  -- | Equality symmetry
  sym :: a :~: b -> b :~: a 
  sym Refl = Refl
  