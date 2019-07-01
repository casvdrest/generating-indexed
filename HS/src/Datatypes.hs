{-# LANGUAGE DataKinds , DeriveGeneric, DeriveAnyClass, KindSignatures, GADTs, PolyKinds, TypeOperators, RankNTypes #-}

{-|
Module      : Datatypes
Description : Various datatypes used acrooss the library
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

Contains some datatypes that are used in various places throughout this library
-}
module Datatypes where 

  import GHC.Generics
  import Generic.Depth

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

  -- | Equality proofs (heterogeneous)
  -- 
  --   'Refl :: a :~: b' is inhabited if a == b.
  --   Note that such a proof can only exist if and only if  
  --   both a and b have the same kind. 
  -- 
  --   > Refl :: 'True :~: 'True 
  --   Where k1 == k2 == 'Bool
  data (:~:) (a :: k1) (b :: k2) where 
    Refl :: forall (k :: *) (ty :: k) . ty :~: ty  
  
  -- | Coerce values using an equality proof
  eqConv :: forall (a :: *) (b :: *)  . a :~: b -> (a -> b) 
  eqConv Refl = id 
  
  -- | Equality symmetry
  sym :: forall (a :: k) (b :: k) . a :~: b -> b :~: a 
  sym Refl = Refl

  -- | Equality congruence
  cong :: forall (a :: k) (b :: k) (f :: k -> *) . a :~: b -> f a :~: f b 
  cong Refl = Refl

  -- | Equality transitivity 
  trans :: forall (a :: k) (b :: k) (c :: k) . a :~: b -> b :~: c -> a :~: c 
  trans Refl Refl = Refl
  