{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module IDesc.Instances where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Control.Applicative
  import Unsafe.Coerce
  import Instances
  import qualified GHC.Generics as Generics

  import Singleton 
  import Data

  import IDesc.IDesc

  ----------------------------------------------------------------------------
  -- Finite sets

  type family FinDesc (n :: Nat) :: IDesc Nat Nat 
  type instance FinDesc Zero    = Empty
  type instance FinDesc (Suc n) = (SSuc (SSuc SZero)) :+> (One ::: Var n ::: VNil)

  type instance Desc T_FIN Nat Nat i = FinDesc i

  finSDesc :: Proxy T_FIN -> Sing n -> SingIDesc (FinDesc n)
  finSDesc _ SZero    = SEmpty 
  finSDesc _ (SSuc n) = SSuc2 (SSuc2 SZero2) :+>~ (SOne :::~ SVar (dm n) :::~ SVNil)

  toFin :: Proxy T_FIN -> Sing n -> Interpret (FinDesc n) -> Nat 
  toFin _ (SSuc sn) (Left ()) = Zero 
  toFin _ (SSuc sn) (Right n) = Suc n 

  instance Describe T_FIN Nat Nat where 
    sdesc = finSDesc
    to    = toFin

  genFin :: forall (n :: Nat) . Nat -> G Nat Nat Nat 
  genFin n = 
    case promote n of 
      (Promoted sn) -> genDesc (Proxy :: Proxy T_FIN) sn

  instance IndexedGeneratable Nat Nat where 
    genIndexed = genFin

  ----------------------------------------------------------------------------
  -- Vectors

  type family VecDesc (a :: *) (n :: Nat) :: IDesc [a] Nat
  type instance VecDesc a Zero    = One
  type instance VecDesc a (Suc n) = K ('Proxy :: Proxy a) '() :*: (Var n)

  type instance Desc T_VEC [a] Nat i = VecDesc a i

  vecSDesc :: Generatable a => Proxy a -> Proxy T_VEC -> Sing n -> SingIDesc (VecDesc a n)
  vecSDesc _ _ SZero    = SOne
  vecSDesc p _ (SSuc n) = SK p SUnit_ :*:~ SVar (dm n)

  toVec :: Generatable a => Proxy a -> Proxy T_VEC -> Sing n -> Interpret (VecDesc a n) -> [a]
  toVec _ _ SZero ()          = []
  toVec _ _ (SSuc n) (x , xs) = x : xs

  instance Generatable a => Describe T_VEC [a] Nat where 
    sdesc = vecSDesc Proxy
    to    = toVec Proxy

  genVec :: forall a (n :: Nat) . Generatable a => Nat -> G Nat [a] [a] 
  genVec n = 
    case promote n of 
      (Promoted sn) -> genDesc (Proxy :: Proxy T_VEC) sn

  ----------------------------------------------------------------------------
  -- Well-scoped terms
  
  instance DepthCalc () where
    depth () = 0

  ----------------------------------------------------------------------------
  -- Sized Trees

  data Tree = Leaf
            | Node Tree Tree
            deriving (Eq , Show)

  type family I :: a -> b

  type family STreeDesc (n :: Nat) :: IDesc Tree Nat
  type instance STreeDesc Zero = One  
  type instance STreeDesc (Suc n) = Sigma ('Proxy :: Proxy (Nat , Nat)) (Var I :*: Var I)

  type instance Desc T_STREE Tree Nat n = STreeDesc n

  sTreeSDesc :: Proxy T_STREE -> Sing n -> SingIDesc (STreeDesc n)
  sTreeSDesc _ SZero    = SOne
  sTreeSDesc _ (SSuc n) = 
     SSigma (SVar fst :*:~ SVar snd) (reversePlus (dm n))
     (\_ -> Refl)
 
  toTree :: Proxy T_STREE -> Sing n -> Interpret (STreeDesc n) -> Tree 
  toTree _ SZero ()               = Leaf
  toTree _ (SSuc n) (_ , (l , r)) = Node l r

  instance Describe T_STREE Tree Nat where 
    sdesc = sTreeSDesc
    to    = toTree

  genSTree :: Nat -> G Nat Tree Tree 
  genSTree n =
    case promote n of 
      (Promoted n') -> genDesc (Proxy :: Proxy T_STREE) n' 

  reversePlus :: Nat -> G () (Nat, Nat) (Nat , Nat)
  reversePlus Zero = pure (Zero , Zero)
  reversePlus (Suc n) =  pure (Suc n , Zero)
                      <|> ((\(x, y) -> (x , Suc y)) <$> reversePlus n)
            
  ----------------------------------------------------------------------------
  -- Rose Trees, poc for mutual recursion

  data Rose a = a :> [Rose a] deriving (Show)

  data RLabel = RL | RT

  data RoseTree' a = RoseNode' a (RoseTree' a)
                   | RoseNil'
                   | RoseCons' (RoseTree' a) (RoseTree' a)

  genRose' :: Generatable a => RLabel -> G RLabel (RoseTree' a) (RoseTree' a)
  genRose' RL = pure RoseNil' <|> RoseCons' <$> mu RT <*> mu RL
  genRose' RT = RoseNode' <$> G (Call (\() -> unG gen) ()) <*> mu RL

  toRose :: RoseTree' a -> Rose a
  toRose (RoseNode' v rs) = v :> toRose' rs 

  toRose' :: RoseTree' a -> [Rose a]
  toRose' RoseNil' = []
  toRose' (RoseCons' x xs) = toRose x : toRose' xs

  genRose :: Generatable a => RLabel -> G RLabel (Rose a) (Rose a)
  genRose l = toRose <$> (G (Call (unG . genRose') RT))

  runRoseGen :: Int -> [Rose Bool]
  runRoseGen = run genRose RT
