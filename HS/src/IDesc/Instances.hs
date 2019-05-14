{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

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
  finSDesc _ (SSuc n) = SSuc2 (SSuc2 SZero2) :+>~ (SOne :::~ SVar (demote n) :::~ SVNil)

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
  vecSDesc p _ (SSuc n) = SK p SUnit_ :*:~ SVar (demote n)

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

  data Term a = VarT a
              | AbsT a (Term a)
              | AppT (Term a) (Term a)
              deriving (Show, Eq , Generics.Generic, DepthCalc)

  type family WSTermDesc (n :: Nat) :: IDesc (Term Nat) Nat
  type instance WSTermDesc n = 
    SSuc (SSuc (SSuc SZero)) :+> 
    (   K ('Proxy :: Proxy Nat) n
    ::: Var (Suc n) 
    ::: Var n :*: Var n 
    ::: VNil )

  type instance Desc T_WSTERM (Term Nat) Nat n = WSTermDesc n

  wsTermSDesc :: Proxy T_WSTERM -> Sing n -> SingIDesc (WSTermDesc n)
  wsTermSDesc _ n = 
    SSuc2 (SSuc2 (SSuc2 SZero2)) :+>~ 
    (    SK Proxy n
    :::~ SVar (Suc (demote n)) 
    :::~ (SVar (demote n)) :*:~ (SVar (demote n)) 
    :::~ SVNil )

  toTerm :: Proxy T_WSTERM -> Sing n -> Interpret (WSTermDesc n) -> Term Nat
  toTerm _ n (Left x)                  = VarT x
  toTerm _ n (Right (Left x))          = AbsT Zero x
  toTerm _ n (Right (Right (t1 , t2))) = AppT t1 t2

  instance Describe T_WSTERM (Term Nat) Nat where 
    sdesc = wsTermSDesc 
    to    = toTerm

  genTerm :: Nat -> G Nat (Term Nat) (Term Nat)
  genTerm n = 
    case promote n of 
      Promoted n' -> genDesc (Proxy :: Proxy T_WSTERM) n' 

{-
  ----------------------------------------------------------------------------
  -- Rose Trees

  data Rose a = a :> [Rose a] deriving (Show)

  data RLabel = RL | RT

  asLabel :: Anything -> RLabel
  asLabel (Hidden x) = unsafeCoerce x

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
  genRose l = toRose <$> (G (Call undefined RT))

  runRoseGen :: Int -> [Rose Bool]
  runRoseGen = run genRose RT

  ----------------------------------------------------------------------------
  -- Sized Trees

  data Tree = Leaf
            | Node Tree Tree
            deriving (Eq , Show)

  treeFunc :: Func Tree Nat
  treeFunc Zero    = One
  treeFunc (Suc n) = Sigma (Proxy :: Proxy Plus) (pure n) (\(n' , m') -> Var n' :*: Var m') 

  reversePlus :: Nat -> G () (Nat, Nat) (Nat , Nat)
  reversePlus Zero = pure (Zero , Zero)
  reversePlus (Suc n) =  pure (Suc n , Zero)
                     <|> ((\(x, y) -> (x , Suc y)) <$> reversePlus n)

  instance Solve Plus (Nat , Nat) Nat where
    solve _ = reversePlus

  toTree :: Nat -> Anything -> Tree
  toTree Zero _ = Leaf
  toTree (Suc n) (Hidden x) =
    case asPair x of
      (a , b) ->
        case asPair a of
          (ix1 , v1) -> 
            case asPair b of
              (ix2 , v2) -> Node (toTree ix1 (Hidden v1)) (toTree ix2 (Hidden v2))

  tree :: Description Tree Nat
  tree = Description
    { func   = treeFunc
    , to     = toTree
    }

  runTreeGen :: Nat -> Int -> [Tree]
  runTreeGen = run (genDesc tree)
-} 