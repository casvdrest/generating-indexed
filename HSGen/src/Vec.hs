{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Vec where 
  import Data.Proxy

  data Nat = Z | S Nat

  data (n :: Nat) :<=: (m :: Nat) where
    ZS :: forall n . Z :<=: (S n) 
    SS :: forall n m . n :<=: m -> (S n) :<=: (S m)

  type family (n :: Nat) :+: (m :: Nat) :: Nat
  type instance Z :+: m = m 
  type instance (S n) :+: m = S (n :+: m)

  data STree (n :: Nat) where 
    N :: STree Z
    (:<>:) :: STree (n :: Nat) -> STree (m :: Nat) -> STree (S (n :+: m))

  class Val (n :: Nat) where 
    val :: Proxy n -> Int

  instance Val Z where 
    val _ = 0

  instance (Val n) => Val (S n) where 
    val _ = 1 + (val (Proxy :: Proxy n))

  data a :~: b where
    Refl :: forall a . a :~: a

  treeSize :: forall (n :: Nat) . Val n => STree n -> Int
  treeSize tree = val (Proxy :: Proxy n)
  
  tree1 :: STree (S (S (S (S Z))))
  tree1 = N :<>: (N :<>: ((N :<>: N) :<>: N)) 

  data Expr a where 
    Add :: Expr Int -> Expr Int -> Expr Int 
    LTE  :: Expr Int -> Expr Int -> Expr Bool 
    Con :: a -> Expr a

  eval :: Expr a -> a 
  eval (Add e1 e2) = eval e1 + eval e2
  eval (LTE e1 e2) = eval e1 < eval e2 
  eval (Con x)     = x