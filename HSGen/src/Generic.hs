{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Generic where 

  import Data.Proxy

  data Regular where 
    Z :: Regular 
    U :: Regular 
    (:+:) :: Regular -> Regular -> Regular
    (:*:) :: Regular -> Regular -> Regular 
    I :: Regular 
    K :: (a :: *) -> Regular

  data Empty where

  data Unit where 
    TT :: Unit

  type family   Inp (f :: Regular) (r :: *) :: *
  type instance Inp Z r = Empty
  type instance Inp U r = Unit
  type instance Inp (f :+: g) r = Either (Inp f r) (Inp g r)  
  type instance Inp (f :*: g) r = (Inp f r, Inp g r)
  type instance Inp I r = r
  type instance Inp (K a) r = a

  data Fix (f :: Regular) where 
    In :: Inp f (Fix f) -> Fix f

  data a :~: b where 
    Refl :: forall a . a :~: a 

  data Nat = Ze | Su Nat deriving Show

  type NatF = Fix (U :+: I) 

  fromNat :: Nat -> NatF
  fromNat Ze = In (Left TT)
  fromNat (Su n) = In (Right (fromNat n))

  type family Cong (f :: a -> b) (eq :: x :~: y) :: f x :~: f y
  type instance Cong f Refl = Refl

  type family Sym (eq :: x :~: y) :: y :~: x 
  type instance Sym Refl = Refl

  type family   FromNat (n :: Nat) :: NatF
  type instance FromNat Ze = In (Left TT)
  type instance FromNat (Su n) = In (Right (FromNat n))

  type family   ToNat (n :: NatF) :: Nat 
  type instance ToNat (In (Left TT)) = Ze
  type instance ToNat (In (Right n)) = Su (ToNat n)

  type family NatEqFrom (n :: Nat) :: ToNat (FromNat n) :~: n
  type instance NatEqFrom Ze = Refl
  type instance NatEqFrom (Su n) = Cong Su (NatEqFrom n)

  type family NatEqTo (n :: NatF) :: FromNat (ToNat n) :~: n 
  type instance NatEqTo (In (Left TT)) = Refl
  type instance NatEqTo (In (Right n)) = Cong n (NatEqTo n)