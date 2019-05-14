{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Singleton where 

  import Data
  import Gen
  import Data.Proxy

  ---------------------------------------------------------------------------
  -- Singleton types

  -- | The class of types for which there exists a singleton type. 
  -- 
  --   The associated type 'Sing :: a -> *' is the singleton type 
  --   of a. 
  --   'demote' describes how a value of type 'Sing x' can be converted 
  --   to a value of type 'a' , for all 'x :: a'
  class Singleton a where 
    type Sing :: a -> *
    demote :: forall (x :: a) . Sing x -> a

  -- | The class of generatable singleton types
  -- 
  --   Captures those types of which we are able to generate values of the 
  --   associated singleton type. 
  class Singleton s => SingGeneratable s where 
    genSing :: forall (s' :: s) . G () (Sing s') (Sing s')

  -- | Associated singleton type for natural numbers
  data SNat (n :: Nat) where 
    SZero :: SNat Zero
    SSuc :: SNat n -> SNat (Suc n)

  -- | Singleton instance for natural numbers
  instance Singleton Nat where 
    type Sing = SNat
    demote SZero = Zero 
    demote (SSuc n) = Suc (demote n)

  -- | Second order singleton instance for natural numbers
  data SNat2 (n :: SNat m) where
    SZero2 :: SNat2 SZero 
    SSuc2  :: SNat2 sn -> SNat2 (SSuc sn)

  -- | Singleton instance for SNat
  instance Singleton (SNat n) where 
    type Sing = SNat2
    demote SZero2 = SZero 
    demote (SSuc2 n) = SSuc (demote n)

  -- | Singleton type for proxy's
  data SProxy (p :: Proxy a) where 
    SProxy_ :: SProxy ('Proxy :: Proxy a)

  infixr 5 :::~ 
  
  -- | Singleton type for vectors
  --   Note that the type of values that is contained 
  --   in the vector is required to be an instance of 
  --   'Singleton' as well. 
  data SVec (xs :: Vec a n) where 
    SVNil  :: SVec VNil 
    (:::~) :: Sing x -> SVec xs -> SVec (x ::: xs)

  -- | Type of promoted singleton values. We explicitly quantify over the 
  --   index of the singleton type, since otherwise we would not be able to 
  --   return singleton values with different indeces. I.e. the following 
  --   does not compile: 
  --   
  --   > promoteNat :: Nat -> Sing n
  --   > promoteNat Zero      = SZero 
  --   > promoteNat (SSuc n)  = Suc (promoteNat n)
  data Promoted (a :: *) (f :: a -> *) = forall (x :: a) . Promoted (f x)

  -- | Class of singleton types of which we can promote values to its
  --   associated singleton type. 
  class Singleton a => Promote a where 
    promote :: a -> Promoted a Sing

  -- | Promote instance for natural numbers. 
  instance Promote Nat where 
    promote Zero = Promoted SZero
    promote (Suc n) = 
      case promote n of 
        Promoted sn -> Promoted (SSuc sn) 

  data SUnit (u :: ()) where 
    SUnit_ :: SUnit '()

  instance Singleton () where 
    type Sing = SUnit 
    demote SUnit_ = ()
