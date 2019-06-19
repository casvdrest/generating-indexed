{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Singleton where

  import Data
  import Gen
  import Data.Proxy
  import Control.Applicative

  ---------------------------------------------------------------------------
  -- Singleton types

  -- | The class of types for which there exists a singleton type.
  --
  --   The associated type 'Sing :: a -> *' is the singleton type
  --   of a.
  --   'dm' describes how a value of type 'Sing x' can be converted
  --   to a value of type 'a' , for all 'x :: a'
  class Singleton a where
    type Sing :: a -> *
    dm :: forall (x :: a) . Sing x -> a

  -- | The class of generatable singleton types
  --
  --   Captures those types of which we are able to generate values of the
  --   associated singleton type.
  class Promote s => SingGeneratable s where
    genSing :: G () (Promoted s Sing) (Promoted s Sing)

    -- | Tags used to tag various indexed datatypes. We need this to
  --   distinguish between different indexed datatypes that are mapped
  --   to the same non-indexed datatype.
  data DataTag = T_FIN
               | T_VEC
               | T_WSTERM
               | T_CTXMEM
               | T_WTTERM
               | T_STREE
               | T_EXPR

  -- | Tags used to distinguish between different generators for the same type,
  --   in order to be able to seledct different generation strategies for
  --   generation of the first element of a Sigma.
  data GenTag = GT_INVERSEPLUS
              | GT_CHOOSE
              | GT_EQUAL

  class InType (t :: GenTag) where
    type InputType (p :: Proxy t) :: *

  -- | Class of tagged singleton generators
  class (Promote a, InType t) => TSingGeneratable (t :: GenTag) (a :: *) where
    taggedGen :: Proxy t -> InputType ('Proxy :: Proxy t) -> G () (Promoted a Sing) (Promoted a Sing)

  data Pair' = forall a . Eq a => InPair' a a

  instance InType GT_EQUAL where
    type InputType ('Proxy :: Proxy GT_EQUAL) = Pair'

  instance TSingGeneratable GT_EQUAL () where
    taggedGen _ (InPair' x y) | x == y    = pure (Promoted SUnit_)
                              | otherwise = empty

  instance InType GT_CHOOSE where 
    type InputType ('Proxy :: Proxy GT_CHOOSE) = ()

  instance (Promote a , SingGeneratable a) 
    => TSingGeneratable GT_CHOOSE a where 
    taggedGen _ () = genSing

  -- | Singleton generator for natural numbers
  instance SingGeneratable Nat where
    genSing :: G () (Promoted Nat SNat) (Promoted Nat SNat)
    genSing  =  (pure (Promoted SZero))
            <|> ((\(Promoted r) -> Promoted (SSuc r)) <$> mu ())

  -- | Singleton generators for pairs
  instance (SingGeneratable a , SingGeneratable b) => SingGeneratable (a , b) where
    genSing :: G () (Promoted (a, b) SPair) (Promoted (a, b) SPair)
    genSing = do
      Promoted x <- G $ Call (\() -> unG genSing) ()
      Promoted y <- G $ Call (\() -> unG genSing) ()
      pure (Promoted (SPair x y))

  -- | Singleton generators for lists 
  instance SingGeneratable a => SingGeneratable [a] where 
    genSing  =  pure (Promoted SNil) 
            <|> ((\(Promoted x) (Promoted xs) -> Promoted (SCons x xs)) 
                <$> (G $ Call (\() -> unG genSing) ()) <*> genSing)

  -- | Associated singleton type for natural numbers
  data SNat (n :: Nat) where
    SZero :: SNat Zero
    SSuc :: SNat n -> SNat (Suc n)

  -- | Singleton instance for natural numbers
  instance Singleton Nat where
    type Sing = SNat
    dm SZero = Zero
    dm (SSuc n) = Suc (dm n)

  -- | Second order singleton instance for natural numbers
  data SNat2 (n :: SNat m) where
    SZero2 :: SNat2 SZero
    SSuc2  :: SNat2 sn -> SNat2 (SSuc sn)

  -- | Singleton instance for SNat
  instance Singleton (SNat n) where
    type Sing = SNat2
    dm SZero2 = SZero
    dm (SSuc2 n) = SSuc (dm n)

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

  -- | Singleton datatype for unit/()
  data SUnit (u :: ()) where
    SUnit_ :: SUnit '()

  -- | Singleton instance for unit/()
  instance Singleton () where
    type Sing = SUnit
    dm SUnit_ = ()

  instance Promote () where
    promote () = Promoted SUnit_

  -- | Pair of singleton values
  data SPair :: (k1 , k2) -> * where
    SPair :: Sing a -> Sing b -> SPair ('(,) a b)

  -- | Singleton instance of pairs
  instance (Singleton a , Singleton b) => Singleton (a, b) where
    type Sing = SPair
    dm (SPair x y) = (dm x , dm y)

  -- | Promote instance of pairs
  instance (Promote a , Promote b) => Promote (a, b) where
    promote (x, y) =
      case promote x of
        (Promoted x') ->
          case promote y of
            (Promoted y') -> Promoted (SPair x' y')

  -- | Coproduct of singleton values
  data SEither :: Either k1 k2 -> * where
    SLeft  :: Sing x -> SEither (Left  x)
    SRight :: Sing y -> SEither (Right y)

  -- | Singleton instance for coproducts
  instance (Singleton a , Singleton b) => Singleton (Either a b) where
    type Sing = SEither
    dm (SLeft  x) = Left  (dm x)
    dm (SRight y) = Right (dm y)

  -- | Promote instance for coproducts
  instance (Promote a , Promote b) => Promote (Either a b) where
    promote (Left x)  =
      case promote x of
        (Promoted x') -> Promoted (SLeft x')
    promote (Right y) =
      case promote y of
        (Promoted y') -> Promoted (SRight y')

  -- | Singleton lists
  data SList :: [a] -> * where
    SNil  :: SList '[]
    SCons :: Sing x -> Sing xs -> SList (x ': xs)

  -- | Singleton instance for lists
  instance Singleton a => Singleton [a] where
    type Sing = SList
    dm SNil         = []
    dm (SCons x xs) = dm x : dm xs

  -- | Promote instance for lists
  instance Promote a => Promote [a] where
    promote [] = Promoted SNil
    promote (x:xs) =
      case promote x of
        (Promoted x') ->
          case promote xs of 
            (Promoted xs') ->
              Promoted (SCons x' xs')

  -- | Singleton type for 'Maybe'
  data SMaybe :: Maybe a -> * where
    SNothing :: SMaybe Nothing
    SJust    :: Sing x -> SMaybe (Just x)

  -- | Singleton instance for 'Maybe'
  instance Singleton a => Singleton (Maybe a) where
    type Sing = SMaybe
    dm (SNothing) = Nothing
    dm (SJust x)  = Just (dm x)

  -- | Promote instance for 'Maybe'
  instance Promote a => Promote (Maybe a) where
    promote Nothing  = Promoted SNothing
    promote (Just x) =
      case promote x of
        (Promoted x') -> Promoted (SJust x')

  data SBool :: Bool -> * where 
    STrue  :: SBool True 
    SFalse :: SBool False

  instance Singleton Bool where 
    type Sing = SBool 
    dm STrue  = True 
    dm SFalse = False

  instance Promote Bool where 
    promote True = Promoted STrue 
    promote False = Promoted SFalse

  type S0 = SZero 
  type S1 = SSuc SZero
  type S2 = SSuc (SSuc SZero)
  type S3 = SSuc (SSuc (SSuc SZero))
  type S4 = SSuc (SSuc (SSuc (SSuc SZero)))
  type S5 = SSuc (SSuc (SSuc (SSuc (SSuc SZero))))
  type S6 = SSuc (SSuc (SSuc (SSuc (SSuc (SSuc SZero)))))

  s0 = SZero2 
  s1 = SSuc2 SZero2
  s2 = SSuc2 (SSuc2 SZero2)
  s3 = SSuc2 (SSuc2 (SSuc2 SZero2))
  s4 = SSuc2 (SSuc2 (SSuc2 (SSuc2 SZero2)))
  s5 = SSuc2 (SSuc2 (SSuc2 (SSuc2 (SSuc2 SZero2))))
  s6 = SSuc2 (SSuc2 (SSuc2 (SSuc2 (SSuc2 (SSuc2 SZero2)))))
      
