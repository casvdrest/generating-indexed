{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module IDesc.IDesc2 where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics

  import Debug.Trace

  data E

  data Fin (n :: Nat) where
    Fz :: Fin (Suc n)
    Fs :: Fin n -> Fin (Suc n)

  data Vec (a :: *) :: Nat -> * where
    VNil :: Vec a Zero
    (:::) :: a -> Vec a n -> Vec a (Suc n)

  ---------------------------------------------------------------------------
  -- Singleton types

  class Singleton a where 
    type Sing :: a -> *
    demote :: forall (x :: a) . Sing x -> a
    promote :: forall (x :: a) . a -> Sing x

  class Singleton s => SingGeneratable s where 
    genSing :: forall (s' :: s) . G () (Sing s') (Sing s')

  data SNat (n :: Nat) where 
    SZero :: SNat Zero
    SSuc :: SNat n -> SNat (Suc n)

  data SNat2 (n :: SNat m) where
    SZero2 :: SNat2 SZero 
    SSuc2  :: SNat2 sn -> SNat2 (SSuc sn)

  data SProxy (p :: Proxy a) where 
    SProxy_ :: SProxy ('Proxy :: Proxy a)

  data SVec (xs :: Vec a n) where 
    SVNil  :: SVec VNil 
    (:::~) :: SingIDesc x -> SVec xs -> SVec (x ::: xs)
  
  ---------------------------------------------------------------------------
  -- Generation of common datatypes

  genBool :: G () Bool Bool
  genBool = pure True <|> pure False

  genNat :: G () Nat Nat
  genNat = pure Zero <|> Suc <$> mu ()

  instance Generatable Bool where
    gen = genBool

  instance Generatable Nat where
    gen = genNat

  instance Generatable () where
    gen = pure ()

  infixr 5 :::

  ---------------------------------------------------------------------------
  -- Singleton types

  class IndexedGeneratable a i where
    genIndexed :: i -> G i a a

  instance Generatable a => IndexedGeneratable a () where
    genIndexed () = gen

  data FTag = Plus
            | Choose
            | Equal
 
  class (Show i , Show o) => Solve (t :: FTag) i o where
    solve :: Proxy t -> o -> G () i i

  instance (Show a , Eq a) => Solve Equal () (a,a) where
    solve _ (x, y) | x == y    = pure ()
                   | otherwise = empty

  instance (Show a , Eq a) => Solve Choose a a where
    solve _ x = pure x 

  --------------------------------------------------------------------------
  -- Universe definition
  
  data IDesc (a :: *) (i :: *) where
    One    :: IDesc a i
    Empty  :: IDesc a i
    Var    :: i -> IDesc a i
    (:*:)  :: IDesc a i -> IDesc a i -> IDesc a i
    (:+>)  :: SNat n -> Vec (IDesc a i) n -> IDesc a i
    K      :: Proxy s -> IDesc a i
    Sigma  :: Proxy s -> IDesc a (s -> i) -> IDesc a i 

  type Func a i = i -> IDesc a i
  type UnProxy (p :: Proxy a) = a

  type family Interpret (d :: IDesc a i) :: *
  type instance Interpret One = ()
  type instance Interpret Empty = E
  type instance Interpret (Var _ :: IDesc i a) = a
  type instance Interpret (dl :*: dr) = (Interpret dl , Interpret dr)
  type instance Interpret (SZero :+> VNil) = E
  type instance Interpret (SSuc n :+> (x ::: xs)) = Either (Interpret x) (Interpret (n :+> xs))
  type instance Interpret (K p) = UnProxy p
  type instance Interpret (Sigma p fd) = (UnProxy p , Interpret fd)

  data (:~:) (a :: k1) (b :: k2) where 
    Refl :: a :~: a

  data SingIDesc (d :: IDesc i a) where 
    SOne   :: SingIDesc One
    SEmpty :: SingIDesc Empty 
    SVar   :: Sing i' -> SingIDesc (Var i')  
    (:*:~) :: SingIDesc l -> SingIDesc r -> SingIDesc (l :*: r)
    (:+>~) :: SNat2 n -> SVec xs -> SingIDesc (n :+> xs)
    SK     :: Generatable s => Proxy s -> SingIDesc (K ('Proxy :: Proxy s))
    SSigma :: SingGeneratable s => Proxy s -> SingIDesc d -> (Sing s' -> Interpret d :~: Interpret (Expand d s')) -> SingIDesc (Sigma ('Proxy :: Proxy s) d)  

  type family VExpand (sn :: SNat n) (xs :: Vec (IDesc a (s -> i)) n) (x :: s) :: Vec (IDesc a i) n
  type instance VExpand SZero VNil s = VNil
  type instance VExpand (SSuc sn) (x ::: xs) s = Expand x s ::: VExpand sn xs s

  type family Expand (d :: IDesc a (s -> i)) (x :: s) :: IDesc a i
  type instance Expand One s = One
  type instance Expand Empty s = Empty 
  type instance Expand (Var i) s = Var (i s)
  type instance Expand (dl :*: dr) s = (Expand dl s) :*: (Expand dr s)
  type instance Expand (sn :+> xs) s = sn :+> VExpand sn xs s 
  type instance Expand (K p) s = K p
  
  
  vexpand :: 
    forall (s :: *) (s' :: s) (sn :: SNat n) (xs :: Vec (IDesc a (s -> i)) n) .  
    (Singleton s) => SNat2 sn -> SVec xs -> Sing s' -> SVec (VExpand sn xs s')
  vexpand SZero2 SVNil s = SVNil 
  vexpand (SSuc2 sn) (x :::~ xs) s = expand x s :::~ vexpand sn xs s

  expand :: 
    forall (s :: *) (s' :: s) (d :: IDesc a (s -> i)) . (Singleton s) => 
    SingIDesc d -> Sing s' -> SingIDesc (Expand d s') 
  expand SOne sv = SOne
  expand SEmpty sv = SEmpty
  expand (SVar ix) sv = undefined
  expand (dl :*:~ dr) sv = expand dl sv :*:~ expand dr sv
  expand (sn :+>~ xs) sv = sn :+>~ vexpand sn xs sv

  eqConv :: a :~: b -> a -> b 
  eqConv Refl x = x

  sym :: a :~: b -> b :~: a 
  sym Refl = Refl

  ---------------------------------------------------------------------------
  -- Generic generator 

  idesc_gen :: 
    (Singleton i) => 
    forall (d :: IDesc i a) (d' :: IDesc i a) . 
    SingIDesc d -> SingIDesc d' -> G i (Interpret d') (Interpret d)
  idesc_gen SOne d' = pure ()
  idesc_gen SEmpty d' = G None
  idesc_gen (SVar p) d' = undefined 
  idesc_gen (dl :*:~ dr) d' = (,) <$> idesc_gen dl d' <*> idesc_gen dr d'
  idesc_gen (SZero2  :+>~ SVNil) d' = G None
  idesc_gen (SSuc2 n :+>~ (d :::~ ds)) d' =
    Left <$> idesc_gen d d' <|> Right <$> idesc_gen (n :+>~ ds) d'
  idesc_gen (SK p) d' = G (Call (\() -> unG gen) ()) 
  idesc_gen (SSigma Proxy f eq) d' = do 
    x <- G (Call (\() -> unG genSing) ())
    p <- idesc_gen (expand f x) d' 
    pure (demote x , eqConv (sym (eq x)) p) 
    