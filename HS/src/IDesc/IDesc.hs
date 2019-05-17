{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module IDesc.IDesc where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Data
  import Singleton

  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics
  import Debug.Trace

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
    K      :: Proxy s -> j -> IDesc a i
    Sigma  :: Proxy s -> IDesc a (s -> i) -> IDesc a i 

  -- | Uncovers the type carried by a proxy  
  type UnProxy (p :: Proxy a) = a

  -- | Map a type to it's interpretation 
  type family Interpret (d :: IDesc a i) :: *
  type instance Interpret One                            = ()
  type instance Interpret Empty                          = E
  type instance Interpret (Var _ :: IDesc a i)           = a
  type instance Interpret (dl :*: dr)                    = (Interpret dl , Interpret dr)
  type instance Interpret (SZero :+> VNil)               = E
  type instance Interpret (SSuc SZero :+> (x ::: VNil))  = Interpret x
  type instance Interpret (SSuc (SSuc n) :+> (x ::: xs)) = Either (Interpret x) (Interpret (SSuc n :+> xs))
  type instance Interpret (K p _)                        = UnProxy p
  type instance Interpret (Sigma p fd)                   = (UnProxy p , Interpret fd)

  --------------------------------------------------------------------------
  -- Singleton Instance for Indexed Descriptions

  -- | Singleton type for indexed descriptions
  data SingIDesc (d :: IDesc a i) where 
    SOne   :: SingIDesc One
    SEmpty :: SingIDesc Empty 
    SVar   :: forall (i' :: i) . i -> SingIDesc (Var i')  
    (:*:~) :: SingIDesc l -> SingIDesc r -> SingIDesc (l :*: r)
    (:+>~) :: SNat2 n -> SVec xs -> SingIDesc (n :+> xs)
    SK     :: forall (j :: *) (j' :: j) . 
     (IndexedGeneratable s j , Singleton j)
      => Proxy s -> Sing j'
      -> SingIDesc (K ('Proxy :: Proxy s) j')
    SSigma :: TSingGeneratable t s 
      => Proxy s -> Proxy t -> SingIDesc d 
      -> (forall s' . Sing s' -> Interpret d :~: Interpret (Expand d s')) 
      -> InputType ('Proxy :: Proxy t)
      -> SingIDesc (Sigma ('Proxy :: Proxy s) d)  

  -- | Demote a value of type SingIDesc d to some IDesc a i
  demoteIDesc :: forall (d :: IDesc a i) . SingIDesc d -> IDesc a i 
  demoteIDesc SOne                        = One
  demoteIDesc SEmpty                      = Empty 
  demoteIDesc (SVar x)                    = Var x
  demoteIDesc (l :*:~ r)                  = demoteIDesc l :*: demoteIDesc r
  demoteIDesc (SZero2 :+>~ SVNil)         = SZero :+> VNil 
  demoteIDesc (SSuc2 sn :+>~ (x :::~ xs)) = 
    case demoteIDesc (sn :+>~ xs) of 
      (sn' :+> xs') -> 
        (SSuc sn' :+> (demote x ::: xs'))
  demoteIDesc (SK p p')                   = K p p'
  demoteIDesc (SSigma p p' desc eq _)          = Sigma p (demote desc)

  instance Singleton (IDesc a i) where 
    type Sing = SingIDesc
    demote = demoteIDesc

  --------------------------------------------------------------------------
  -- Description Expansions 

  -- | Map expansions over vectors
  type family VExpand (sn :: SNat n) (xs :: Vec (IDesc a (s -> i)) n) (x :: s) :: Vec (IDesc a i) n
  type instance VExpand SZero     VNil s       = VNil
  type instance VExpand (SSuc sn) (x ::: xs) s = Expand x s ::: VExpand sn xs s

  -- | Expand some description 'd :: IDesc a (s -> i)' to a "function" of type 
  --   s -> IDesc a i. 
  type family Expand (d :: IDesc a (s -> i)) (x :: s) :: IDesc a i
  type instance Expand One         s = One
  type instance Expand Empty       s = Empty 
  type instance Expand (Var i)     s = Var (i s)
  type instance Expand (dl :*: dr) s = (Expand dl s) :*: (Expand dr s)
  type instance Expand (sn :+> xs) s = sn :+> VExpand sn xs s 
  type instance Expand (K p sj)    s = K p sj
  
  -- | Map term level expansion over vectors
  vexpand :: 
    forall (s :: *) (s' :: s) (sn :: SNat n) (xs :: Vec (IDesc a (s -> i)) n) .  
    (Singleton s) => SNat2 sn -> SVec xs -> Sing s' -> SVec (VExpand sn xs s')
  vexpand SZero2     SVNil       s = SVNil 
  vexpand (SSuc2 sn) (x :::~ xs) s = expand x s :::~ vexpand sn xs s

  -- | Term level expansion of descriptions
  expand :: 
    forall (s :: *) (s' :: s) (d :: IDesc a (s -> i)) . (Singleton s) => 
    SingIDesc d -> Sing s' -> SingIDesc (Expand d s') 
  expand SOne         sv = SOne
  expand SEmpty       sv = SEmpty
  expand (SVar ix)    sv = SVar (ix (demote sv))
  expand (dl :*:~ dr) sv = expand dl sv :*:~ expand dr sv
  expand (sn :+>~ xs) sv = sn :+>~ vexpand sn xs sv

  ---------------------------------------------------------------------------
  -- Generic generator 

  -- | Derive a generator from a description
  idesc_gen :: forall (d :: IDesc a i) . (Singleton i) => SingIDesc d -> G i a (Interpret d)
  idesc_gen SOne                               = pure ()
  idesc_gen SEmpty                             = G None
  idesc_gen (SVar v)                           = mu v 
  idesc_gen (dl :*:~ dr)                       = (,) <$> idesc_gen dl <*> idesc_gen dr
  idesc_gen (SZero2 :+>~ SVNil)                = G None
  idesc_gen (SSuc2 SZero2 :+>~ (d :::~ SVNil)) = idesc_gen d
  idesc_gen (SSuc2 (SSuc2 n) :+>~ (d :::~ ds)) =
        Left  <$> idesc_gen d 
    <|> Right <$> idesc_gen (SSuc2 n :+>~ ds)
  idesc_gen (SK (Proxy :: Proxy s) sj) = G (Call (unG . genIndexed) (demote sj))
  idesc_gen (SSigma Proxy p f eq v)          = do 
    (Promoted x) <- G (Call (\() -> unG (taggedGen p v)) ())
    p <- idesc_gen (expand f x) 
    pure (demote x , eqConv (sym (eq x)) p) 
  
  -- | Maps a combination of tag, goal type and index to a description. 
  type family Desc (t :: DataTag) (a :: *) (i :: *) (i' :: i) :: IDesc a i

  -- | Class of types that can be described by an indexed description. 
  -- 
  --   Again, we carry around a 'DataTag' to disambiguate between indexed types
  --   that share the same goal type. 
  class Singleton i => Describe (t :: DataTag) (a :: *) (i :: *) where 
    sdesc :: Proxy t -> Sing i' -> SingIDesc (Desc t a i i')
    to    :: Proxy t -> Sing i' -> Interpret (Desc t a i i') -> a
  
  -- | Derive generators for types that are members of the 'Describe' class by using their associated 
  --   description to compose a generator. 
  genDesc :: forall a i t (i' :: i) . (Singleton i , Describe t a i ) => Proxy t -> Sing i' -> G i a a
  genDesc p (x :: Sing i') = 
    (to p x) <$> idesc_gen (sdesc p x :: SingIDesc (Desc t a i i')) 