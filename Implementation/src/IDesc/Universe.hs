{-# LANGUAGE GADTs, TypeFamilies, DataKinds, MultiParamTypeClasses, FlexibleInstances, RankNTypes, PolyKinds, TypeOperators, ScopedTypeVariables #-}

{-|
Module      : Universe
Description : Universe definition of indexed descriptions
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

This module defines the universe of indexed descriptions (see 'A Cosmology of Datatypes' by Dagand)
as a haskell datatypes, together with its semantics and an appropriate singleton instance. Description
expansion maps descriptions whose index type is a function 's -> i' to a function from 's' to description, 
such that the semantics of the original description is the same for all possible values of type 's' applied
to its expansion. 
-}
module IDesc.Universe where

  import Data.Proxy
  import Gen
  import Generic.Depth
  import Datatypes
  import Singleton

  import Control.Applicative

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
  type instance Expand (Sigma p d) s = Sigma p (Expand d s)
  
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
  expand (SVar ix)    sv = SVar (ix (dm sv))
  expand (dl :*:~ dr) sv = expand dl sv :*:~ expand dr sv
  expand (sn :+>~ xs) sv = sn :+>~ vexpand sn xs sv

  ---------------------------------------------------------------------------
  -- Singleton types

  class IndexedGeneratable a i where
    genIndexed :: i -> G i a

  instance Generatable a => IndexedGeneratable a () where
    genIndexed () = gen

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
  type instance Interpret One                             = ()
  type instance Interpret Empty                           = E
  type instance Interpret (Var _ :: IDesc a i)            = a
  type instance Interpret (dl :*: dr)                     = (Interpret dl , Interpret dr)
  type instance Interpret (SZero :+> VNil)                = E
  type instance Interpret (SSuc SZero :+> (x ::: VNil))   = Interpret x
  type instance Interpret (SSuc (SSuc n) :+> (x ::: xs))  = Either (Interpret x) (Interpret (SSuc n :+> xs))
  type instance Interpret (K p _)                         = UnProxy p
  type instance Interpret (Sigma p fd)                    = (UnProxy p , Interpret fd)

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
    SSigma :: Promote s => SingIDesc d
      -> G_ s -> (forall s' . Sing s' -> Interpret d :~: Interpret (Expand d s')) 
      -> SingIDesc (Sigma ('Proxy :: Proxy s) d)  

  -- | Demote a value of type SingIDesc d to (d :: IDesc a i)
  demoteIDesc :: forall (d :: IDesc a i) . SingIDesc d -> IDesc a i 
  demoteIDesc SOne                        = One
  demoteIDesc SEmpty                      = Empty 
  demoteIDesc (SVar x)                    = Var x
  demoteIDesc (l :*:~ r)                  = demoteIDesc l :*: demoteIDesc r
  demoteIDesc (SZero2 :+>~ SVNil)         = SZero :+> VNil 
  demoteIDesc (SSuc2 sn :+>~ (x :::~ xs)) = 
    case demoteIDesc (sn :+>~ xs) of 
      (sn' :+> xs') -> 
        (SSuc sn' :+> (dm x ::: xs'))
  demoteIDesc (SK p p')                   = K p p'
  demoteIDesc (SSigma desc gen eq)        = Sigma Proxy (dm desc)

  instance Singleton (IDesc a i) where 
    type Sing = SingIDesc
    dm = demoteIDesc