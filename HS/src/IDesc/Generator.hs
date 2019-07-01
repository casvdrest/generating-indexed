{-# LANGUAGE GADTs, TypeFamilies, DataKinds, MultiParamTypeClasses, FlexibleInstances, RankNTypes, PolyKinds, TypeOperators, ScopedTypeVariables #-}

{-|
Module      : Generator
Description : Generic generator for indexed descriptions
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

This module describes how an abstract generator can be derived for codes in the 
universe of indexed descriptions, that produce values of the type that is 
represented by the code. Required input by the user is a description of the 
type, and a conversion function that describes how values that live in the type
dictated by the semantics to the described types. 
-}
module IDesc.Generator where 

  import Datatypes 
  import Singleton
  import IDesc.Universe
  import Gen
  import Data.Proxy

  import Control.Applicative

  -- | Derive a generator from a description
  idesc_gen :: forall (d :: IDesc a i) . (Singleton i) => SingIDesc d -> Gen i a (Interpret d)
  idesc_gen SOne                               = pure ()
  idesc_gen SEmpty                             = empty
  idesc_gen (SVar v)                           = mu v
  idesc_gen (dl :*:~ dr)                       = (,) <$> idesc_gen dl <*> idesc_gen dr
  idesc_gen (SZero2 :+>~ SVNil)                = empty
  idesc_gen (SSuc2 SZero2 :+>~ (d :::~ SVNil)) = idesc_gen d
  idesc_gen (SSuc2 (SSuc2 n) :+>~ (d :::~ ds)) =
        Left  <$> idesc_gen d 
    <|> Right <$> idesc_gen (SSuc2 n :+>~ ds)
  idesc_gen (SK (Proxy :: Proxy s) sj) = (Call genIndexed (dm sj))
  idesc_gen (SSigma desc gen eq)               = do 
    x <- Call (trivial gen) ()
    let px = promote x
    case px of 
      Promoted x' -> do 
        p <- idesc_gen (expand desc x')
        -- Use an equality type to coerce the generated value. 
        pure (x , eqConv (sym (eq x')) p)
  
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
  genDesc :: forall a i t (i' :: i) . (Singleton i , Describe t a i ) => Proxy t -> Sing i' -> G i a
  genDesc p (x :: Sing i') = 
    (to p x) <$> idesc_gen (sdesc p x :: SingIDesc (Desc t a i i')) 