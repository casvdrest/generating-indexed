{-# LANGUAGE GADTs, RankNTypes, DeriveGeneric, DeriveAnyClass, UnicodeSyntax #-}

{-|
Module      : Gen
Description : The abstract type of generators
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

This module contains the definition of the type of abstract generators, which 
only mark the structure of a generator without making any choices of the type 
it will eventually be mapped to. They are an instance of Functor, Applicative, 
Monad and Alternative, with additional recursion and the possibility to refer
to the results of other generators. 
-}
module Gen where 

  import Generic.Depth
  import GHC.Generics
  import Control.Applicative
  import Unsafe.Coerce

  -- | The type of abstract generators 
  data Gen i t a where 
    None  ::                                   Gen i t a 
    Pure  :: a                              -> Gen i t a 
    Or    :: Gen i t a -> Gen i t a         -> Gen i t a 
    Ap    :: Gen i t (b -> a) -> Gen i t b  -> Gen i t a
    Bind  :: Gen i t a -> (a -> Gen i t b)  -> Gen i t b
    Mu    :: i                              -> Gen i t t
    Call  :: (j -> Gen j a a) -> j          -> Gen i t a

  type G i a = Gen i a a 
  type G_ a  = Gen () a a 

  -- | Typeclass for generatable non-indexed datatypes
  class Generatable a where 
    gen :: G_ a

  -- | Typeclass for generatable non-indexed function types
  class CoGeneratable a where 
    cogen :: (Generatable b) => G_ (a -> b)

  ----------------------------------------------------------------------------
  -- Typeclass instances
     
  instance Functor (Gen i t) where 
    fmap f = Ap (Pure f)

  instance Applicative (Gen i t) where
    pure   = Pure
    (<*>)  = Ap 

  instance Monad (Gen i t) where 
    return  = Pure 
    (>>=)   = Bind

  instance Alternative (Gen i t) where 
    empty     = None 
    (<|>)     = Or

  ----------------------------------------------------------------------------
  -- Smart constructors for generator compositions

  -- | denotes a recursive position - intended for use with lhs2TeX (where 'mu') is 
  --   turned into the greek letter mu. 
  mu :: i -> G i t
  mu = Mu

  -- | Calls a non indexed generator, omitting the need to work with the trival index
  call :: Generatable a => Gen () t a
  call = Call (trivial gen) ()

  -- | Lifts a value from 'a' to '() -> a' 
  trivial :: a -> () -> a 
  trivial = const

  -- | Marks choice over a list of options 
  --   TODO: use a tree-like structure instead of simply folding the list
  oneof :: [a] -> G i a 
  oneof = foldr1 (<|>) . map pure
