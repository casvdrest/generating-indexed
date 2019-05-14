{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module IDesc.IDesc where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Data.Singletons
  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics

  import Debug.Trace

  ----------------------------------------------------------------------------
  -- Hide the type of a value
  data Anything = forall a . Hidden a

  -- | Singleton instance for Nat, used for generalised coproducts. 
  data instance Sing (n :: Nat) where
    SZero :: Sing Zero
    SSuc  :: Sing n -> Sing (Suc n)

  -- | Finite sets
  data Fin (n :: Nat) where
    Fz :: Fin (Suc n)
    Fs :: Fin n -> Fin (Suc n)

  -- | Length-indexed lists (vectors)
  data Vec (a :: *) :: Nat -> * where
    VNil :: Vec a Zero
    (:::) :: a -> Vec a n -> Vec a (Suc n)

  infixr 5 :::
  
  ----------------------------------------------------------------------------
  -- Generators for common types

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
  
  -- | Generation of indexed types
  class IndexedGeneratable a i where
    genIndexed :: i -> G i a a

  -- | Generatable, non-indexed datatypes are also generatable 
  --   indexed types (by trivially indexing them)
  instance Generatable a => IndexedGeneratable a () where
    genIndexed () = gen

  -- | Function tags -> used to select the correct reversal when solving sigma's
  data FTag = Plus
            | Choose
            | Equal
 
  -- | Functions (distinguished by FTag) of whom we can enumerate 
  --   the set of arguments that map to a given result. 
  class (Show i , Show o) => Solve (t :: FTag) i o where
    solve :: Proxy t -> o -> G () i i

  -- | Equality constraint. Yields a unit if the input values are equal, nothing otherwise
  instance (Show a , Eq a) => Solve Equal () (a,a) where
    solve _ (x, y) | x == y    = pure ()
                   | otherwise = empty

  -- | Chooses a value of the given type
  instance (Show a , Eq a) => Solve Choose a a where
    solve _ x = pure x 

  --------------------------------------------------------------------------
  -- Universe definition of indexed descriptions
  
  data IDesc (a :: *) (i :: *) where
    One    :: IDesc a i
    Empty  :: IDesc a i
    Var    :: i -> IDesc a i
    (:*:)  :: IDesc a i -> IDesc a i -> IDesc a i
    (:+>)  :: Sing n -> Vec (IDesc a i) n -> IDesc a i
    K      :: IndexedGeneratable s j => Proxy s -> (i -> j) -> IDesc a i
    Sigma  :: forall it ot a i (s :: FTag) . Solve s it ot =>
      Proxy s -> G () ot ot -> (it -> IDesc a i) -> IDesc a i 

  type Func a i = i -> IDesc a i

  ---------------------------------------------------------------------------
  -- Generic generator for indexed descriptions

  idesc_gen :: IDesc a i -> i -> G i Anything Anything
  idesc_gen One _ = pure (Hidden ())
  idesc_gen Empty _ = G None
  idesc_gen (Var i) _ = (\x (Hidden y) -> Hidden (x , y)) <$> pure i <*> G (Mu i)
  idesc_gen (SZero :+> VNil) _= G None
  idesc_gen (dl :*: dr) i =
      (\(Hidden x) (Hidden y) -> Hidden (x , y)) <$>
        idesc_gen dl i
    <*> idesc_gen dr i
  idesc_gen ((SSuc n) :+> (x ::: xs)) i =
        ((\(Hidden x) -> Hidden $ Left x)  <$> idesc_gen x i)
    <|> ((\(Hidden y) -> Hidden $ Right y) <$> idesc_gen (n :+> xs) i)
  idesc_gen (K (Proxy :: Proxy s) (j :: i -> jTy)) i = Hidden <$> G (Call (unG . gen) (j i))
    where gen :: jTy -> G jTy s s
          gen = genIndexed
  idesc_gen (Sigma ptag og f) i =
    do v  <- G (Call (\() -> unG og) ())
       iv <- G (Call (\() -> unG (solve ptag v)) ())
       idesc_gen (f iv) i

  -- | a type description consists of a function from index to description, and a 
  --   conversion function that describes how we can convert to the goal type. 
  data Description a i = Description
    { func   :: Func a i
    , to     :: i -> Anything -> a
    }

  -- | Composes a generator that generates all inhabitants of the fixed point of 
  --   a given description, and applies the accompanying conversion function to 
  --   those values. 
  genDesc :: forall a i . Description a i -> i -> G i a a
  genDesc desc x = to desc x <$> (G (Call (unG . genF) x))
    where genF :: i -> G i Anything Anything
          genF ix = idesc_gen (func desc ix) ix

  
  ---------------------------------------------------------------------------
  -- These are just there so that we purposefully convert to a certain goal 
  -- type when invoking unsafeCoerce ...
  
  asEither :: x -> Either a b
  asEither = unsafeCoerce

  asPair :: x -> (a , b)
  asPair = unsafeCoerce

  asUnit :: x -> ()
  asUnit = unsafeCoerce

  asNat :: x -> Nat
  asNat = unsafeCoerce

  asBool :: x -> Bool
  asBool = unsafeCoerce

  -- | Unpack a hidden value using a given conversion function. 
  unHidden :: (forall a . a -> b) -> Anything -> b
  unHidden f (Hidden x) = f x