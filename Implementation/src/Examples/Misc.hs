{-# LANGUAGE DataKinds, MultiParamTypeClasses, FlexibleInstances, DeriveGeneric, DeriveAnyClass, RankNTypes, PolyKinds, TypeOperators, TypeFamilies, GADTs, UndecidableInstances, ScopedTypeVariables #-}

{-|
Module      : Mics
Description : Various generators
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

This module contains generators for various types, of which some are indexed. 
-}
module Examples.Misc where

  import Data.Proxy
  import Gen
  import Interpret
  import Generic.Depth
  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics

  import Singleton 
  import Datatypes

  import IDesc.Universe
  import IDesc.Generator

  ----------------------------------------------------------------------------
  -- Finite sets

  -- Just for reference, the GADT we're representing generically here 
  data Fn (n :: Nat) :: * where 
    FZ :: Fn Zero 
    FSuc :: Fn n -> Fn (Suc n)

  -- | Type level description of the 'Fin' type
  type family FinDesc (n :: Nat) :: IDesc Nat Nat 
  type instance FinDesc Zero    = Empty
  type instance FinDesc (Suc n) = (SSuc (SSuc SZero)) :+> (One ::: Var n ::: VNil)

  type instance Desc T_FIN Nat Nat i = FinDesc i

  -- | Term level description of the 'Fin' type. 
  finSDesc :: Proxy T_FIN -> Sing n -> SingIDesc (FinDesc n)
  finSDesc _ SZero    = SEmpty 
  finSDesc _ (SSuc n) = SSuc2 (SSuc2 SZero2) :+>~ (SOne :::~ SVar (dm n) :::~ SVNil)

  -- | Convert a generic representation back into a valule of type 'Fin'
  toFin :: Proxy T_FIN -> Sing n -> Interpret (FinDesc n) -> Nat 
  toFin _ (SSuc sn) (Left ()) = Zero 
  toFin _ (SSuc sn) (Right n) = Suc n 

  -- | 'Describe' instance for finite setss
  instance Describe T_FIN Nat Nat where 
    sdesc = finSDesc
    to    = toFin

  -- | Generator producing values inhabiting a finite set
  genFin :: forall (n :: Nat) . Nat -> G Nat Nat 
  genFin n = 
    case promote n of 
      (Promoted sn) -> genDesc (Proxy :: Proxy T_FIN) sn

  instance IndexedGeneratable Nat Nat where 
    genIndexed = genFin

  ----------------------------------------------------------------------------
  -- Vectors

  -- For reference, the GADT we're representing here
  data Vect (a :: *) :: Nat -> * where 
    VEmpy :: Vect a Zero 
    VCons :: a -> Vect a n -> Vect a (Suc n) 

  -- | Type level description of vectors
  type family VecDesc (a :: *) (n :: Nat) :: IDesc [a] Nat
  type instance VecDesc a Zero    = One
  type instance VecDesc a (Suc n) = K ('Proxy :: Proxy a) '() :*: (Var n)

  type instance Desc T_VEC [a] Nat i = VecDesc a i

  -- | Term level descriptions of vectors
  vecSDesc :: Generatable a => Proxy a -> Proxy T_VEC -> Sing n -> SingIDesc (VecDesc a n)
  vecSDesc _ _ SZero    = SOne
  vecSDesc p _ (SSuc n) = SK p SUnit_ :*:~ SVar (dm n)

  -- | Convert a generic representation back into a vector
  toVec :: Generatable a => Proxy a -> Proxy T_VEC -> Sing n -> Interpret (VecDesc a n) -> [a]
  toVec _ _ SZero ()          = []
  toVec _ _ (SSuc n) (x , xs) = x : xs

  -- | 'Describe' instance for vectors
  instance Generatable a => Describe T_VEC [a] Nat where 
    sdesc = vecSDesc Proxy
    to    = toVec Proxy

  -- | Generator producing vectors of a given length. 
  genVec :: forall a (n :: Nat) . Generatable a => Nat -> G Nat [a]
  genVec n = 
    case promote n of 
      (Promoted sn) -> genDesc (Proxy :: Proxy T_VEC) sn

  ----------------------------------------------------------------------------
  -- Sized Trees

  -- | Binary trees
  data Tree = Leaf
            | Node Tree Tree
            deriving (Eq , Show)

  -- | Type level dummy used to represent indices that may depend on 
  --   the first element of a dependent pair. 
  type family I :: a -> b

  -- | Type level description of size indexed binary trees
  type family STreeDesc (n :: Nat) :: IDesc Tree Nat
  type instance STreeDesc Zero = One  
  type instance STreeDesc (Suc n) = Sigma ('Proxy :: Proxy (Nat , Nat)) (Var I :*: Var I)

  type instance Desc T_STREE Tree Nat n = STreeDesc n

  -- | Term level description of size indexed binary trees. 
  sTreeSDesc :: Proxy T_STREE -> Sing n -> SingIDesc (STreeDesc n)
  sTreeSDesc _ SZero    = SOne
  sTreeSDesc _ (SSuc n) = 
     SSigma (SVar fst :*:~ SVar snd) (reversePlus (dm n))
     (\_ -> Refl)
 
  -- | Convert a generic representation back to a size indexed binary tree
  toTree :: Proxy T_STREE -> Sing n -> Interpret (STreeDesc n) -> Tree 
  toTree _ SZero ()               = Leaf
  toTree _ (SSuc n) (_ , (l , r)) = Node l r

  -- | 'Describe' instance for size indexed binary trees
  instance Describe T_STREE Tree Nat where 
    sdesc = sTreeSDesc
    to    = toTree

   -- | Generator producing size indexed binary trees
  genSTree :: Nat -> G Nat Tree
  genSTree n =
    case promote n of 
      (Promoted n') -> genDesc (Proxy :: Proxy T_STREE) n' 

  -- | Function generating all possible decompositions an index. 
  reversePlus :: Nat -> G () (Nat, Nat)
  reversePlus Zero = pure (Zero , Zero)
  reversePlus (Suc n) =  pure (Suc n , Zero)
                      <|> ((\(x, y) -> (x , Suc y)) <$> reversePlus n)
            
  ----------------------------------------------------------------------------
  -- Rose Trees, poc for mutual recursion

  -- Rose trees
  data Rose a = a :> [Rose a] deriving (Show)

  data RLabel = RL | RT

  -- | For reference, the GADT representing rose trees we use to 
  --   generate rose trees
  data GRose (a :: *) :: RLabel -> * where 
    RoseNode :: a -> (GRose a RL) -> GRose a RT
    RoseNil  :: GRose a RL 
    RoseCons :: GRose a RT -> GRose a RL -> GRose a RL

  -- | Single type representing rose trees, with the label index 
  --   erased. Note that this implies that a correct recursive 
  --   structure of values is no longer guaranteed by Haskell's 
  --   type system!
  data RoseTree' a = RoseNode' a (RoseTree' a)
                   | RoseNil'
                   | RoseCons' (RoseTree' a) (RoseTree' a)

  -- | Generator producting rose trees
  genRose' :: Generatable a => RLabel -> G RLabel (RoseTree' a)
  genRose' RL = pure RoseNil' <|> RoseCons' <$> mu RT <*> mu RL
  genRose' RT = RoseNode' <$> Call (trivial gen) () <*> mu RL
  toRose :: RoseTree' a -> Rose a
  toRose (RoseNode' v rs) = v :> toRose' rs 

  toRose' :: RoseTree' a -> [Rose a]
  toRose' RoseNil' = []
  toRose' (RoseCons' x xs) = toRose x : toRose' xs

  genRose :: Generatable a => RLabel -> G RLabel (Rose a)
  genRose l = toRose <$> (Call genRose' RT)

  runRoseGen :: Generatable a => BoundedList (Rose a)
  runRoseGen = interpret genRose RT
  
  -- Misc generators 

  genNat :: G_ Nat 
  genNat = pure Zero <|> Suc <$> mu ()

  genBool :: G_ Bool 
  genBool = pure True <|> pure False
  
  -- | Generatable instance for natural numbers
  instance Generatable Nat where 
    gen = genNat 

  -- | Generatable instance for boolean
  instance Generatable Bool where 
    gen = genBool
  