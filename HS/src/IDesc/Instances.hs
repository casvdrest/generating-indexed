{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module IDesc.Instances where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Data.Singletons
  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics

  import IDesc.IDesc

  ----------------------------------------------------------------------------
  -- Finite sets

  finFunc :: Func Nat Nat
  finFunc Zero    = Empty
  finFunc (Suc n) =
    (SSuc (SSuc SZero)) :+>
    (   One
    ::: Var n
    ::: VNil
    )

  toFin :: Nat -> Anything -> Nat
  toFin (Suc n) (Hidden x) = 
    case asEither x of
      (Left _) -> Zero
      (Right x) ->
        case asEither x of
          (Left x) ->
            case asPair x of
              (n' , rc) -> Suc (toFin n' (Hidden rc))

  fin :: Description Nat Nat
  fin = Description
    { func   = finFunc
    , to     = toFin
    }

  instance IndexedGeneratable Nat Nat where
    genIndexed   = genDesc fin
    giMuConv   _ = unHidden asNat

  genFin :: Nat -> G Nat Nat Nat
  genFin = genDesc fin

  ----------------------------------------------------------------------------
  -- Vectors

  vecFunc :: Generatable a => Proxy a -> Func [a] Nat
  vecFunc _ Zero    = One
  vecFunc p (Suc n) = K p (const ()) :*: (Var n)

  toVec :: Nat -> Anything -> [a]
  toVec Zero (Hidden x) =
    case asUnit x of
      () -> []
  toVec (Suc n) (Hidden x) = error "should redefine" {-
    case asPair x of
      (a , b) -> a : (toVec n (Hidden b)) -}

  vec :: Generatable a => Description [a] Nat
  vec = Description
    { func   = vecFunc Proxy
    , to     = toVec
    }

  ----------------------------------------------------------------------------
  -- Well-scoped terms

  instance DepthCalc () where
    depth () = 0

  data Term a = VarT a
            | AbsT a (Term a)
            | AppT (Term a) (Term a)
            deriving (Show, Eq , Generics.Generic, DepthCalc)

  termFunc :: Func (Term Nat) Nat
  termFunc n =
    SSuc (SSuc (SSuc SZero)) :+>
    (   K (Proxy :: Proxy Nat) id
    ::: Var (Suc n)
    ::: Var n :*: Var n
    ::: VNil
    )

  toTerm :: Nat -> Anything -> Term Nat
  toTerm n (Hidden x) = 
    case asEither x of
      (Left a)  -> VarT (asNat a)
      (Right b) ->
        case asEither b of
          (Left t') ->
            case asPair t' of
              (n' , r) -> AbsT Zero (toTerm n' (Hidden r))
          (Right t') ->
            case asEither t' of
              (Left ts) ->
                case asPair ts of
                  (t1 , t2) ->
                    let (n1 , r1) = asPair t1 in
                    let (n2 , r2) = asPair t2 in 
                    AppT (toTerm n1 (Hidden r1)) (toTerm n2 (Hidden r2)) 

  term :: Description (Term Nat) Nat
  term = Description
     { func   = termFunc
    , to     = toTerm
    }

  termGen :: Nat -> G Nat (Term Nat) (Term Nat)
  termGen i = genDesc term i

  runTermGen :: Nat -> Int -> [(Term Nat)]
  runTermGen = run termGen

  instance Ord Nat where
    Zero <= n = True
    (Suc n) <= Zero = False
    (Suc n) <= Suc m = n <= m

  well_scoped :: (Term Nat) -> Bool
  well_scoped = well_scoped' Zero
    where well_scoped' :: Nat -> (Term Nat) -> Bool
          well_scoped' n (VarT n') = n' <= n
          well_scoped' n (AbsT _ t) = well_scoped' (Suc n) t
          well_scoped' n (AppT t1 t2) = well_scoped' n t1 && well_scoped' n t2

  ----------------------------------------------------------------------------
  -- Rose Trees

  data Rose a = a :> [Rose a] deriving (Show)

  data RLabel = RL | RT

  asLabel :: Anything -> RLabel
  asLabel (Hidden x) = unsafeCoerce x

  data RoseTree' a = RoseNode' a (RoseTree' a)
                   | RoseNil'
                   | RoseCons' (RoseTree' a) (RoseTree' a)

  genRose' :: Generatable a => RLabel -> G RLabel (RoseTree' a) (RoseTree' a)
  genRose' RL = pure RoseNil' <|> RoseCons' <$> mu RT <*> mu RL
  genRose' RT = RoseNode' <$> G (Call (\() -> unG gen) ()) <*> mu RL

  toRose :: RoseTree' a -> Rose a
  toRose (RoseNode' v rs) = v :> toRose' rs 

  toRose' :: RoseTree' a -> [Rose a]
  toRose' RoseNil' = []
  toRose' (RoseCons' x xs) = toRose x : toRose' xs

  genRose :: Generatable a => RLabel -> G RLabel (Rose a) (Rose a)
  genRose l = toRose <$> (G (Call undefined RT))

  runRoseGen :: Int -> [Rose Bool]
  runRoseGen = run genRose RT

  ----------------------------------------------------------------------------
  -- Sized Trees

  data Tree = Leaf
            | Node Tree Tree
            deriving (Eq , Show)

  treeFunc :: Func Tree Nat
  treeFunc Zero    = One
  treeFunc (Suc n) = Sigma (Proxy :: Proxy Plus) (pure n) (\(n' , m') -> Var n' :*: Var m') 

  reversePlus :: Nat -> G () (Nat, Nat) (Nat , Nat)
  reversePlus Zero = pure (Zero , Zero)
  reversePlus (Suc n) =  pure (Suc n , Zero)
                     <|> ((\(x, y) -> (x , Suc y)) <$> reversePlus n)

  instance Solve Plus (Nat , Nat) Nat where
    solve _ = reversePlus

  toTree :: Nat -> Anything -> Tree
  toTree Zero _ = Leaf
  toTree (Suc n) (Hidden x) =
    case asPair x of
      (a , b) ->
        case asPair a of
          (ix1 , v1) -> 
            case asPair b of
              (ix2 , v2) -> Node (toTree ix1 (Hidden v1)) (toTree ix2 (Hidden v2))

  tree :: Description Tree Nat
  tree = Description
    { func   = treeFunc
    , to     = toTree
    }

  runTreeGen :: Nat -> Int -> [Tree]
  runTreeGen = run (genDesc tree)
