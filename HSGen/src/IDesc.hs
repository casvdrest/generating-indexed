{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module IDesc where

  import Data.Proxy
  import Gen
  import Enumerate
  import Data.Singletons
  import Control.Applicative
  import Unsafe.Coerce

  data Nat = Zero | Suc Nat deriving Show

  data instance Sing (n :: Nat) where
    SZero :: Sing Zero
    SSuc  :: Sing n -> Sing (Suc n)

  data Fin (n :: Nat) where
    Fz :: Fin (Suc n)
    Fs :: Fin n -> Fin (Suc n)

  data Vec (a :: *) :: Nat -> * where
    VNil :: Vec a Zero
    (:::) :: a -> Vec a n -> Vec a (Suc n)

  infixr 5 :::

  --------------------------------------------------------------------------
  -- Universe definition
  
  data IDesc (a :: *) (i :: *) where
    One    ::  IDesc a i
    Empty  ::  IDesc a i
    Var    ::  i -> IDesc a i
    (:*:)  ::  IDesc a i -> IDesc a i -> IDesc a i
    (:+>)  ::  Sing n -> Vec (IDesc a i) n -> IDesc a i
    K      ::  Generatable s => Proxy s -> IDesc a i

  type Func a i = i -> IDesc a i

  ---------------------------------------------------------------------------
  -- Generic generator 

  data Ex = forall a . Ex a

  newtype CG a = CG (Gen a a)

  idesc_gen :: IDesc a i -> Func a i -> G Ex Ex
  idesc_gen One f = pure (Ex ())
  idesc_gen Empty f = G None
  idesc_gen (Var i) f = idesc_gen (f i) f
  idesc_gen (SZero :+> VNil) f = G None
  idesc_gen (dl :*: dr) f =
      (\(Ex x) (Ex y) -> Ex (x , y)) <$>
        idesc_gen dl f
    <*> idesc_gen dr f
  idesc_gen ((SSuc n) :+> (x ::: xs)) f =
        ((\(Ex x) -> Ex $ Left x)  <$> idesc_gen x f)
    <|> ((\(Ex y) -> Ex $ Right y) <$> idesc_gen (n :+> xs) f)
  idesc_gen (K (Proxy :: Proxy s)) f = Ex <$> G (Call (unG ext))
    where ext :: G s s
          ext = call

  data Description a i = Description
    { func :: Func a i
    , to   :: i -> Ex -> a
    }

  genDesc :: Description a i -> i -> G a a
  genDesc desc x = to desc x <$> (G (Call (unG ggen)))
    where ggen :: G Ex Ex
          ggen = idesc_gen (func desc x) (func desc)
 
  asEither :: x -> Either a b
  asEither = unsafeCoerce

  asPair :: x -> (a , b)
  asPair = unsafeCoerce

  asUnit :: x -> ()
  asUnit = unsafeCoerce

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

  toFin :: Nat -> Ex -> Nat
  toFin (Suc n) (Ex x) =
    case asEither x of
      (Left _) -> Zero
      (Right x) ->
        case asEither x of
          (Left x) -> Suc (toFin n (Ex x))

  fin :: Description Nat Nat
  fin = Description
    { func = finFunc
    , to   = toFin
    }

  ----------------------------------------------------------------------------
  -- Vectors

  genBool :: G Bool Bool
  genBool = pure True <|> pure False

  instance Generatable Bool where
    gen = genBool

  vecFunc :: Generatable a => Proxy a -> Func [a] Nat
  vecFunc _ Zero    = One
  vecFunc p (Suc n) = K p :*: (Var n)

  toVec :: Nat -> Ex -> [a]
  toVec Zero (Ex x) =
    case asUnit x of
      () -> []
  toVec (Suc n) (Ex x) =
    case asPair x of
      (a , b) -> a : (toVec n (Ex b))

  vec :: Generatable a => Description [a] Nat
  vec = Description
    { func = vecFunc Proxy
    , to   = toVec
    }

  
