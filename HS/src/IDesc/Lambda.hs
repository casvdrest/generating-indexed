{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module IDesc.Lambda where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Singleton
  import Data
  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics

  import IDesc.IDesc
  import IDesc.Instances
  import IDesc.Context

  ----------------------------------------------------------------------------
  -- Well typed terms

{-

  tyGen :: () -> G () Ty Ty
  tyGen () = pure T <|> (:->:) <$> mu () <*> mu ()

  idGen :: () -> G () Id Id
  idGen () = pure "aa" <|> pure "bb" <|> pure "cc"

  wttermFunc :: Func (Term String) (Ctx , Ty)
  wttermFunc (ctx , T)          =
    SSuc (SSuc SZero) :+>
      (   K (Proxy :: Proxy String) id
      ::: Sigma (Proxy :: Proxy Choose) (tyGen ()) (\ty -> Var (ctx , ty :->: T) :*: Var (ctx, ty))
      ::: VNil
      )
  wttermFunc (ctx , ty1 :->: ty2) =
    SSuc (SSuc (SSuc SZero)) :+>
      (   K (Proxy :: Proxy String) id
      ::: Sigma (Proxy :: Proxy Choose) (idGen ()) (\id -> Var (CtxCons id ty1 ctx , ty2))
      ::: Sigma (Proxy :: Proxy Choose)
            (tyGen ()) (\ty -> Var (ctx , ty :->: (ty1 :->: ty2)) :*: Var (ctx, ty))
      ::: VNil
      )

  toWtTerm :: (Ctx, Ty) -> Anything -> Term String
  toWtTerm (ctx, T) (Hidden x) =
    case asEither x of
      Left l   -> VarT l
      Right r -> 
        case asEither r of
          Left l' ->
            case asPair l' of
              ((i1 , t1) , (i2 , t2)) -> AppT
                (toWtTerm i1 (Hidden t1))
                (toWtTerm i2 (Hidden t2))
  toWtTerm (ctx, ty1 :->: ty2) (Hidden x) =
    case asEither x of
      Left l -> VarT l
      Right r ->
        case asEither r of
          Left ((CtxCons id' ty' ctx' , ty'') , t) ->
            AbsT id' (toWtTerm (CtxCons id' ty' ctx', ty'') (Hidden t))
          Right r' -> 
            case asEither r' of
              Left l'' ->
                case asPair l'' of
                  ((i1 , t1) , (i2 , t2)) -> AppT
                    (toWtTerm i1 (Hidden t1))
                    (toWtTerm i2 (Hidden t2))
                

  contains :: Ctx -> String -> Ty -> Bool
  contains CtxEmpty id ty = False
  contains (CtxCons id1 ty1 ctx) id2 ty2 = (ty1 == ty2 && id1 == id2) || contains ctx id2 ty2  

  well_typed :: Ctx -> Ty -> Term String -> Bool
  well_typed ctx ty (VarT x) = contains ctx x ty
  well_typed ctx (ty1 :->: ty2) (AbsT id tm) = well_typed (CtxCons id ty1 ctx) ty2 tm
  well_typed ctx ty (AppT tm1 tm2) =
    any (\sig -> well_typed ctx (sig :->: ty) tm1 && well_typed ctx sig tm2) (run tyGen () 4)
  well_typed ctx ty tm = False

  wtterm :: Description (Term String) (Ctx , Ty)
  wtterm = Description
    { func   = wttermFunc
    , to     = toWtTerm
    }

  runWtTermGen :: (Ctx, Ty) -> Int -> [Term String]
  runWtTermGen = run (genDesc wtterm)
  -}