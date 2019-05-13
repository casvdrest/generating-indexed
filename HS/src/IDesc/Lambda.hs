{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module IDesc.Lambda where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Data.Singletons
  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics

  import IDesc.IDesc
  import IDesc.Instances

  ----------------------------------------------------------------------------
  -- Well typed terms

  type Id = String

  data Ty = T | Ty :->: Ty deriving (Show , Eq)

  data Ctx = CtxEmpty | CtxCons Id Ty Ctx deriving (Show , Eq)

  ctxFromList :: [(Id , Ty)] -> Ctx
  ctxFromList []           = CtxEmpty
  ctxFromList ((id,ty):xs) = CtxCons id ty (ctxFromList xs)

  (!!~) :: Ctx -> Nat -> (Id , Ty)
  CtxEmpty            !!~ n       = error "cannot index empty context"
  (CtxCons id ty ctx) !!~ Zero    = (id , ty)
  (CtxCons id ty ctx) !!~ (Suc n) = ctx !!~ n

  memFunc :: Func String (Ctx , Ty)
  memFunc (CtxEmpty , ty) = Empty
  memFunc (CtxCons id ty1 ctx , ty2) =
    SSuc (SSuc SZero) :+>
    (   Sigma (Proxy :: Proxy Equal) (pure (ty1 , ty2)) (\() -> One)
    ::: Var (ctx , ty2)
    ::: VNil
    )

  toId :: (Ctx , Ty) -> Anything -> String
  toId (CtxCons id ty1 ctx , ty2) (Hidden x) =
    case asEither x of
      (Left l) ->
        case asUnit l of
          () -> id -- Top rule
      (Right r) ->
        case asEither r of
          (Left l') ->
            case asPair l' of
              (ix' , rc) -> toId ix' (Hidden rc)

  ctx1 :: Ctx
  ctx1 = ctxFromList
    [ ("a" , T :->: T)
    , ("b" , T)
    , ("c" , T :->: (T :->: T))
    , ("d" , T)
    ]

  mem :: Description String (Ctx , Ty)
  mem = Description
    { func = memFunc
    , to   = toId
    }

  instance IndexedGeneratable String (Ctx, Ty) where
    genIndexed = genDesc mem
    giMuConv _ = unHidden unsafeCoerce

  runMemGen :: (Ctx, Ty) -> Int -> [String]
  runMemGen = run (genDesc mem)

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
