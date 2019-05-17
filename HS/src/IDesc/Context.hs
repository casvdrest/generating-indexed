{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module IDesc.Context where

  import Singleton 
  import IDesc.IDesc
  import Data.Proxy
  import Data
  import Gen

  data Symbol = Syma | Symb | Symc | Symd | Syme deriving (Eq)

  toChar :: Symbol -> Char 
  toChar Syma = 'a'
  toChar Symb = 'b' 
  toChar Symc = 'c' 
  toChar Symd = 'd' 
  toChar Syme = 'e' 

  symlistToString :: [Symbol] -> String 
  symlistToString = map toChar

  instance Show Symbol where 
    show = show . toChar

  type Id = [Symbol]

  data SSymbol :: Symbol -> * where 
    Sa :: SSymbol Syma
    Sb :: SSymbol Symb
    Sc :: SSymbol Symc
    Sd :: SSymbol Symd  
    Se :: SSymbol Syme 

  instance Singleton Symbol where 
    type Sing = SSymbol
    demote Sa = Syma 
    demote Sb = Symb 
    demote Sc = Symc 
    demote Sd = Symd

  instance Promote Symbol where
    promote Syma = Promoted Sa 
    promote Symb = Promoted Sb 
    promote Symc = Promoted Sc 
    promote Symd = Promoted Sd 

  data Ty = T | Ty :->: Ty deriving (Show , Eq)

  data STy :: Ty -> * where 
    ST   :: STy T 
    (:->$) :: STy ty1 -> STy ty2 -> STy (ty1 :->: ty2) 

  instance Singleton Ty where 
    type Sing = STy
    demote ST = T
    demote (ty1 :->$ ty2) = demote ty1 :->: demote ty2

  instance Promote Ty where 
    promote T = Promoted ST 
    promote (t1 :->: t2) = 
      case (promote t1 , promote t2) of 
        (Promoted t1' , Promoted t2') -> Promoted (t1' :->$ t2')

  data Ctx = CtxEmpty | CtxCons Id Ty Ctx deriving (Show , Eq)

  data SCtx :: Ctx -> * where 
    SCtxEmpty :: SCtx CtxEmpty
    SCtxCons :: Sing id -> Sing ty -> Sing ctx -> SCtx (CtxCons id ty ctx)

  instance Singleton Ctx where 
    type Sing = SCtx 
    demote SCtxEmpty            = CtxEmpty 
    demote (SCtxCons id ty ctx) = CtxCons (demote id) (demote ty) (demote ctx)

  instance Promote Ctx where 
    promote CtxEmpty = Promoted SCtxEmpty 
    promote (CtxCons id ty ctx) = 
      case promote id of 
        (Promoted id') -> 
          case promote ty of 
            (Promoted ty') -> 
              case promote ctx of 
                (Promoted ctx') -> Promoted (SCtxCons id' ty' ctx')

  ctxFromList :: [(Id , Ty)] -> Ctx
  ctxFromList []           = CtxEmpty
  ctxFromList ((id,ty):xs) = CtxCons id ty (ctxFromList xs)

  type family MemDesc (i :: (Ctx , Ty)) :: IDesc Id (Ctx, Ty)
  type instance MemDesc ('(,) CtxEmpty ty) = Empty
  type instance MemDesc ('(,) (CtxCons id ty' ctx) ty) = 
    SSuc (SSuc SZero) :+> 
    (   Sigma ('Proxy :: Proxy ()) One
    ::: Var ('(,) ctx ty)
    ::: VNil
    )
  
  type instance Desc T_CTXMEM Id (Ctx , Ty) i = MemDesc i

  memSDesc :: Proxy T_CTXMEM -> SPair i -> SingIDesc (MemDesc i) 
  memSDesc _ (SPair SCtxEmpty                sty) = SEmpty
  memSDesc _ (SPair (SCtxCons sid sty' sctx) sty) = 
    SSuc2 (SSuc2 SZero2) :+>~
    (    SSigma (Proxy :: Proxy ()) (Proxy :: Proxy GT_EQUAL) 
                SOne (const Refl) 
                (InPair' (demote sty') (demote sty)) 
    :::~ SVar (demote sctx , demote sty) 
    :::~ SVNil
    )
  
  toMem :: Proxy T_CTXMEM -> Sing i -> Interpret (MemDesc i) -> Id
  toMem _ (SPair (SCtxCons sid sty' sctx) sty) (Left (() , ())) = demote sid
  toMem _ (SPair (SCtxCons sid sty' sctx) sty) (Right y)        = y

  instance Describe T_CTXMEM Id (Ctx , Ty) where 
    sdesc = memSDesc
    to    = toMem

  ctx1 :: Ctx
  ctx1 = ctxFromList
    [ ([Syma] , T :->: T)
    , ([Symb] , T)
    , ([Symc] , T :->: (T :->: T))
    , ([Symd] , T)
    ]

  genMem :: (Ctx , Ty) -> G (Ctx, Ty) Id Id 
  genMem ix = 
    case promote ix of 
      Promoted ix' -> genDesc (Proxy :: Proxy T_CTXMEM) ix'

  instance IndexedGeneratable Id (Ctx, Ty) where 
    genIndexed = genMem
  
