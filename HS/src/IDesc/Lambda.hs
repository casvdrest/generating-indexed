{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}

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

  tyGen :: () -> G () Ty Ty
  tyGen () = pure T <|> (:->:) <$> mu () <*> mu ()

  idGen :: G () Id Id
  idGen = pure [Syma, Syma] <|> pure [Symb,  Symb] <|> pure [Symc , Symc]

  instance Generatable Id where 
    gen = idGen

  type family WTTermDesc (i :: (Ctx, Ty)) :: IDesc (Term Id) (Ctx , Ty)
  type instance WTTermDesc ('(,) ctx T) = 
    SSuc (SSuc SZero) :+> 
      (   K ('Proxy :: Proxy Id) ('(,) ctx T)
      ::: Sigma ('Proxy :: Proxy Ty) (Var I :*: Var I) 
      ::: VNil )
  type instance WTTermDesc ('(,) ctx (ty1 :->: ty2)) = 
    SSuc (SSuc (SSuc SZero)) :+> 
      (   K ('Proxy :: Proxy Id) ('(,) ctx (ty1 :->: ty2)) 
      ::: Sigma ('Proxy :: Proxy Id) (Var I)
      ::: Sigma ('Proxy :: Proxy Ty) (Var I :*: Var I) 
      ::: VNil ) 

  type instance Desc T_WTTERM (Term Id) (Ctx , Ty) i = WTTermDesc i

  wtTermSDesc :: Proxy T_WTTERM -> Sing i -> SingIDesc (WTTermDesc i)
  wtTermSDesc _ (SPair sctx ST) = 
    SSuc2 (SSuc2 SZero2) :+>~ 
      (    SK (Proxy :: Proxy Id) (SPair sctx ST)
      :::~ SSigma (Proxy :: Proxy Ty) (Proxy :: Proxy GT_CHOOSE) 
            (SVar (\ty' -> (demote sctx , ty' :->: T)) :*:~ SVar (\ty' -> (demote sctx , ty'))) 
            (\_ -> Refl) () 
      :::~ SVNil )
  wtTermSDesc _ (SPair sctx (sty1 :->$ sty2)) = 
    SSuc2 (SSuc2 (SSuc2 SZero2)) :+>~ 
      (    SK (Proxy :: Proxy Id) (SPair sctx (sty1 :->$ sty2))
      :::~ choose @Id (SVar (\id -> (CtxCons id (demote sty1) (demote sctx) , demote sty2))) (\_->Refl)
      :::~ choose @Ty (SVar (\ty' -> (demote sctx , ty' :->: (demote sty1 :->: demote sty2))) :*:~ SVar (\ty' -> (demote sctx , ty'))) (\_->Refl)
      :::~ SVNil )

  toWtTerm :: Proxy T_WTTERM -> Sing i -> Interpret (WTTermDesc i) -> Term Id 
  toWtTerm _ (SPair sctx ST) (Left x)  = VarT x
  toWtTerm _ (SPair sctx ST) (Right (p , (t1 , t2))) = AppT t1 t2
  toWtTerm _ (SPair sctx (sty1 :->$ sty2)) (Left x) = VarT x 
  toWtTerm _ (SPair sctx (sty1 :->$ sty2)) (Right (Left (id, tm))) = AbsT id tm
  toWtTerm _ (SPair sctx (sty1 :->$ sty2)) (Right (Right (p , (t1 , t2)))) = AppT t1 t2 


  choose :: forall a d . SingGeneratable a => SingIDesc d -> (forall s' . Sing s' -> Interpret d :~: Interpret (Expand d s')) -> SingIDesc (Sigma ('Proxy :: Proxy a) d) 
  choose desc p = SSigma (Proxy :: Proxy a) (Proxy :: Proxy GT_CHOOSE) desc p ()
    where tyProx :: Proxy a 
          tyProx = Proxy

  instance Describe T_WTTERM (Term Id) (Ctx , Ty) where 
    sdesc = wtTermSDesc 
    to = toWtTerm

  wtTermGen :: (Ctx , Ty) -> G (Ctx , Ty) (Term Id) (Term Id)
  wtTermGen i = 
    case promote i of 
      (Promoted i') -> genDesc (Proxy :: Proxy T_WTTERM) i' 