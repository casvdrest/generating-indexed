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
{-# LANGUAGE TupleSections #-}

module IDesc.Lambda where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Singleton
  import Data
  import Control.Applicative
  import IDesc.Instances
  import Unsafe.Coerce

  import Data.List

  import IDesc.IDesc
  import IDesc.Term

  type P a = ('Proxy :: Proxy a)

  type VarDesc = Sigma (P CtxPos) One
  type AppDesc = Sigma (P Type) (Var I :*: Var I) 

  type family SLTCDesc (i :: (Ctx , Type)) :: IDesc Term (Ctx , Type)
  type instance SLTCDesc ('(,) ctx T) = 
    SSuc (SSuc SZero) :+> ( VarDesc ::: AppDesc ::: VNil )
  type instance SLTCDesc ('(,) ctx (t1 :-> t2)) = 
    SSuc (SSuc (SSuc SZero)) :+> 
      ( VarDesc ::: Var ('(,) (t1:ctx) t2) ::: AppDesc ::: VNil )

  type instance Desc T_WTTERM Term (Ctx , Type) i = SLTCDesc i

  sltcDesc :: Proxy T_WTTERM -> Sing i -> Sing (SLTCDesc i)
  sltcDesc _ (SPair sctx ST) = (SSuc2 (SSuc2 SZero2)) :+>~ 
    (    SSigma SOne (genElem (dm sctx) T) (\_ -> Refl) 
    :::~ SSigma (SVar (\sigma -> (dm sctx, (sigma :-> T))) :*:~ SVar ((dm sctx,))) genType (\_ -> Refl)
    :::~ SVNil)
  sltcDesc _ (SPair sctx (t1 :->$ t2)) = (SSuc2 (SSuc2 (SSuc2 SZero2))) :+>~ 
    (    SSigma SOne (genElem (dm sctx) (dm t1 :-> dm t2)) (\_ -> Refl) 
    :::~ SVar (dm t1 : dm sctx , dm t2)
    :::~ SSigma (SVar (\sigma -> (dm sctx, (sigma :-> (dm t1 :-> dm t2)))) :*:~ SVar ((dm sctx,))) genType (\_ -> Refl)
    :::~ SVNil)

  toTerm :: Proxy T_WTTERM -> Sing i -> Interpret (SLTCDesc i) -> Term
  toTerm _ (SPair sctx ST) (Left (n , ())) = TVar (toNat n)
  toTerm _ (SPair sctx ST) (Right (_ , (t1 , t2))) = TApp t1 t2
  toTerm _ (SPair sctx (_ :->$ _)) (Left (n , ())) = TVar (toNat n)
  toTerm _ (SPair sctx (_ :->$ _)) (Right (Left y)) = TAbs y
  toTerm _ (SPair sctx (_ :->$ _)) (Right (Right (_ , (t1 , t2)))) = TApp t1 t2 

  instance Describe T_WTTERM Term (Ctx , Type) where 
    sdesc = sltcDesc 
    to = toTerm

  termGen :: (Ctx , Type) -> G (Ctx , Type) Term Term
  termGen i = 
    case promote i of 
      (Promoted i') -> genDesc (Proxy :: Proxy T_WTTERM) i' 

  isApp :: Term -> Bool 
  isApp (TApp _ _ ) = True 
  isApp _ = False

  test :: [Term]
  test = {- foldl' (\b tm -> b && check [T , T :-> T] tm T) True -} run termGen ([T , T , T, T, T :-> T, T] , T :-> T) 3

  inContext :: Nat -> Ctx -> Type -> Bool
  inContext n [] _ = False 
  inContext Zero (t:ts) t' = t == t' 
  inContext (Suc n) (t:ts) t' = inContext n ts t'

  types :: Int -> [Type] 
  types = run (\() -> genType) ()

  check :: Ctx -> Term -> Type -> Bool 
  check ctx (TVar n )      ty            = inContext n ctx ty
  check ctx (TAbs tm)      (ty1 :-> ty2) = check (ty1:ctx) tm ty2
  check ctx (TApp tm1 tm2) ty            = any (\i -> any (\ty' -> check ctx tm1 (ty' :-> ty) && check ctx tm2 ty') (types i)) [1..3]
  check _   _              _             = False

  --                                          T -> T
  -- [y : T , z : T :-> T] |- (\x -> y) z
  tm1 :: Term 
  tm1 = TApp (TApp (TAbs (TVar Zero)) (TAbs (TVar (Suc Zero)))) (TVar (Suc Zero))