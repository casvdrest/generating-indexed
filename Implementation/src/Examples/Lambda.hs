{-# LANGUAGE DataKinds, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, KindSignatures, TypeFamilies, TypeOperators, GADTs, RankNTypes, UndecidableInstances, PolyKinds, TupleSections #-}

{-|
Module      : Lambda
Description : Example generator producting simply typed lambda terms. 
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

In this module we define a description for well typed terms in the simply typed lambda calculs, 
and use this description to define a generator that produces raw terms that are well typed. 
-}
module Examples.Lambda where

  import Data.Proxy
  import Gen
  import Interpret
  import Generic.Depth
  import Singleton
  import Datatypes
  import Control.Applicative
  import Examples.Misc

  import Data.List

  import IDesc.Universe
  import IDesc.Generator
  import Examples.Term

  -- | A shorthand for type level proxy's carrying a type. 
  type P a = ('Proxy :: Proxy a)

  -- | Type level description of the variable constructor
  type VarDesc = Sigma (P CtxPos) One

  -- | Type level description of the application constructor
  type AppDesc = Sigma (P Type) (Var I :*: Var I) 

  -- | Description for well-typed terms. 
  type family SLTCDesc (i :: (Ctx , Type)) :: IDesc Term (Ctx , Type)

  -- | If the index type is a ground type, terms can only be constructed 
  --   using the variable or application rule
  type instance SLTCDesc ('(,) ctx T) = 
    SSuc (SSuc SZero) :+> ( VarDesc ::: AppDesc ::: VNil )

  -- | If the index type is a function type, the term could have been constructed using 
  --   the variable, abstraction or application rule
  type instance SLTCDesc ('(,) ctx (t1 :-> t2)) = 
    SSuc (SSuc (SSuc SZero)) :+> 
      ( VarDesc ::: Var ('(,) (t1:ctx) t2) ::: AppDesc ::: VNil )

  -- | 'Desc' instance for well-typed terms
  type instance Desc T_WTTERM Term (Ctx , Type) i = SLTCDesc i

  -- | Singleton value describing well-typed terms
  sltcDesc :: Proxy T_WTTERM -> Sing i -> Sing (SLTCDesc i)
  sltcDesc _ (SPair sctx ST) = (SSuc2 (SSuc2 SZero2)) :+>~ 
    (    SSigma SOne (genElem (dm sctx) T) (\_ -> Refl) 
    :::~ SSigma (SVar (\sigma -> (dm sctx, (sigma :-> T))) :*:~ SVar ((dm sctx,))) 
                genType (\_ -> Refl)
    :::~ SVNil)
  sltcDesc _ (SPair sctx (t1 :->$ t2)) = (SSuc2 (SSuc2 (SSuc2 SZero2))) :+>~ 
    (    SSigma SOne (genElem (dm sctx) (dm t1 :-> dm t2)) (\_ -> Refl) 
    :::~ SVar (dm t1 : dm sctx , dm t2)
    :::~ SSigma (SVar (\sigma -> (dm sctx, (sigma :-> (dm t1 :-> dm t2)))) :*:~ SVar ((dm sctx,))) 
                genType (\_ -> Refl)
    :::~ SVNil)

  -- | Conversion function converting interpretations of the description for well-typed 
  --   terms to raw terms
  toTerm :: Proxy T_WTTERM -> Sing i -> Interpret (SLTCDesc i) -> Term
  toTerm _ (SPair sctx ST) (Left (n , ())) = TVar (toNat n)
  toTerm _ (SPair sctx ST) (Right (_ , (t1 , t2))) = TApp t1 t2
  toTerm _ (SPair sctx (_ :->$ _)) (Left (n , ())) = TVar (toNat n)
  toTerm _ (SPair sctx (_ :->$ _)) (Right (Left y)) = TAbs y
  toTerm _ (SPair sctx (_ :->$ _)) (Right (Right (_ , (t1 , t2)))) = TApp t1 t2 

  -- | 'Describe' instance for well typed terms
  instance Describe T_WTTERM Term (Ctx , Type) where 
    sdesc = sltcDesc 
    to    = toTerm

  -- | Term generator that produces raw terms using the description
  --   for well-typed terms. All generated terms are well typed in 
  --   STLC. 
  termGen :: (Ctx , Type) -> G (Ctx , Type) Term
  termGen i = 
    case promote i of 
      (Promoted i') -> genDesc (Proxy :: Proxy T_WTTERM) i' 

