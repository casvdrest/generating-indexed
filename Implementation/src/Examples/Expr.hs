{-# LANGUAGE DataKinds, GADTs, TypeFamilies, KindSignatures, PolyKinds, TypeOperators, RankNTypes, MultiParamTypeClasses #-}

{-|
Module      : Expr
Description : Generation of well typed expressions
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

uses the universe of indexed description to generate well typed expressins
-}
module Expr where 

  import Data.Proxy
  import Gen
  import Interpret
  import Generic.Depth
  import Singleton
  import Datatypes
  import Examples.Misc
  import Control.Applicative
  import Unsafe.Coerce

  import IDesc.Universe
  import IDesc.Generator

  -- | The type of expressions
  data Type = Nat | Bool 

  -- | Singleton type for expression types
  data SType :: Type -> * where 
    SNat  :: SType 'Nat 
    SBool :: SType 'Bool
  
  -- | Singleton instance for expression type
  instance Singleton Type where 
    type Sing = SType 
    dm SNat  = Nat 
    dm SBool = Bool

  -- | 'Promote' instance for expression types
  instance Promote Type where 
    promote Nat = Promoted SNat 
    promote Bool = Promoted SBool 

  -- | Type family desc
  type family Itp (ty :: Type) :: *
  type instance Itp 'Nat  = Nat
  type instance Itp 'Bool = Bool 

  -- | GADT describing well typed expressions
  data Expr :: Type -> * where 
    AddE  :: Expr 'Nat -> Expr 'Nat -> Expr 'Nat 
    MulE  :: Expr 'Nat -> Expr 'Nat -> Expr 'Nat
    ITE   :: Expr 'Bool -> Expr ty -> Expr ty -> Expr ty
    LEQ   :: Expr 'Nat -> Expr 'Nat -> Expr 'Bool
    ValE  :: Itp ty -> Expr ty 

  -- | Untyped expressions
  data Expr' = AddE' Expr' Expr' 
             | MulE' Expr' Expr' 
             | ITE' Expr' Expr' Expr' 
             | LEQ' Expr' Expr' 
             | ValN Nat 
             | ValB Bool deriving Show

  -- Checks wether an expression has a given type
  check :: Expr' -> Type -> Bool 
  check (AddE' e1 e2) Nat  = check e1 Nat && check e2 Nat
  check (MulE' e1 e2) Nat  = check e1 Nat && check e2 Nat
  check (ITE' g t e)  ty   = check g Bool && check t ty && check e ty 
  check (LEQ' e1 e2)  Bool = check e1 Nat && check e2 Nat
  check (ValN n)      Nat  = True 
  check (ValB b)      Bool = True  
  check _             _    = False

  -- | Evaluates an expression
  eval :: Expr ty -> Itp ty
  eval expr = undefined

  -- | Type level description of well typed expressions
  type family ExprDesc (ty :: Type) :: IDesc (Expr') Type
  type instance ExprDesc 'Nat = 
    S4 :+> (   Var 'Nat :*: Var 'Nat 
           ::: Var 'Nat :*: Var 'Nat  
           ::: Var 'Bool :*: Var 'Nat :*: Var 'Nat  
           ::: Sigma ('Proxy :: Proxy Nat) One
           ::: VNil )
  type instance ExprDesc 'Bool = 
    S3 :+> (   Var 'Bool :*: Var 'Bool :*: Var 'Bool
           ::: Var 'Nat :*: Var 'Nat 
           ::: Sigma ('Proxy :: Proxy Bool) One
           ::: VNil )

  type instance Desc T_EXPR (Expr') Type ty = ExprDesc ty 

  -- | Term level descriptions of well typed expressions
  exprDesc :: Proxy T_EXPR -> Sing ty -> Sing (ExprDesc ty)
  exprDesc _ SNat  = 
    s4 :+>~ (    SVar Nat :*:~ SVar Nat 
            :::~ SVar Nat :*:~ SVar Nat  
            :::~ SVar Bool :*:~ SVar Nat :*:~ SVar Nat 
            :::~ SSigma SOne gen (\_ -> Refl) 
            :::~ SVNil )
  exprDesc _ SBool = 
    s3 :+>~ (    SVar Bool :*:~ SVar Bool :*:~ SVar Bool  
            :::~ SVar Nat :*:~ SVar Nat 
            :::~ SSigma SOne gen (\_ -> Refl) 
            :::~ SVNil )

  -- | Convert a generic representation back to its corresponding expression
  toExpr :: Proxy T_EXPR -> Sing ty -> Interpret (ExprDesc ty) -> Expr' 
  toExpr _ SNat  (Left (e1 , e2)) = AddE' e1 e2
  toExpr _ SNat  (Right (Left (e1 , e2))) = AddE' e1 e2
  toExpr _ SNat  (Right (Right (Left ((g , t) , e)))) = ITE' g t e
  toExpr _ SNat  (Right (Right (Right (n , ())))) = ValN n
  toExpr _ SBool (Left ((g , t) , e)) = ITE' g t e
  toExpr _ SBool (Right (Left (e1 , e2))) = LEQ' e1 e2
  toExpr _ SBool (Right (Right (b , ()))) = ValB b

  -- | 'Describe' instance for wel-type expressions
  instance Describe T_EXPR Expr' Type where 
    sdesc = exprDesc 
    to = toExpr

  -- | Generator producing well-typed expressions
  exprGen :: Type -> G Type Expr'
  exprGen i = 
    case promote i of 
      (Promoted i') -> genDesc (Proxy :: Proxy T_EXPR) i' 
