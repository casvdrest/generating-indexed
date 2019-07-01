{-# LANGUAGE DataKinds, GADTs, TypeFamilies, KindSignatures, PolyKinds, TypeOperators, RankNTypes, MultiParamTypeClasses #-}

module Expr where 

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Singleton
  import Data
  import Control.Applicative
  import IDesc.Instances
  import Unsafe.Coerce

  import IDesc.IDesc

  data Type = Nat | Bool 

  data SType :: Type -> * where 
    SNat  :: SType 'Nat 
    SBool :: SType 'Bool
  
  instance Singleton Type where 
    type Sing = SType 
    dm SNat  = Nat 
    dm SBool = Bool

  instance Promote Type where 
    promote Nat = Promoted SNat 
    promote Bool = Promoted SBool 

  type family Itp (ty :: Type) :: *
  type instance Itp 'Nat  = Nat
  type instance Itp 'Bool = Bool 

  data Expr :: Type -> * where 
    AddE  :: Expr 'Nat -> Expr 'Nat -> Expr 'Nat 
    MulE  :: Expr 'Nat -> Expr 'Nat -> Expr 'Nat
    ITE   :: Expr 'Bool -> Expr ty -> Expr ty -> Expr ty
    LEQ   :: Expr 'Nat -> Expr 'Nat -> Expr 'Bool
    ValE  :: Itp ty -> Expr ty 

  data Expr' = AddE' Expr' Expr' | MulE' Expr' Expr' | ITE' Expr' Expr' Expr' | LEQ' Expr' Expr' | ValN Nat | ValB Bool deriving Show

  check :: Expr' -> Type -> Bool 
  check (AddE' e1 e2) Nat  = check e1 Nat && check e2 Nat
  check (MulE' e1 e2) Nat  = check e1 Nat && check e2 Nat
  check (ITE' g t e)  ty   = check g Bool && check t ty && check e ty 
  check (LEQ' e1 e2)  Bool = check e1 Nat && check e2 Nat
  check (ValN n)      Nat  = True 
  check (ValB b)      Bool = True  
  check _             _    = False

  eval :: Expr ty -> Itp ty
  eval expr = undefined

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

  toExpr :: Proxy T_EXPR -> Sing ty -> Interpret (ExprDesc ty) -> Expr' 
  toExpr _ SNat  (Left (e1 , e2)) = AddE' e1 e2
  toExpr _ SNat  (Right (Left (e1 , e2))) = AddE' e1 e2
  toExpr _ SNat  (Right (Right (Left ((g , t) , e)))) = ITE' g t e
  toExpr _ SNat  (Right (Right (Right (n , ())))) = ValN n
  toExpr _ SBool (Left ((g , t) , e)) = ITE' g t e
  toExpr _ SBool (Right (Left (e1 , e2))) = LEQ' e1 e2
  toExpr _ SBool (Right (Right (b , ()))) = ValB b

  instance Describe T_EXPR Expr' Type where 
    sdesc = exprDesc 
    to = toExpr

  exprGen :: Type -> G Type Expr' Expr'
  exprGen i = 
    case promote i of 
      (Promoted i') -> genDesc (Proxy :: Proxy T_EXPR) i' 
