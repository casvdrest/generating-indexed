{-|
Module      : Eval
Description : Evaluator for the simply typed lamba calculus
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

Contains an evaluator and typechecker for the simply typed lambda calculus
-}

module Examples.Eval where

  import Examples.Instances
  import Examples.Lambda
  import Examples.Term

  import Datatypes
  import Interpret

  -- | Evaluate lambda terms
  eval :: Term -> Term
  eval tm = undefined

  -- | Asserts whether a term is a function application
  isApp :: Term -> Bool 
  isApp (TApp _ _ ) = True 
  isApp _ = False

  -- | Checks whether a variable in a context has a certain type
  inContext :: Nat -> Ctx -> Type -> Bool
  inContext n [] _ = False 
  inContext Zero (t:ts) t' = t == t' 
  inContext (Suc n) (t:ts) t' = inContext n ts t'

  -- | Generates some types
  types :: Int -> [Type] 
  types = runEnum (\() -> genType) ()

  -- | Check if a term has a certain type under a given context
  check :: Ctx -> Term -> Type -> Bool 
  check ctx (TVar n )      ty            = inContext n ctx ty
  check ctx (TAbs tm)      (ty1 :-> ty2) = check (ty1:ctx) tm ty2
  check ctx (TApp tm1 tm2) ty            = any (\i -> any (\ty' -> check ctx tm1 (ty' :-> ty) && check ctx tm2 ty') (types i)) [1..3]
  check _   _              _             = False