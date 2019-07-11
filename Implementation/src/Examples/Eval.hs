module Examples.Eval where

  import Examples.Instances
  import Examples.Lambda
  import Examples.Term

  import Datatypes
  import Interpret

  eval :: Term -> Term
  eval tm = undefined

  isApp :: Term -> Bool 
  isApp (TApp _ _ ) = True 
  isApp _ = False

  inContext :: Nat -> Ctx -> Type -> Bool
  inContext n [] _ = False 
  inContext Zero (t:ts) t' = t == t' 
  inContext (Suc n) (t:ts) t' = inContext n ts t'

  types :: Int -> [Type] 
  types = runEnum (\() -> genType) ()

  check :: Ctx -> Term -> Type -> Bool 
  check ctx (TVar n )      ty            = inContext n ctx ty
  check ctx (TAbs tm)      (ty1 :-> ty2) = check (ty1:ctx) tm ty2
  check ctx (TApp tm1 tm2) ty            = any (\i -> any (\ty' -> check ctx tm1 (ty' :-> ty) && check ctx tm2 ty') (types i)) [1..3]
  check _   _              _             = False