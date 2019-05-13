
module IDesc.Eval where

  import IDesc.Instances
  import IDesc.Lambda

  subst :: Term Id -> Id -> Term Id -> Term Id
  subst (VarT x') x t' | x == x'   = t'
                       | otherwise = VarT x'
  subst (AbsT x' t) x t' | x == x'   = AbsT x' t
                         | otherwise = AbsT x' (subst t x t')
  subst (AppT t1 t2) x t' = AppT (subst t1 x t') (subst t2 x t')

  eval :: Term Id -> Term Id
  eval (AppT t1 t2) =
    case eval t1 of
      (AbsT x t1') -> eval (subst t1' x t2) 
      term         -> AppT term t2
  eval t = t

  term1 :: Term Id
  term1 = AppT (AbsT "x" (VarT "x")) (VarT "y")
