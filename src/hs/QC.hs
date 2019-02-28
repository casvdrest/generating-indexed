{-# LANGUAGE DeriveAnyClass #-}

module QC where

  import Data.List
  import Test.QuickCheck
  import Test.QuickCheck.Gen

  reverse' :: Eq a => [a] -> [a]
  reverse' []     = []
  reverse' (x:xs) = nub ((reverse' xs) ++ [x, x])

  reverse_preserves_length :: [Int] -> Bool
  reverse_preserves_length xs =
    length xs == length (reverse' xs)


  insert' :: Ord a => a -> [a] -> [a]
  insert' v []                   = [v]
  insert' v (x:xs) |  v <= x     = v:x:xs 
                  |  otherwise  = x:insert' v xs

  sorted :: Ord a => [a] -> Bool 
  sorted []        = True 
  sorted (_:[])    = True
  sorted (x:y:xs)  = x <= y && sorted (y:xs)

  insert_preserves_sorted :: (Int, [Int]) -> Bool 
  insert_preserves_sorted (x, xs) = sorted (insert' x xs)

  gen_sorted :: Gen (Int, [Int])
  gen_sorted = do 
    xs <- arbitrary 
    x  <- arbitrary 
    return (x, diff (map abs xs))
    where diff :: [Int] -> [Int]
          diff []     = [] 
          diff (x:xs) = x:map (+x) (diff xs) 

  data Term = Abs Term
            | App Term Term 
            | Var Int 
            deriving Show


  instance Arbitrary Term where 
    arbitrary = oneof [ Abs <$> arbitrary
                      , App <$> arbitrary <*> arbitrary
                      , Var <$>  arbitrary `suchThat` (>=0) ]

  well_scoped :: Term -> Bool  
  well_scoped tm = well_scoped' 0 tm  
    where well_scoped' :: Int -> Term -> Bool 
          well_scoped' n (Abs tm) = well_scoped' (n + 1) tm
          well_scoped' n (App tm1 tm2) = well_scoped' n tm1 && well_scoped' n tm2
          well_scoped' n (Var v) = v < n

  well_typed :: Term -> Bool 
  well_typed _ = True

  foo :: Term -> Property 
  foo tm = well_scoped tm ==> well_typed tm