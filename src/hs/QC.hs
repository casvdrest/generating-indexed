module QC where

  import Data.List
  import Test.QuickCheck

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