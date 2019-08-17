module Example where 

  import Test.QuickCheck 

  merge :: [Int] -> [Int] -> [Int]
  merge xs []         = xs 
  merge [] ys         = ys 
  merge (x:xs) (y:ys) | x <= y    = x:(merge xs (y:ys))
                      | otherwise = y:(merge (x:xs) ys)  

  sorted :: [Int] -> Bool
  sorted [] = True
  sorted [x] = True 
  sorted (x:y:xs) = x <= y && sorted (y:xs)

  prop :: [Int] -> [Int] -> Property 
  prop xs ys = (sorted xs && sorted ys) ==> sorted (merge xs ys)