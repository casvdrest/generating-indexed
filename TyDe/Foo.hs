merge :: [Int] -> [Int] -> [Int]
merge [] ys         = ys 
merge xs []         = xs 
merge (x:xs) (y:ys) | x <= y = x:merge xs (y:ys) 
                    | otherwise = y:merge (x:xs) ys 

sorted :: [Int] -> Bool
sorted [] = True
sorted [x] = True 
sorted (x:y:xs) = x <= y && sorted (y:xs)