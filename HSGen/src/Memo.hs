module Memo where 

  -- Trees with stored size
  data Tree = Leaf | Node Tree Int Tree deriving Show

  split :: Int -> [(Int, Int)]
  split n | n < 0     = error ""
          | n == 0    = [(0 , 0)]
          | otherwise = (0, n) : map (\(n, m) -> (n + 1, m)) (split (n - 1))

  -- List all trees of a given size
  trees :: (Int -> [Tree]) -> Int -> [Tree]
  trees f n | n < 0     = [] 
            | n == 0    = [Leaf]
            | otherwise = concatMap (\(n , m) -> Node <$> (f n) <*> pure (n + m + 1) <*> f m) (split (n - 1))

  fix :: (a -> a) -> a  
  fix f = let x = f x in x

  memoize :: (Int -> a) -> (Int -> a)
  memoize f = (map f [0 ..] !!)

  