import Distribution.Simple
main = defaultMain

map' :: (a -> b) -> [a] -> [b]
map' f [] = []
map' f (x:xs) = f x : map' f xsλ> 