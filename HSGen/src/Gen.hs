{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Gen where 

  import Control.Applicative

  data Gen a t where 
    None  :: Gen a t 
    Pure  :: a -> Gen a t 
    Or    :: Gen a t -> Gen a t -> Gen a t 
    Ap    :: Gen (b -> a) t -> Gen b t -> Gen a t
    Bind  :: Gen a t -> (a -> Gen b t) -> Gen b t
    Mu    :: Gen a a
    CoMu  :: Generatable b => Gen (a -> b) (a -> b)
    Call  :: Gen a a -> Gen a t

  merge :: [a] -> [a] -> [a] 
  merge []     ys = ys 
  merge (x:xs) ys = x : merge ys xs

  (.~.) :: (Gen a t, Gen t t) -> Int -> [a]
  (CoMu  , tg) .~. 0    = [ \_ -> x | x <- run gen 0]
  (Pure x, tg) .~. 0    = [x] 
  (Mu    , tg) .~. 0    = []
  (gen, tg)  .~. n = 
    case gen of 
      None       -> []
      Pure x     -> [x]
      Or g1 g2   -> merge ((g1, tg) .~. n) ((g2, tg) .~. n)
      Ap g1 g2   -> ((g1, tg) .~. n) <*> ((g2, tg) .~. n)
      Bind g1 g2 -> ((g1, tg) .~. n) >>= \x -> (g2 x, tg) .~. n
      Mu         -> (tg, tg) .~. (n - 1) 
      CoMu       -> (tg, tg) .~. (n - 1) 
      Call gen'  -> (gen', gen') .~. n

  newtype G t a = G (Gen a t)

  unG :: G t a -> Gen a t 
  unG (G g) = g

  instance Functor (G t) where 
    fmap f (G gen) = G (Ap (Pure f) gen)

  instance Applicative (G t) where
    pure              = G . Pure
    (G g1) <*> (G g2) = G (Ap g1 g2) 

  instance Monad (G t) where 
    return        = G . Pure 
    (G g1) >>= g2 = G (Bind g1 (unG . g2))

  instance Alternative (G t) where 
    empty             = G None 
    (G g1) <|> (G g2) = G (Or g1 g2)

  class Generatable a where 
    gen :: G a a

  class CoGeneratable a where 
    cogen :: Generatable b => G (a -> b) (a -> b)

  mu :: G t t 
  mu = G Mu

  mu' :: Generatable b => G (a -> b) (a -> b)
  mu' = G CoMu

  call :: Generatable a => G t a
  call = G (Call (unG gen))

  call' :: (CoGeneratable a , Generatable b) => G t (a -> b)
  call' = G (Call (unG cogen))

  run :: G a a -> Int -> [a]
  run (G gen) n = (gen, gen) .~. n