{-# LANGUAGE InstanceSigs #-}

module Profunctor where 

  class Profunctor p where 
    dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b' 

  class Profunctor p => Cartesian p where 
    first  :: p a b -> p (a, c) (b, c)
    second :: p a b -> p (c, a) (c, b)
    
  class Profunctor p => CoCartesian p where 
    left  :: p a b -> p (Either a c) (Either b c)
    right :: p a b -> p (Either c a) (Either c b)

  instance Profunctor (->) where 
    dimap f g h = g . h . f

  cross :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
  cross f g (x, y) = (f x, g y)

  plus :: (a -> c) -> (b -> d) -> Either a b -> Either c d
  plus f g (Left x)  = Left (f x)
  plus f g (Right y) = Right (g y)

  instance Cartesian (->) where 
    first h = cross h id
    second h = cross id h

  instance CoCartesian (->) where 
    left h = plus h id 
    right h = plus id h

  (>>=) :: (s -> (a, s)) -> (a -> s -> (b, s)) -> s -> (b, s)
  f >>= g = uncurry g . f

  return :: a -> s -> (a, s)
  return = (,)

  type State s a = s -> (a, s)
  type Except a = Either String a

  liftState :: (a -> b) -> State s a -> State s b
  liftState = (.) . first

  liftEither :: (a -> b) -> Except a -> Except b
  liftEither = right
  