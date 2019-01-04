-- Mostly taken from https://hackage.haskell.org/package/control-monad-omega-0.3/docs/Control-Monad-Omega.html

module Omega where 

  import qualified Control.Monad as Monad
  import qualified Control.Applicative as Applicative

  diagonal :: [[a]] -> [a]
  diagonal = concat . stripe
    where stripe [] = []
          stripe ([]:xss) = stripe xss
          stripe ((x:xs):xss) = [x] : zipCons xs (stripe xss)

          zipCons [] ys = ys
          zipCons xs [] = map (:[]) xs
          zipCons (x:xs) (y:ys) = (x:y) : zipCons xs ys

  newtype Omega a = Omega { runOmega :: [a] }

  each :: [a] -> Omega a
  each = Omega

  instance Functor Omega where
    fmap f (Omega xs) = Omega (map f xs)
  
  instance Monad Omega where
    return x = Omega [x]
    Omega m >>= f = Omega $ diagonal $ map (runOmega . f) m
    fail _ = Omega []

  instance Applicative.Applicative Omega where
    pure = return
    (<*>) = Monad.ap

  interleave :: Omega a -> Omega a -> Omega a
  interleave (Omega { runOmega = xs} ) ys = do 
    case xs of 
      (z:zs) -> each (z: runOmega (interleave ys (each zs)))
      _      -> ys

  data Nat = Z | S Nat

  type R = (Nat, Nat)
  
  asInt :: Nat -> Int
  asInt Z = 0
  asInt (S n) = 1 + asInt n

  instance Show Nat where 
    show = show . asInt

  nats :: [Nat]
  nats = Z : map S nats

  enumerateRationals :: Omega R
  enumerateRationals = do 
    x <- each (map S nats)
    y <- each (map S nats)
    return (x, y)

  data Foo = Bar | Baz Foo Foo deriving (Show)

  enumerateBar :: Omega Foo 
  enumerateBar = return Bar

  enumerateBaz :: Omega Foo 
  enumerateBaz = do 
    x <- enumerateFoo 
    y <- enumerateFoo
    return (Baz x y)

  enumerateFoo :: Omega Foo 
  enumerateFoo = interleave enumerateBar enumerateBaz