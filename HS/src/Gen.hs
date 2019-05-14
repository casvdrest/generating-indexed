{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UnicodeSyntax #-}

module Gen where 

  import Depth
  import GHC.Generics
  import Control.Applicative
  import Unsafe.Coerce

  -- | The type of abstract generators 
  data Gen i a t where 
    None  :: Gen i a t 
    Pure  :: a -> Gen i a t 
    Or    :: Gen i a t -> Gen i a t -> Gen i a t 
    Ap    :: Gen i (b -> a) t -> Gen i b t -> Gen i a t
    Bind  :: Gen i a t -> (a -> Gen i b t) -> Gen i b t
    Mu    :: i -> Gen i a a
    Call :: (j -> Gen j a a) -> j -> Gen i a t

  -- | Wrapper to allow generators to be an instance of 
  --   the required typeclasses
  newtype G i t a = G (Gen i a t)

  -- | Convert a wrapped generator into a generator
  unG :: G i t a -> Gen i a t 
  unG (G g) = g

  ----------------------------------------------------------------------------
  -- Show instance printing a generator's structure (for debuggin purposes)
  
  p :: String -> String
  p s = "(" <> s <> ")"

  s :: [String] -> String
  s []     = ""
  s (x:xs) = x ++ " " ++ s xs  

  instance Show (Gen i a t) where
    show None = "None"
    show (Pure _) = "Pure"
    show (Or l r) = p (s ["Or" , show l , show r])
    show (Ap f g) = p (s ["Ap" , show f , show g])
    show (Bind f g) = p (s ["Bind" , show f , "# -> #"])
    show (Mu _) = "Mu"
    show (Call g i) = p (s ["Call" , show (g i)])

  instance Show (G i a t) where
    show (G g) = "G " ++ show g

  ----------------------------------------------------------------------------
  -- Typeclasses for generatable non-indexed datatypes
  class Generatable a where 
    gen :: G () a a

  class CoGeneratable a where 
    cogen :: (Generatable b) => G () (a -> b) (a -> b)

  ----------------------------------------------------------------------------
  -- Typeclass instances
     
  instance Functor (G i t) where 
    fmap f (G gen) = G (Ap (Pure f) gen)

  instance Applicative (G i t) where
    pure              = G . Pure
    (G g1) <*> (G g2) = G (Ap g1 g2) 

  instance Monad (G i t) where 
    return        = G . Pure 
    (G g1) >>= g2 = G (Bind g1 (unG . g2))

  instance Alternative (G i t) where 
    empty             = G None 
    (G g1) <|> (G g2) = G (Or g1 g2)

  ----------------------------------------------------------------------------
  -- Smart constructors for generator compositions

  mu :: i -> G i t t 
  mu = G . Mu

  call :: Generatable a => G () t a
  call = G (Call (\() -> unG gen) ())

  call' :: (CoGeneratable a, Generatable b) => G () t (a -> b)
  call' = G (Call (\() -> unG cogen) ())

  -- | Lifts a value from a to () -> a 
  triv :: a -> () -> a 
  triv = const
