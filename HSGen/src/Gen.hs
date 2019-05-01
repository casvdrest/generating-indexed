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

  data Ex = forall a . Ex a

  data Nat = Zero | Suc Nat deriving (Show, Eq, Generic, DepthCalc)

  -- | The type of abstract generators 
  data Gen a t where 
    None  :: Gen a t 
    Pure  :: a -> Gen a t 
    Or    :: Gen a t -> Gen a t -> Gen a t 
    Ap    :: Gen (b -> a) t -> Gen b t -> Gen a t
    Bind  :: Gen a t -> (a -> Gen b t) -> Gen b t
    Mu    :: Ex -> Gen a a
    Call  :: Gen a a -> Gen a t
    CallF :: i -> (i -> Gen a a) -> (Ex -> i) -> Gen a t

  newtype G t a = G (Gen a t)

  unG :: G t a -> Gen a t 
  unG (G g) = g

  
  p :: String -> String
  p s = "(" <> s <> ")"

  s :: [String] -> String
  s []     = ""
  s (x:xs) = x ++ " " ++ s xs  

  instance Show (Gen a t) where
    show None = "None"
    show (Pure _) = "Pure"
    show (Or l r) = p (s ["Or" , show l , show r])
    show (Ap f g) = p (s ["Ap" , show f , show g])
    show (Bind f g) = p (s ["Bind" , show f , "# -> #"])
    show (Mu _) = "Mu"
    show (Call g) = p (s ["Call" , show g])
    show (CallF _ _ _) = "CallF"

  instance Show (G a t) where
    show (G g) = "G " ++ show g

  class Generatable a where 
    gen :: G a a

  class CoGeneratable a where 
    cogen :: (Generatable b) => G (a -> b) (a -> b)

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

  mu :: Ex -> G t t 
  mu = G . Mu

  call :: Generatable a => G t a
  call = G (Call (unG gen))

  c :: G a a -> G t a 
  c gen = G (Call (unG gen))

  call' :: (CoGeneratable a, Generatable b) => G t (a -> b)
  call' = G (Call (unG cogen))
