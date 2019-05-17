{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Contains a couple of manually defined instances of 'Generatable',
-- demonstrating how generator definitions arise from the structure of
-- the type they're designed for.
module Instances where

  import Gen
  import Depth
  import Data
  import Control.Applicative

  instance (CoGeneratable a, Generatable b) => Generatable (a -> b) where
    gen = cogen

  instance Generatable Nat where
    gen  =  pure Zero
        <|> (Suc <$> mu ())
  {-
  instance CoGeneratable Nat where
    cogen = toF <$> call <*> mu'
      where toF :: a -> (Nat -> a) -> Nat -> a
            toF z _ Zero     = z
            toF _ f (Suc n) = f n -}

  instance Generatable Bool where
    gen  =  pure True
        <|> pure False

  instance CoGeneratable Bool where
    cogen = toF <$> call <*> call
      where toF :: a -> a -> Bool -> a
            toF x y True  = x
            toF x y False = y

  instance (Generatable a) => Generatable (Maybe a) where
    gen  =  pure Nothing
        <|> Just <$> call

  instance (CoGeneratable a) => CoGeneratable (Maybe a) where
    cogen = toF <$> call <*> call'
      where toF :: b -> (a -> b) -> Maybe a -> b
            toF x fy Nothing  = x
            toF x fy (Just v) = fy v

  instance (Generatable a, Generatable b) => Generatable (a, b) where
    gen = (,) <$> call <*> call

  instance (CoGeneratable a, CoGeneratable b) => CoGeneratable (a, b) where
    cogen = uncurry <$> call'

  instance (Generatable a, Generatable b) => Generatable (Either a b) where
    gen  =  Left  <$> call
        <|> Right <$> call

  instance (CoGeneratable a, CoGeneratable b) => CoGeneratable (Either a b) where
    cogen = toF <$> call' <*> call'
      where toF :: (a -> c) -> (b -> c) -> (Either a b) -> c
            toF fx fy (Left x)  = fx x
            toF fx fy (Right y) = fy y

  {-instance (Generatable a) => Generatable [a] where
    gen  =  pure []
        <|> (:) <$> call <*> mu () -}

  instance (CoGeneratable a) => CoGeneratable [a] where
    cogen = toF <$> call <*> (uncurry <$> call')
      where toF :: b -> ((a , [a]) -> b) -> [a] -> b
            toF x fy []     = x
            toF x fy (z:zs) = fy (z, zs)
