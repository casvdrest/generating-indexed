{-# LANGUAGE TypeOperators #-}

module Species where

  data Zero a

  instance Functor Zero where
    fmap = undefined

  data One a = One

  instance Functor One where
    fmap _ One = One

  data X a = X a

  instance Functor X where
    fmap f (X x) = X (f x)

  infixl 6 +

  data (f + g) a = Inl (f a) | Inr (g a)

  instance (Functor f, Functor g) => Functor (f + g) where
    fmap f (Inl x) = Inl (f <$> x)
    fmap f (Inr y) = Inr (f <$> y)

  data P f g a = P (f a) (g a)
