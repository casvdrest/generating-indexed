{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Generic where 

  import Gen

  import GHC.Generics
  import Data.Proxy

  import Control.Applicative

  class GGeneratable f g where 
    ggen :: G g (f a)

  class GCoGeneratable f g where 
    gcogen :: (Generatable b) => G (g -> b) (f a -> b)

  instance GGeneratable V1 g where 
    ggen = empty 

  instance GCoGeneratable V1 g where 
    gcogen = empty

  instance GGeneratable U1 g where 
    ggen = pure U1

  instance GCoGeneratable U1 g where 
    gcogen = (\x U1 -> x) <$> call 
  
  instance (GGeneratable f1 g, GGeneratable f2 g) 
      => GGeneratable (f1 :+: f2) g where
    ggen  =  L1 <$> ggen
         <|> R1 <$> ggen

  instance (GCoGeneratable f1 g, GCoGeneratable f2 g)
      => GCoGeneratable (f1 :+: f2) g where 
    gcogen = toF <$> gcogen <*> gcogen
      where toF :: (f1 a -> b) -> (f2 a -> b) 
                -> (f1 :+: f2) a -> b
            toF fx fy (L1 v) = fx v 
            toF fx fy (R1 v) = fy v

  instance (GGeneratable f1 g, GGeneratable f2 g) 
      => GGeneratable (f1 :*: f2) g where 
    ggen = (:*:) <$> ggen  <*> ggen

  instance (GCoGeneratable f1 g, GCoGeneratable f2 g)
      => GCoGeneratable (f1 :*: f2) g where 
    gcogen = undefined

  instance {-# OVERLAPPING #-} GGeneratable (Rec0 f) f where 
    ggen = K1 <$> mu

  instance {-# OVERLAPPING #-} GCoGeneratable (Rec0 f) f where 
    gcogen = undefined -- (. unK1) <$> mu'

  instance {-# OVERLAPPABLE #-} Generatable c 
      => GGeneratable (K1 i c) a where 
    ggen = K1 <$> call

  instance {-# OVERLAPPABLE #-} CoGeneratable c 
      => GCoGeneratable (K1 i c) a where 
    gcogen = (. unK1) <$> call' 

  instance (Datatype d, GGeneratable f g) 
      => GGeneratable (D1 d f) g where 
    ggen = M1 <$> ggen

  instance (Datatype d, GCoGeneratable f g)
      => GCoGeneratable (D1 d f) g where 
    gcogen = (. unM1) <$> gcogen 

  instance (Constructor c, GGeneratable f g) 
      => GGeneratable (C1 c f) g where 
    ggen = M1 <$> ggen

  instance (Constructor c, GCoGeneratable f g)
      => GCoGeneratable (C1 c f) g where 
    gcogen = (. unM1) <$> gcogen 

  instance (Selector s, GGeneratable f g) 
      => GGeneratable (S1 s f) g where 
    ggen = M1 <$> ggen 

  instance (Selector s, GCoGeneratable f g)
      => GCoGeneratable (S1 s f) g where 
    gcogen = (. unM1) <$> gcogen 

  instance (Generic a, GGeneratable (Rep a) a) 
      => Generatable a where 
    gen = to <$> ggen
  
  instance (Generic a, GCoGeneratable (Rep a) a)
      => CoGeneratable a where 
    cogen = (. from) <$> gcogen 