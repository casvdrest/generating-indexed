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

  import Control.Applicative

  class GGeneratable f g where 
    ggen :: G g (f a)

  instance GGeneratable V1 g where 
    ggen = empty 

  instance GGeneratable U1 g where 
    ggen = pure U1
    
  instance (GGeneratable f1 g, GGeneratable f2 g) 
      => GGeneratable (f1 :+: f2) g where
    ggen  =  L1 <$> ggen
         <|> R1 <$> ggen
        
  instance (GGeneratable f1 g, GGeneratable f2 g) 
      => GGeneratable (f1 :*: f2) g where 
    ggen = (:*:) <$> ggen  <*> ggen
  
  instance {-# OVERLAPPING #-} GGeneratable (Rec0 f) f where 
    ggen = K1 <$> mu

  instance {-# OVERLAPPABLE #-} Generatable c 
      => GGeneratable (K1 i c) a where 
    ggen = K1 <$> call

  instance (Datatype d, GGeneratable f g) 
      => GGeneratable (D1 d f) g where 
    ggen = M1 <$> ggen

  instance (Constructor c, GGeneratable f g) 
      => GGeneratable (C1 c f) g where 
    ggen = M1 <$> ggen

  instance (Selector s, GGeneratable f g) 
      => GGeneratable (S1 s f) g where 
    ggen = M1 <$> ggen 

  instance (Generic a, GGeneratable (Rep a) a) 
      => Generatable a where 
    gen = to <$> ggen
    
