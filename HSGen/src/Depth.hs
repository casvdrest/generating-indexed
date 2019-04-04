{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Depth where 

  import GHC.Generics
  import Data.Proxy
  
  -- | Class of those types whose recursive depth we can calculate
  class DepthCalc a where 
    depth :: a -> Int

    -- | Default generic implementation for simple algebraic data types
    default depth :: (Generic a, GDepthCalc (Rep a) a) => a -> Int 
    depth = gdepth (Proxy :: Proxy a) . from

  -- | Generic depth calculation
  -- 
  -- The second parameter 'b' is used to record for which type we are 
  -- deriving a depth calculation function. The 'Proxy' parameter is 
  -- used to guide the typechecker towards selecting the right instance. 
  class GDepthCalc f b where 
    gdepth :: Proxy b -> f a -> Int 

  -- | Depth calculation for U1
  --
  -- Constructors with arity 0 have a recursive depth of 0
  instance GDepthCalc U1 a where 
    gdepth Proxy U1 = 0

  -- | Depth calculation for product types 
  -- 
  -- The depth of a product type is equal to the maximum depth of 
  -- its children
  instance (GDepthCalc f a , GDepthCalc g a) => GDepthCalc (f :*: g) a where 
    gdepth Proxy (l :*: r) = max (gdepth (Proxy :: Proxy a) l) (gdepth (Proxy :: Proxy a) r)

  -- | Depth calculation for sum types 
  -- 
  -- The depth of a sum type is simply the depth of value that lives within 
  instance (GDepthCalc f a, GDepthCalc g a) => GDepthCalc (f :+: g) a where 
    gdepth Proxy (L1 l) = gdepth (Proxy :: Proxy a) l 
    gdepth Proxy (R1 r) = gdepth (Proxy :: Proxy a) r

  -- | Metadata wrappers do not influence a type's depth calculation
  instance (GDepthCalc f a) => GDepthCalc (M1 i c f) a where 
    gdepth Proxy (M1 x) = gdepth (Proxy :: Proxy a) x

  -- | Recursive calls 
  -- 
  -- The depth of a recursive position is one greater than the depth of the 
  -- recursive value. 
  instance {-# OVERLAPPING #-} (DepthCalc a) => GDepthCalc (K1 R a) a where 
    gdepth Proxy (K1 x) = 1 + depth x

  -- | Constants (Other)
  -- 
  -- Other constants simply use the depth of the type that is referred to 
  -- by the constant.
  instance {-# OVERLAPPABLE #-} (DepthCalc b) => GDepthCalc (K1 R b) a where 
    gdepth Proxy (K1 x) = depth x
  
  -- | A few useful instances. 
  instance DepthCalc a => DepthCalc [a]
  instance DepthCalc Bool
  instance DepthCalc a => DepthCalc (Maybe a)
  instance (DepthCalc a , DepthCalc b) => DepthCalc (a, b)
  instance (DepthCalc a , DepthCalc b) => DepthCalc (Either a b) 
