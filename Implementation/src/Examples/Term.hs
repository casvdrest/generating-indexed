{-# LANGUAGE DataKinds, TypeOperators, KindSignatures, GADTs, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}

{-|
Module      : Term
Description : Raw datatypes for lambda terms
Copyright   : (c) Cas van der Rest, 2019
Maintainer  : c.r.vanderrest@students.uu.nl
Stability   : experimental

Contains the raw datatypes that we use to represent untyped lambda terms. They function 
as a base type for generation of well typed terms. 
-}
module Examples.Term where

  import Singleton 
  import IDesc.Universe
  import Data.Proxy
  import Datatypes
  import Gen

  import Control.Applicative

  -- | Type of lambda terms
  data Type = Type :-> Type | T deriving (Show , Eq)

  -- | Singleton type for types
  data SType :: Type -> * where 
    ST      :: SType T
    (:->$)  :: SType t1 -> SType t2 -> SType (t1 :-> t2)

  -- | 'Singleton' instance for types.
  instance Singleton Type where 
    type Sing = SType
    dm ST            = T
    dm (t1 :->$ t2)  = dm t1 :-> dm t2

  -- | 'Promote' instance for types
  instance Promote Type where 
    promote T = Promoted ST 
    promote (t1 :-> t2) = 
      case promote t1 of 
        Promoted t1' -> 
          case promote t2 of 
            Promoted t2' -> Promoted (t1' :->$ t2')

  -- | Instance for the generation of type level types
  instance SingGeneratable Type where 
    genSing   =   pure (Promoted ST)
             <|>  ( do  (Promoted ty1) <- mu ()
                        (Promoted ty2) <- mu ()
                        return (Promoted (ty1 :->$ ty2)) )
  type Ctx = [Type]

  -- | Context positions (isomorphic to Nat)
  data CtxPos = Here | There CtxPos
    
  -- | Convert an context position to a natural
  toNat :: CtxPos -> Nat  
  toNat Here = Zero 
  toNat (There p) = Suc (toNat p)

  -- | Singleton instance for context positions
  data SCtxPos :: CtxPos -> * where 
    SHere :: SCtxPos Here 
    SThere :: SCtxPos p -> SCtxPos (There p)

  -- | 'Singleton' instance for context positions
  instance Singleton CtxPos where
    type Sing = SCtxPos 
    dm SHere = Here 
    dm (SThere p) = There (dm p)

  -- | 'Promote' instance for context positions
  instance Promote CtxPos where 
    promote Here  = Promoted SHere
    promote (There p) = 
      case promote p of 
        (Promoted p') -> Promoted (SThere p') 

  -- | The type of terms
  data Term = TVar Nat | TAbs Term | TApp Term Term deriving Show

  -- | Generates all context positions that have a given type
  genElem :: Ctx -> Type -> G () CtxPos 
  genElem [] _      = empty
  genElem (t:ts) t' = (if t == t' then pure Here else empty) <|> (There <$> genElem ts t')

  -- | Generates types
  genType :: G () Type  
  genType = pure T <|> ((:->) <$> mu () <*> mu ())

