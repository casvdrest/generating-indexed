{-# LANGUAGE DataKinds, TypeOperators, KindSignatures, GADTs, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}

module Examples.Term where

  import Singleton 
  import IDesc.Universe
  import Data.Proxy
  import Datatypes
  import Gen

  import Control.Applicative

  data Type = Type :-> Type | T deriving (Show , Eq)

  data SType :: Type -> * where 
    ST      :: SType T
    (:->$)  :: SType t1 -> SType t2 -> SType (t1 :-> t2)

  instance Singleton Type where 
    type Sing = SType
    dm ST            = T
    dm (t1 :->$ t2)  = dm t1 :-> dm t2

  instance Promote Type where 
    promote T = Promoted ST 
    promote (t1 :-> t2) = 
      case promote t1 of 
        Promoted t1' -> 
          case promote t2 of 
            Promoted t2' -> Promoted (t1' :->$ t2')

  instance SingGeneratable Type where 
    genSing   =   pure (Promoted ST)
             <|>  ( do  (Promoted ty1) <- mu ()
                        (Promoted ty2) <- mu ()
                        return (Promoted (ty1 :->$ ty2)) )
  type Ctx = [Type]

  data CtxPos = Here | There CtxPos
    
  toNat :: CtxPos -> Nat  
  toNat Here = Zero 
  toNat (There p) = Suc (toNat p)

  data SCtxPos :: CtxPos -> * where 
    SHere :: SCtxPos Here 
    SThere :: SCtxPos p -> SCtxPos (There p)

  instance Singleton CtxPos where
    type Sing = SCtxPos 
    dm SHere = Here 
    dm (SThere p) = There (dm p)

  instance Promote CtxPos where 
    promote Here  = Promoted SHere
    promote (There p) = 
      case promote p of 
        (Promoted p') -> Promoted (SThere p') 

  -- | The type of terms
  data Term = TVar Nat | TAbs Term | TApp Term Term deriving Show

  ab :: Term -> Term  
  ab (TVar n) = TVar (Suc n)
  ab (TAbs t) = TAbs (ab t)
  ab (TApp t1 t2) = TApp (ab t1) (ab t2)


  genElem :: Ctx -> Type -> G () CtxPos 
  genElem [] _      = empty
  genElem (t:ts) t' = (if t == t' then pure Here else empty) <|> (There <$> genElem ts t')

  genType :: G () Type  
  genType = pure T <|> ((:->) <$> mu () <*> mu ())

