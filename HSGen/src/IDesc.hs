{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module IDesc where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Data.Singletons
  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics

  import Debug.Trace

  data instance Sing (n :: Nat) where
    SZero :: Sing Zero
    SSuc  :: Sing n -> Sing (Suc n)

  data Fin (n :: Nat) where
    Fz :: Fin (Suc n)
    Fs :: Fin n -> Fin (Suc n)

  data Vec (a :: *) :: Nat -> * where
    VNil :: Vec a Zero
    (:::) :: a -> Vec a n -> Vec a (Suc n)
  
  genBool :: G Bool Bool
  genBool = pure True <|> pure False

  genNat :: G Nat Nat
  genNat = pure Zero <|> Suc <$> mu (Ex ())

  instance Generatable Bool where
    gen = genBool

  instance Generatable Nat where
    gen = genNat

  instance Generatable () where
    gen = pure ()

  infixr 5 :::

  class IndexedGeneratable a i where
    genIndexed :: i -> G a a
    giMuConv   :: Proxy a -> Ex -> i 

  instance Generatable a => IndexedGeneratable a () where
    genIndexed () = gen
    giMuConv _ = unEx asUnit

  --------------------------------------------------------------------------
  -- Universe definition
  
  data IDesc (a :: *) (i :: *) where
    One    :: IDesc a i
    Empty  :: IDesc a i
    Var    :: i -> IDesc a i
    (:*:)  :: IDesc a i -> IDesc a i -> IDesc a i
    (:+>)  :: Sing n -> Vec (IDesc a i) n -> IDesc a i
    K      :: IndexedGeneratable s j => Proxy s -> (i -> j) -> IDesc a i
    Sigma  :: forall it ot a i (s :: FTag) . Solve s it ot =>
      Proxy s -> G ot ot -> (it -> IDesc a i) -> IDesc a i 

  type Func a i = i -> IDesc a i

  ---------------------------------------------------------------------------
  -- Generic generator 

  newtype CG a = CG (Gen a a)

  idesc_gen :: IDesc a i -> i -> G Ex Ex
  idesc_gen One _ = pure (Ex ())
  idesc_gen Empty _ = G None
  idesc_gen (Var i) _ = (\x (Ex y) -> Ex (x , y)) <$> pure i <*> G (Mu (Ex i))
  idesc_gen (SZero :+> VNil) _= G None
  idesc_gen (dl :*: dr) i =
      (\(Ex x) (Ex y) -> Ex (x , y)) <$>
        idesc_gen dl i
    <*> idesc_gen dr i
  idesc_gen ((SSuc n) :+> (x ::: xs)) i =
        ((\(Ex x) -> Ex $ Left x)  <$> idesc_gen x i)
    <|> ((\(Ex y) -> Ex $ Right y) <$> idesc_gen (n :+> xs) i)
  idesc_gen (K (Proxy :: Proxy s) (j :: i -> jTy)) i = Ex <$> G (CallF (j i) (unG . gen) conv)
    where gen :: jTy -> G s s
          gen = genIndexed
          conv :: Ex -> jTy
          conv = giMuConv (Proxy :: Proxy s)
  idesc_gen (Sigma ptag og f) i =
    do v  <- G (Call (unG og))
       iv <- G (Call (unG (solve ptag v)))
       idesc_gen (f iv) i

  data Description a i = Description
    { func   :: Func a i
    , to     :: i -> Ex -> a
    , muConv :: Ex -> i
    }

  genDesc :: forall a i . Description a i -> i -> G a a
  genDesc desc x = to desc x <$> (G (CallF x (unG . genF) (muConv desc)))
    where genF :: i -> G Ex Ex
          genF ix = idesc_gen (func desc ix) ix

  asEither :: x -> Either a b
  asEither = unsafeCoerce

  asPair :: x -> (a , b)
  asPair = unsafeCoerce

  asUnit :: x -> ()
  asUnit = unsafeCoerce

  asNat :: x -> Nat
  asNat = unsafeCoerce

  unEx :: (forall a . a -> b) -> Ex -> b
  unEx f (Ex x) = f x

  asBool :: x -> Bool
  asBool = unsafeCoerce

  ----------------------------------------------------------------------------
  -- Finite sets

  finFunc :: Func Nat Nat
  finFunc Zero    = Empty
  finFunc (Suc n) =
    (SSuc (SSuc SZero)) :+>
    (   One
    ::: Var n
    ::: VNil
    )

  toFin :: Nat -> Ex -> Nat
  toFin (Suc n) (Ex x) = 
    case asEither x of
      (Left _) -> Zero
      (Right x) ->
        case asEither x of
          (Left x) ->
            case asPair x of
              (n' , rc) -> Suc (toFin n' (Ex rc))

  fin :: Description Nat Nat
  fin = Description
    { func   = finFunc
    , to     = toFin
    , muConv = unEx asNat
    }

  instance IndexedGeneratable Nat Nat where
    genIndexed   = genDesc fin
    giMuConv   _ = unEx asNat


  ----------------------------------------------------------------------------
  -- Vectors

  vecFunc :: Generatable a => Proxy a -> Func [a] Nat
  vecFunc _ Zero    = One
  vecFunc p (Suc n) = K p (const ()) :*: (Var n)

  toVec :: Nat -> Ex -> [a]
  toVec Zero (Ex x) =
    case asUnit x of
      () -> []
  toVec (Suc n) (Ex x) = error "should redefine" {-
    case asPair x of
      (a , b) -> a : (toVec n (Ex b)) -}

  vec :: Generatable a => Description [a] Nat
  vec = Description
    { func   = vecFunc Proxy
    , to     = toVec
    , muConv = unEx asNat
    }

  ----------------------------------------------------------------------------
  -- Well-scoped terms

  instance DepthCalc () where
    depth () = 0

  data Term a = VarT a
            | AbsT a (Term a)
            | AppT (Term a) (Term a)
            deriving (Show, Eq , Generics.Generic, DepthCalc)

  termFunc :: Func (Term Nat) Nat
  termFunc n =
    SSuc (SSuc (SSuc SZero)) :+>
    (   K (Proxy :: Proxy Nat) id
    ::: Var (Suc n)
    ::: Var n :*: Var n
    ::: VNil
    )

  toTerm :: Nat -> Ex -> Term Nat
  toTerm n (Ex x) = 
    case asEither x of
      (Left a)  -> VarT (asNat a)
      (Right b) ->
        case asEither b of
          (Left t') ->
            case asPair t' of
              (n' , r) -> AbsT Zero (toTerm n' (Ex r))
          (Right t') ->
            case asEither t' of
              (Left ts) ->
                case asPair ts of
                  (t1 , t2) ->
                    let (n1 , r1) = asPair t1 in
                    let (n2 , r2) = asPair t2 in 
                    AppT (toTerm n1 (Ex r1)) (toTerm n2 (Ex r2)) 

  term :: Description (Term Nat) Nat
  term = Description
     { func   = termFunc
    , to     = toTerm
    , muConv = unEx asNat
    }

  termGen :: Nat -> G (Term Nat) (Term Nat)
  termGen i = genDesc term i

  runTermGen :: Nat -> Int -> [(Term Nat)]
  runTermGen = runI (unEx asNat) termGen

  instance Ord Nat where
    Zero <= n = True
    (Suc n) <= Zero = False
    (Suc n) <= Suc m = n <= m

  well_scoped :: (Term Nat) -> Bool
  well_scoped = well_scoped' Zero
    where well_scoped' :: Nat -> (Term Nat) -> Bool
          well_scoped' n (VarT n') = n' <= n
          well_scoped' n (AbsT _ t) = well_scoped' (Suc n) t
          well_scoped' n (AppT t1 t2) = well_scoped' n t1 && well_scoped' n t2

  ----------------------------------------------------------------------------
  -- Rose Trees

  data Rose a = a :> [Rose a] deriving (Show)

  data RLabel = RL | RT

  asLabel :: Ex -> RLabel
  asLabel (Ex x) = unsafeCoerce x

  data RoseTree' a = RoseNode' a (RoseTree' a)
                   | RoseNil'
                   | RoseCons' (RoseTree' a) (RoseTree' a)

  genRose' :: Generatable a => RLabel -> G (RoseTree' a) (RoseTree' a)
  genRose' RL = pure RoseNil' <|> RoseCons' <$> mu (Ex RT) <*> mu (Ex RL)
  genRose' RT = RoseNode' <$> G (Call (unG gen)) <*> mu (Ex RL)

  toRose :: RoseTree' a -> Rose a
  toRose (RoseNode' v rs) = v :> toRose' rs 

  toRose' :: RoseTree' a -> [Rose a]
  toRose' RoseNil' = []
  toRose' (RoseCons' x xs) = toRose x : toRose' xs

  genRose :: Generatable a => RLabel -> G (Rose a) (Rose a)
  genRose l = toRose <$> (G (CallF RT (unG . genRose') asLabel))

  runRoseGen :: Int -> [Rose Bool]
  runRoseGen = runI asLabel genRose RT

  ----------------------------------------------------------------------------
  -- Sized Trees

  data Tree = Leaf
            | Node Tree Tree
            deriving (Eq , Show)

  treeFunc :: Func Tree Nat
  treeFunc Zero    = One
  treeFunc (Suc n) = Sigma (Proxy :: Proxy Plus) (pure n) (\(n' , m') -> Var n' :*: Var m') 

  data FTag = Plus
            | Choose
            | Equal
 
  class (Show i , Show o) => Solve (t :: FTag) i o where
    solve :: Proxy t -> o -> G i i

  instance (Show a , Eq a) => Solve Equal () (a,a) where
    solve _ (x, y) | x == y    = pure ()
                   | otherwise = empty

  instance (Show a , Eq a) => Solve Choose a a where
    solve _ x = pure x 

  reversePlus :: Nat -> G (Nat, Nat) (Nat , Nat)
  reversePlus Zero = pure (Zero , Zero)
  reversePlus (Suc n) =  pure (Suc n , Zero)
                     <|> ((\(x, y) -> (x , Suc y)) <$> reversePlus n)

  instance Solve Plus (Nat , Nat) Nat where
    solve _ = reversePlus

  toTree :: Nat -> Ex -> Tree
  toTree Zero _ = Leaf
  toTree (Suc n) (Ex x) =
    case asPair x of
      (a , b) ->
        case asPair a of
          (ix1 , v1) -> 
            case asPair b of
              (ix2 , v2) -> Node (toTree ix1 (Ex v1)) (toTree ix2 (Ex v2))

  tree :: Description Tree Nat
  tree = Description
    { func   = treeFunc
    , to     = toTree
    , muConv = unEx asNat
    }

  runTreeGen :: Nat -> Int -> [Tree]
  runTreeGen = runI (unEx asNat) (genDesc tree)

  ----------------------------------------------------------------------------
  -- Well typed terms

  type Id = String

  data Ty = T | Ty :->: Ty deriving (Show , Eq)

  data Ctx = CtxEmpty | CtxCons Id Ty Ctx deriving (Show , Eq)

  ctxFromList :: [(Id , Ty)] -> Ctx
  ctxFromList []           = CtxEmpty
  ctxFromList ((id,ty):xs) = CtxCons id ty (ctxFromList xs)

  (!!~) :: Ctx -> Nat -> (Id , Ty)
  CtxEmpty            !!~ n       = error "cannot index empty context"
  (CtxCons id ty ctx) !!~ Zero    = (id , ty)
  (CtxCons id ty ctx) !!~ (Suc n) = ctx !!~ n

  memFunc :: Func String (Ctx , Ty)
  memFunc (CtxEmpty , ty) = Empty
  memFunc (CtxCons id ty1 ctx , ty2) =
    SSuc (SSuc SZero) :+>
    (   Sigma (Proxy :: Proxy Equal) (pure (ty1 , ty2)) (\() -> One)
    ::: Var (ctx , ty2)
    ::: VNil
    )

  toId :: (Ctx , Ty) -> Ex -> String
  toId (CtxCons id ty1 ctx , ty2) (Ex x) =
    case asEither x of
      (Left l) ->
        case asUnit l of
          () -> id -- Top rule
      (Right r) ->
        case asEither r of
          (Left l') ->
            case asPair l' of
              (ix' , rc) -> toId ix' (Ex rc)

  ctx1 :: Ctx
  ctx1 = ctxFromList
    [ ("a" , T :->: T)
    , ("b" , T)
    , ("c" , T :->: (T :->: T))
    , ("d" , T)
    ]

  mem :: Description String (Ctx , Ty)
  mem = Description
    { func = memFunc
    , to   = toId
    , muConv = unEx unsafeCoerce
    }

  instance IndexedGeneratable String (Ctx, Ty) where
    genIndexed = genDesc mem
    giMuConv _ = unEx unsafeCoerce

  runMemGen :: (Ctx, Ty) -> Int -> [String]
  runMemGen = runI (unEx unsafeCoerce) (genDesc mem)

  tyGen :: G Ty Ty
  tyGen = pure T <|> (:->:) <$> mu (Ex ()) <*> mu (Ex ())

  idGen :: G Id Id
  idGen = pure "aa" <|> pure "bb" <|> pure "cc"

  wttermFunc :: Func (Term String) (Ctx , Ty)
  wttermFunc (ctx , T)          =
    SSuc (SSuc SZero) :+>
      (   K (Proxy :: Proxy String) id
      ::: Sigma (Proxy :: Proxy Choose) tyGen (\ty -> Var (ctx , ty :->: T) :*: Var (ctx, ty))
      ::: VNil
      )
  wttermFunc (ctx , ty1 :->: ty2) =
    SSuc (SSuc (SSuc SZero)) :+>
      (   K (Proxy :: Proxy String) id
      ::: Sigma (Proxy :: Proxy Choose) idGen (\id -> Var (CtxCons id ty1 ctx , ty2))
      ::: Sigma (Proxy :: Proxy Choose)
            tyGen (\ty -> Var (ctx , ty :->: (ty1 :->: ty2)) :*: Var (ctx, ty))
      ::: VNil
      )

  toWtTerm :: (Ctx, Ty) -> Ex -> Term String
  toWtTerm (ctx, T) (Ex x) =
    case asEither x of
      Left l   -> VarT l
      Right r -> 
        case asEither r of
          Left l' ->
            case asPair l' of
              ((i1 , t1) , (i2 , t2)) -> AppT
                (toWtTerm i1 (Ex t1))
                (toWtTerm i2 (Ex t2))
  toWtTerm (ctx, ty1 :->: ty2) (Ex x) =
    case asEither x of
      Left l -> VarT l
      Right r ->
        case asEither r of
          Left ((CtxCons id' ty' ctx' , ty'') , t) ->
            AbsT id' (toWtTerm (CtxCons id' ty' ctx', ty'') (Ex t))
          Right r' -> 
            case asEither r' of
              Left l'' ->
                case asPair l'' of
                  ((i1 , t1) , (i2 , t2)) -> AppT
                    (toWtTerm i1 (Ex t1))
                    (toWtTerm i2 (Ex t2))
                

  contains :: Ctx -> String -> Ty -> Bool
  contains CtxEmpty id ty = False
  contains (CtxCons id1 ty1 ctx) id2 ty2 = (ty1 == ty2 && id1 == id2) || contains ctx id2 ty2  

  well_typed :: Ctx -> Ty -> Term String -> Bool
  well_typed ctx ty (VarT x) = contains ctx x ty
  well_typed ctx (ty1 :->: ty2) (AbsT id tm) = well_typed (CtxCons id ty1 ctx) ty2 tm
  well_typed ctx ty (AppT tm1 tm2) =
    any (\sig -> well_typed ctx (sig :->: ty) tm1 && well_typed ctx sig tm2) (run tyGen 4)
  well_typed ctx ty tm = False

  wtterm :: Description (Term String) (Ctx , Ty)
  wtterm = Description
    { func   = wttermFunc
    , to     = toWtTerm
    , muConv = unEx unsafeCoerce
    }

  runWtTermGen :: (Ctx, Ty) -> Int -> [Term String]
  runWtTermGen = runI (unEx unsafeCoerce) (genDesc wtterm)
  
  ----------------------------------------------------------------------------
  -- Regular expressions
  {-
  data ∈ᵣ : Regex → Set where

    [Char] : ∀ {c}
             ----------
           → ∈ᵣ (`c c)

    [One] : ------
            ∈ᵣ one

    [Left] : ∀ {r r'} → ∈ᵣ r
             ---------------
           → ∈ᵣ (r `+ r')

    [Right] : ∀ {r r'} → ∈ᵣ r'
              ----------------
            → ∈ᵣ (r `+ r')

    [Seq] : ∀ {r r'} → ∈ᵣ r → ∈ᵣ r'
            -----------------------
          → ∈ᵣ (r `∙ r')

    [Step] : ∀ {r} → ∈ᵣ r → ∈ᵣ (r *)
             -----------------------
           → ∈ᵣ (r *)

    [Stop] : ----------------
             ∀ {r} → ∈ᵣ (r *)

  rD : func zeroL Regex Regex
  rD = func.mk λ
    { (`c x) → `1
    ; zero → `σ 0 λ ()
    ; one → `1
    ; (r `+ r') →
        `σ 2 λ 
          { ∙     → `var r
          ; (▻ ∙) → `var r' 
          }
    ; (r `∙ r') → `var r `× `var r' 
    ; (r *) →
        `σ 2 λ
          { ∙     → `var r `× `var (r *)
          ; (▻ ∙) → `1
          }
    }

-}

  data Regex = RChar Char
             | RZero
             | ROne
             | RPlus Regex Regex
             | RSeq Regex Regex
             | RStar Regex

  regexFunc :: Func String Regex
  regexFunc (RChar c) = One
  regexFunc (RZero) = Empty
  regexFunc (ROne) = One
  regexFunc (RPlus r r') =
    SSuc (SSuc SZero) :+>
      (   Var r
      ::: Var r'
      ::: VNil
      )
  regexFunc (RSeq r r') = Var r :*: Var r'
  regexFunc (RStar r)  =
    SSuc (SSuc SZero) :+>
      (   Var r :*: Var (RStar r)
      ::: One
      ::: VNil
      )

  toRString :: Regex -> Ex -> String
  toRString (RChar c) (Ex x) =
    case asUnit x of
      () -> [c]
  toRString ROne (Ex x) =
    case asUnit x of
      () -> []
  toRString (RPlus _ _) (Ex x) =
    case asEither x of
      (Left (ri , v)) -> toRString ri (Ex v)
      (Right r) ->
        case asEither r of
          Left (ri , v) -> toRString ri (Ex v)
  toRString (RSeq _ _) (Ex x) =
    case asPair x of
      ((ril , vl) , (rir, vr)) -> toRString ril (Ex vl) ++ toRString rir (Ex vr) 
  toRString (RStar _) (Ex x) =
    case asEither x of
      (Left l) ->
        case asPair l of
          ((ril , vl) , (rir, vr)) -> toRString ril (Ex vl) ++ toRString rir (Ex vr) 
      (Right r) ->
        case asEither r of
          Left () -> []

  rstring :: Description String Regex
  rstring = Description
    { func = regexFunc
    , to = toRString
    , muConv = unEx unsafeCoerce
    }

  runRStringGen :: Regex -> Int -> [String]
  runRStringGen = runI (unEx unsafeCoerce) (genDesc rstring)

