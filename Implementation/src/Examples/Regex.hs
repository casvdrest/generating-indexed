{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module IDesc.Regex where

  import Data.Proxy
  import Gen
  import Enumerate
  import Depth
  import Data.Singletons
  import Control.Applicative
  import Unsafe.Coerce
  import qualified GHC.Generics as Generics

  import IDesc.IDesc
  import IDesc.Instances


----------------------------------------------------------------------------
  -- Regular expressions

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

  toRString :: Regex -> Anything -> String
  toRString (RChar c) (Hidden x) =
    case asUnit x of
      () -> [c]
  toRString ROne (Hidden x) =
    case asUnit x of
      () -> []
  toRString (RPlus _ _) (Hidden x) =
    case asEither x of
      (Left (ri , v)) -> toRString ri (Hidden v)
      (Right r) ->
        case asEither r of
          Left (ri , v) -> toRString ri (Hidden v)
  toRString (RSeq _ _) (Hidden x) =
    case asPair x of
      ((ril , vl) , (rir, vr)) -> toRString ril (Hidden vl) ++ toRString rir (Hidden vr) 
  toRString (RStar _) (Hidden x) =
    case asEither x of
      (Left l) ->
        case asPair l of
          ((ril , vl) , (rir, vr)) -> toRString ril (Hidden vl) ++ toRString rir (Hidden vr) 
      (Right r) ->
        case asEither r of
          Left () -> []

  rstring :: Description String Regex
  rstring = Description
    { func = regexFunc
    , to = toRString
    }

  runRStringGen :: Regex -> Int -> [String]
  runRStringGen = run (genDesc rstring)

