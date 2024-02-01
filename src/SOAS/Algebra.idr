module SOAS.Algebra

import SOAS.Context
import SOAS.Family
import SOAS.Strength
import SOAS.Structure
import SOAS.Var

public export
record (.MonoidStruct)
         (signature : type.SortedFunctor)
         (x : type.SortedFamily) where
  constructor MkSignatureMonoid
  mon : type.MonStruct x
  alg : signature x -|> x

public export
record (.MetaAlg)
         (signature : type.SortedFunctor)
         (meta : type.SortedFamily)
         (a : type.SortedFamily) where
  constructor MkMetaAlg
  alg : signature a -|> a
  var : Var -|> a
  mvar : meta -|> (a ^ a)

export
traverse : {0 p,a : type.SortedFamily} ->
      {0 signature : type.SortedFunctor} ->
      (functoriality : signature.Map) =>
      (str : Strength signature) =>
      (coalg : type.PointedCoalgStruct p) =>
      (alg : signature a -|> a) ->
      (phi : p -|> a) ->
      (chi : meta -|> (a ^ a)) -> signature.MetaAlg meta (a ^ p)
traverse {p,a} alg phi chi = MkMetaAlg
      { alg = \h,s => alg $ str.str h s
      , var = \v,s => phi (s v)
      , mvar = \m,e,s => chi m (\v => e v s)
      }
