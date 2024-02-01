module SOAS.Structure

import SOAS.Context
import SOAS.Family
import SOAS.Var

-- Pointed Coalgebra

public export
record (.PointedCoalgStruct) type (x : type.SortedFamily) where
  constructor MkPointedCoalgStruct
  ren : x -|> [] x
  var : Var -|> x

%hint
(.VarPointedCoalgStruct) : (0 type : Type) -> type.PointedCoalgStruct Var
type.VarPointedCoalgStruct = MkPointedCoalgStruct
  { ren = \i, f => f i
  , var = id
  }

export
lift :
  (length : ctx.Erased) -> (mon : type.PointedCoalgStruct p) =>
  (p.subst ctx1 ctx2) -> p.subst (ctx1 ++ ctx) (ctx2 ++ ctx)
lift length f = p.copair length (\v => mon.ren (f v) weakl) (mon.var . weakr)

-- Substitution Monoid

public export
record (.MonStruct) (type : Type) (m : type.SortedFamily) where
  constructor MkSubstMonoidStruct
  var : Var -|> m
  mult : m -|> (m ^ m)

export
(.wkn) :
  (0 m : type.SortedFamily) -> (mon : type.PointedCoalgStruct m) =>
  m sy ctx -> m sy (ctx :< (n :- ty))
m.wkn t = mon.ren t (weakl {length = S Z})

export
(.sub) :
  (0 m : type.SortedFamily) -> (mon : type.MonStruct m) =>
  m sy (ctx :< (n :- ty)) -> m ty ctx -> m sy ctx
m.sub t s = mon.mult t (m.extend s mon.var)

export
(.sub2) :
  (0 m : type.SortedFamily) -> (mon : type.MonStruct m) =>
  m sy (ctx :< (x :- ty1) :< (x :- ty2)) ->
  m ty1 ctx ->  m ty2 ctx -> m sy ctx
m.sub2 t s1 s2 = mon.mult t (m.extend s2 (m.extend s1 mon.var))
