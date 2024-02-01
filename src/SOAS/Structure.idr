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

liftPos :
  (length : ctx.Erased) -> (mon : type.PointedCoalgStruct p) =>
  (p.subst ctx1 ctx2) -> p.substNamed (ctx1 ++ ctx) (ctx2 ++ ctx)
liftPos Z     f x = f x.toVar
liftPos (S l) f Here        = mon.var (Here .toVar)
liftPos (S l) f (There pos) = mon.ren (liftPos l f pos) ThereVar

export
lift :
  (length : ctx.Erased) -> (mon : type.PointedCoalgStruct p) =>
  (p.subst ctx1 ctx2) -> p.subst (ctx1 ++ ctx) (ctx2 ++ ctx)
lift ctx f v = liftPos ctx f v.pos

-- Substitution Monoid

public export
record (.MonStruct) (type : Type) (m : type.SortedFamily) where
  constructor MkSubstMonoidStruct
  var : Var -|> m
  mult : m -|> (m ^ m)

export
(.sub) :
  (mon : type.MonStruct m) ->
  m sy (ctx :< (n :- ty)) -> m ty ctx -> m sy ctx
mon.sub t s = mon.mult t (extend m s mon.var)

export
(.sub2) :
  (mon : type.MonStruct m) ->
  m sy (ctx :< (x :- ty1) :< (x :- ty2)) ->
  m ty1 ctx ->  m ty2 ctx -> m sy ctx
mon.sub2 t s1 s2 = mon.mult t (extend m s2 (extend m s1 mon.var))
