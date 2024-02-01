module SOAS.Strength

import SOAS.Context
import SOAS.Family
import SOAS.Structure
import SOAS.Var

public export
0
(.SortedFunctor) : (type : Type) -> Type
type.SortedFunctor = type.SortedFamily -> type.SortedFamily

public export
record Strength (f : type.SortedFunctor) where
  constructor MkStrength
  str :
    {0 p,x : type.SortedFamily} ->
    (mon : type.PointedCoalgStruct p) =>
    (f (x ^ p)) -|> ((f x) ^ p)

public export
record (.Map) (signature : type.SortedFunctor) where
  constructor MkMap
  map :
    {0 a,b : type.SortedFamily} -> (a -|> b) ->
    signature a -|> signature b

public export
bind : (tys : type.Ctx) -> type.SortedFunctor
bind tys = (<<< tys)

public export
record BindRename (tys : type.Ctx) (a : type.SortedFamily) (ty : type) (ctx : type.Ctx) where
  constructor Bind
  0 names : tys.All (\_,_ => String)
  body : a ty (ctx ++ tys.rename names)

public export
Nil : a -|> BindRename [<] a
[] x = Bind [<] x
