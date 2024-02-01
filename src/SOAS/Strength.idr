module SOAS.Strength

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
  strength :
    (0 p,x : type.SortedFamily) ->
    (mon : type.PointedCoalgStruct p) ->
    (f (x ^ p)) -|> ((f x) ^ p)

export
(.str) :
  Strength f ->
  {0 p,x : type.SortedFamily} ->
  (mon : type.PointedCoalgStruct p) =>
  (f (x ^ p)) -|> ((f x) ^ p)
strength.str {p,x,mon} = strength.strength p x mon

public export
record (.Map) (signature : type.SortedFunctor) where
  constructor MkMap
  map :
    {0 a,b : type.SortedFamily} -> (a -|> b) ->
    signature a -|> signature b
