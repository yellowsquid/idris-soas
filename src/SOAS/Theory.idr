module SOAS.Theory

import SOAS.Algebra
import SOAS.Context
import SOAS.Family
import SOAS.Strength
import SOAS.Structure
import SOAS.Var

public export
record (.Initial)
         (signature : type.SortedFunctor)
         (meta : type.SortedFamily)
         (a : type.SortedFamily) where
  constructor MkInitial
  metalg : signature.MetaAlg meta a
  sem :
    (0 b : type.SortedFamily) ->
    (metalg : signature.MetaAlg meta b) =>
    a -|> b

%hint
public export
(.pointedCoalgStruct) :
  (str : Strength signature) =>
  signature.Initial meta a -> type.PointedCoalgStruct a
init.pointedCoalgStruct = MkPointedCoalgStruct
  { ren = init.sem ([] a) @{traverse init.metalg.alg init.metalg.var init.metalg.mvar}
  , var = init.metalg.var
  }


%hint
public export
(.monStruct) :
  (str : Strength signature) =>
  signature.Initial meta a -> type.MonStruct a
init.monStruct = MkSubstMonoidStruct
  { var = init.metalg.var
  , mult = init.sem (a ^ a) @{traverse init.metalg.alg id init.metalg.mvar}
  }

%hint
public export
(.monoidStruct) :
  (str : Strength signature) =>
  signature.Initial meta a -> signature.MonoidStruct a
init.monoidStruct = MkSignatureMonoid { mon = init.monStruct , alg = init.metalg.alg }
