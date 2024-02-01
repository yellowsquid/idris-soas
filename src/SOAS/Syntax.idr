module SOAS.Syntax

import SOAS.Algebra
import SOAS.Context
import SOAS.Family
import SOAS.Strength
import SOAS.Structure
import SOAS.Theory
import SOAS.Var

--------------------------------------------------------------------------------
-- Signatures

public export
(.ParamsErased) : (type.Ctx, type).Ctx -> Type
params.ParamsErased = params.All (\_, extty => (fst extty).Erased)

public export
record (.Signature) (type : Type) where
  constructor MkSig
  0 ops : (ty : type) -> (params : (type.Ctx, type).Ctx) -> Type
  erased :
    {0 ty : type} -> {0 params : (type.Ctx, type).Ctx} ->
    (op : ops ty params) -> params.ParamsErased

--------------------------------------------------------------------------------
-- Functor

public export
data (.Args) : (type.Ctx, type).Ctx -> type.SortedFamily -> type.Family where
  Lin  : [<].Args a ctx
  (:<) :
    params.Args a ctx ->
    BindRename ext a ty ctx ->
    (params :< (n :- (ext, ty))).Args a ctx

public export
data (.functor) : type.Signature -> type.SortedFunctor where
  Op : (op : sig.ops ty params) -> (args : params.Args a ctx) -> sig.functor a ty ctx

--------------------------------------------------------------------------------
-- Functoriality

argsMap : (a -|> b) -> params.Args a -||> params.Args b
argsMap f [<] = [<]
argsMap f (sx :< (Bind names x)) = argsMap f sx :< (Bind names $ f x)

export
%hint
(.functorMap) : (0 sig : type.Signature) -> sig.functor.Map
sig.functorMap = MkMap $ \f => \(Op op args) => Op op (argsMap f args)

--------------------------------------------------------------------------------
-- Strength

argsStr :
  (erased : params.ParamsErased) -> (mon : type.PointedCoalgStruct p) =>
  params.Args (x ^ p) -||> params.Args x ^^ p
argsStr [<] [<] {ctx} theta = [<]
argsStr (erased :< length) (sx :< (Bind names x)) {ctx} theta =
  argsStr erased sx theta :< (Bind names $ x $ lift (erasedRename length) theta)

export
%hint
(.functorStrength) :
  (sig : type.Signature) -> Strength sig.functor
sig.functorStrength = MkStrength $
  \(Op op args), theta => Op op (argsStr (sig.erased op) args theta)

--------------------------------------------------------------------------------
-- Terms

public export
data (.Term) : (sig : type.Signature) -> type.SortedFunctor where
  Var : Var -|> sig.Term a
  Alg : sig.functor (sig.Term a) -|> sig.Term a
  MVar : a -|> sig.Term a ^ sig.Term a

%hint
export
(.TermMetalg) : (sig : type.Signature) -> sig.functor.MetaAlg meta (sig.Term meta)
sig.TermMetalg = MkMetaAlg { alg = Alg, var = Var, mvar = MVar }

%hint
export
(.TermInitial) : (sig : type.Signature) -> sig.functor.Initial meta (sig.Term meta)
sig.TermInitial = MkInitial
  { metalg = sig.TermMetalg
  , sem = sem
  }
  where
  sem : (0 b : type.SortedFamily) -> (metalg : sig.functor.MetaAlg meta b) => sig.Term meta -|> b
  semArgs :
    (0 b : type.SortedFamily) -> (metalg : sig.functor.MetaAlg meta b) =>
    {0 params : (type.Ctx, type).Ctx} ->
    params.Args (sig.Term meta) -||> params.Args b

  sem b (Var v) = metalg.var v
  sem b (Alg (Op op args)) = metalg.alg $ Op op $ semArgs b args
  sem b (MVar m f) = metalg.mvar m $ \v => sem b (f v)

  semArgs b [<] = [<]
  semArgs b (sx :< (Bind names x)) = semArgs b sx :< (Bind names $ sem b x)
