module SOAS.Var

import Data.Nat
import Data.So

import SOAS.Context
import SOAS.Family

prefix 4 %%
infixr 3 ~> , ~:>

--------------------------------------------------------------------------------
-- Variables

public export
data (.varAt) : (ctx : type.Ctx) -> (0 x : String) -> (n : Nat) -> type -> Type
  where [search x]
  Here  : (ctx :< (x :- ty)).varAt x 0 ty
  There : ctx.varAt x n ty -> (ctx :< sy).varAt x (S n) ty

public export
record (.var) (ctx : type.Ctx) (ty : type)  where
  constructor (%%)
  0 name : String
  {idx : Nat}
  {auto 0 pos : ctx.varAt name idx ty}

export
(.toVar) : {n : Nat} -> (0 v : ctx.varAt x n ty) -> ctx.var ty
pos.toVar = %% x

export
ThereVar : (v : ctx.var ty) -> (ctx :< ex).var ty
ThereVar v = (%% v.name) {idx = S v.idx, pos = There v.pos}

public export
Var : type.SortedFamily
Var = flip (.var)

--------------------------------------------------------------------------------
-- Substitutions

public export 0
(.subst) : {type : Type} -> type.SortedFamily -> type.Ctx -> type.Ctx -> Type
f.subst ctx1 ctx2 = type.gensubst Var f ctx1 ctx2

public export 0
(.substNamed) : {type : Type} -> type.SortedFamily -> type.Ctx -> type.Ctx -> Type
f.substNamed ctx1 ctx2 =
  {k : Nat} -> {0 x : String} -> {0 ty : type} -> (0 pos : ctx1.varAt x k ty) -> f ty ctx2

public export 0
(~>) : {type : Type} -> (src, tgt : type.Ctx) -> Type
(~>) = (Var).subst

public export 0
(~:>) : {type : Type} -> (src, tgt : type.Ctx) -> Type
(~:>) = (Var).substNamed

weaklPos :
  (length : ctx2.Erased) -> ctx1.varAt x n ty ->
  (ctx1 ++ ctx2).varAt x (length.toNat + n) ty
weaklPos Z          pos = pos
weaklPos (S length) pos = There (weaklPos length pos)

%inline
weaklNamed : {auto length : ctx2.Erased} -> ctx1 ~:> (ctx1 ++ ctx2)
weaklNamed pos = (weaklPos length pos).toVar

export
weakl : {auto length : ctx2.Erased} -> ctx1 ~> (ctx1 ++ ctx2)
weakl v = weaklNamed v.pos

weakrPos : ctx2.varAt x n ty -> (ctx1 ++ ctx2).varAt x n ty
weakrPos Here        = Here
weakrPos (There pos) = There (weakrPos pos)

weakrNamed : ctx2 ~:> (ctx1 ++ ctx2)
weakrNamed pos = (weakrPos pos).toVar

export
weakr : ctx2 ~> (ctx1 ++ ctx2)
weakr v = weakrNamed v.pos

splitPosL :
  (length : ctx2.Erased) -> (0 lt : So (n < length.toNat)) ->
  (ctx1 ++ ctx2).varAt x n ty -> ctx2.varAt x n ty
splitPosL Z lt Here impossible
splitPosL (S length) lt Here = Here
splitPosL (S length) lt (There pos) = There (splitPosL length lt pos)

splitPosR :
  (length : ctx2.Erased) -> (0 gte : So (not (n < length.toNat))) ->
  (ctx1 ++ ctx2).varAt x n ty -> ctx1.varAt x (minus n length.toNat) ty
splitPosR Z gte pos = rewrite minusZeroRight n in pos
splitPosR (S z) gte (There pos) = splitPosR z gte pos

(.copairNamed) :
  (0 x : type.SortedFamily) -> (length : ctx2.Erased) ->
  x.subst ctx1 ctx -> x.subst ctx2 ctx -> x.substNamed (ctx1 ++ ctx2) ctx
x.copairNamed length g1 g2 {k} pos =
  case choose (k < length.toNat) of
    Left lt => g2 (splitPosL length lt pos).toVar
    Right gte => g1 (splitPosR length gte pos).toVar

export
(.copair) :
  (0 x : type.SortedFamily) -> (length : ctx2.Erased) ->
  x.subst ctx1 ctx -> x.subst ctx2 ctx -> x.subst (ctx1 ++ ctx2) ctx
x.copair length g1 g2 v = x.copairNamed length g1 g2 v.pos

(.singletonNamed) : (0 x : type.SortedFamily) -> x ty ctx -> x.substNamed [<(n :- ty)] ctx
x.singletonNamed {ty} u Here = u
x.singletonNamed {ty} u (There v) impossible -- workaround

(.singleton) : (0 x : type.SortedFamily) -> x ty ctx -> x.subst [<(n :- ty)] ctx
x.singleton {ty} u v = x.singletonNamed u v.pos

export
(.extend) :
  (0 x : type.SortedFamily) ->
  x ty ctx2 -> x.subst ctx1 ctx2 ->
  x.subst (ctx1 :< (n :- ty)) ctx2
x.extend {ty} u theta = x.copair (S Z) theta (x.singleton u)

--------------------------------------------------------------------------------
-- Families

public export 0
(^) : (tgt, src : type.SortedFamily) -> type.SortedFamily
(tgt ^ src) ty ctx = src.subst ctx -||> tgt ty

public export 0
Nil : type.SortedFamily -> type.SortedFamily
Nil f = f ^ Var

0
(*) : (derivative, tangent : type.SortedFamily) -> type.SortedFamily
(derivative * tangent) ty ctx =
  (ctx' : type.Ctx ** (derivative ty ctx' , tangent.subst ctx' ctx))
