module SOAS.Var

import SOAS.Context
import SOAS.Family

prefix 4 %%
infixr 3 ~> , ~:>

public export
data (.varPos) : (ctx : type.Ctx) -> (0 x : String) -> type -> Type
    where [search x]
  Here  : (ctx :< (x :- ty)).varPos x ty
  There : ctx.varPos x ty -> (ctx :< sy).varPos x ty

public export
data (.var) : type.Ctx -> type -> Type where
  (%%) : (0 name : String) -> {auto pos : ctx.varPos name ty} -> ctx.var ty

0
(.name) : ctx.var ty -> String
(%% name).name = name

export
(.pos) : (v : ctx.var ty) -> ctx.varPos v.name ty
((%% name) {pos}).pos = pos

export
(.toVar) : (v : ctx.varPos x ty) -> ctx.var ty
pos.toVar {x} = (%% x) {pos}

export
ThereVar : (v : ctx.var ty) -> (ctx :< ex).var ty
ThereVar v = (%% v.name) {pos = There v.pos}

public export
Var : type.SortedFamily
Var = flip (.var)

public export 0
(.subst) : {type : Type} -> type.SortedFamily -> type.Ctx -> type.Ctx -> Type
f.subst ctx1 ctx2 = type.gensubst Var f ctx1 ctx2

public export 0
(.substNamed) : {type : Type} -> type.SortedFamily -> type.Ctx -> type.Ctx -> Type
f.substNamed ctx1 ctx2 = {0 x : String} -> {0 ty : type} -> ctx1.varPos x ty -> f ty ctx2

public export 0
(~>) : {type : Type} -> (src, tgt : type.Ctx) -> Type
(~>) = (Var).subst

public export 0
(~:>) : {type : Type} -> (src, tgt : type.Ctx) -> Type
(~:>) = (Var).substNamed

weakl : (ctx1, ctx2 : type.Ctx) -> ctx1 ~> (ctx1 ++ ctx2)
weakl ctx1 [<] x = x
weakl ctx1 (ctx2 :< z) x = ThereVar (weakl ctx1 ctx2 x)

weakrNamed : (ctx1, ctx2 : type.Ctx) -> ctx2 ~:> (ctx1 ++ ctx2)
weakrNamed ctx1 (ctx :< (x :- ty)) Here = (%% x) {pos = Here}
weakrNamed ctx1 (ctx :< sy) (There pos) =
  ThereVar $ weakrNamed ctx1 ctx pos

weakr : (ctx1, ctx2 : type.Ctx) -> ctx2 ~> (ctx1 ++ ctx2)
weakr ctx1 ctx2 ((%% name) {pos}) = weakrNamed ctx1 ctx2 pos

(.copairPos) :
  (0 x : type.SortedFamily) -> {auto length : ctx2.Erased} ->
  x.subst ctx1 ctx -> x.subst ctx2 ctx -> x.substNamed (ctx1 ++ ctx2) ctx
x.copairPos {length = Z} g1 g2 pos = g1 $ pos.toVar
x.copairPos {length = S l} g1 g2 Here = g2 (Here .toVar)
x.copairPos {length = S l} g1 g2 (There pos) =
  x.copairPos g1 (g2 . ThereVar) pos

(.copair) :
  (0 x : type.SortedFamily) -> {auto length : ctx2.Erased} ->
  x.subst ctx1 ctx -> x.subst ctx2 ctx -> x.subst (ctx1 ++ ctx2) ctx
x.copair g1 g2 v = x.copairPos g1 g2 v.pos

export
extend :
  (0 x : type.SortedFamily) ->
  x ty ctx2 -> x.subst ctx1 ctx2 ->
  x.subst (ctx1 :< (n :- ty)) ctx2
extend x {ctx2, ty} u theta = x.copair {length = S Z} theta workaround -- (\case {Here => x})
    where
      workaround : x.subst [< (n :- ty)] ctx2
      workaround ((%% _) {pos = Here}) = u

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
