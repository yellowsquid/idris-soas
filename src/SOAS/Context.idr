module SOAS.Context

infixr 4 :-

public export
record (.extension) (type : Type) where
  constructor (:-)
  0 name : String
  ofType : type

public export
data (.Ctx) : (type : Type) -> Type where
  Lin : type.Ctx
  (:<) : (ctx : type.Ctx) -> (namety : type.extension) -> type.Ctx

public export
data (.Erased) : type.Ctx -> Type where
  Z : [<].Erased
  S : ctx.Erased -> (ctx :< (n :- ty)).Erased

public export
(.toNat) : ctx.Erased -> Nat
(Z).toNat = 0
(S length).toNat = S length.toNat

public export
(++) : (ctx1,ctx2 : type.Ctx) -> type.Ctx
ctx1 ++ [<] = ctx1
ctx1 ++ (ctx2 :< ty) = (ctx1 ++ ctx2) :< ty

namespace All
  public export
  data (.All) : type.Ctx -> (p : (0 n : String) -> type -> Type) -> Type where
    Lin : [<].All p
    (:<) : ctx.All p -> p n ty -> (ctx :< (n :- ty)).All p

  public export
  head : (ctx :< (n :- ty)).All p -> p n ty
  head (sx :< px) = px

  public export
  tail : (ctx :< (n :- ty)).All p -> ctx.All p
  tail (sx :< px) = sx

public export
(.rename) : (ctx : type.Ctx) -> (0 names : ctx.All (\_,_ => String)) -> type.Ctx
[<].rename names = [<]
(ctx :< (_ :- ty)).rename names = ctx.rename (tail names) :< (head names :- ty)

export
erasedRename : ctx.Erased -> (ctx.rename names).Erased
erasedRename Z = Z
erasedRename (S length) = S (erasedRename length)
