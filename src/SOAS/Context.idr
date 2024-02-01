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
  S : ctx.Erased -> (ctx :< x).Erased

public export
(.toNat) : ctx.Erased -> Nat
(Z).toNat = 0
(S length).toNat = S length.toNat

public export
(++) : (ctx1,ctx2 : type.Ctx) -> type.Ctx
ctx1 ++ [<] = ctx1
ctx1 ++ (ctx2 :< ty) = (ctx1 ++ ctx2) :< ty
