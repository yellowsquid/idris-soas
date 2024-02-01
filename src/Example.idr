module Example

import Data.Singleton
import SOAS

infixr 3 -:>

-- Writing the descriptions directly is fine
-- but deriving their functoriality and strength is annoying
-- and not needed with enough metaprogramming

%hide Syntax.PreorderReasoning.prefix.(|~)
%hide Syntax.PreorderReasoning.Generic.prefix.(|~)

data TypeSTLC = B | (-:>) TypeSTLC TypeSTLC

data OpSTLC : TypeSTLC -> (TypeSTLC .Ctx, TypeSTLC).Ctx -> Type where
  App : OpSTLC ty2 [<"f" :- ([<], ty1 -:> ty2), "x" :- ([<], ty1)]
  Lam : OpSTLC (ty1 -:> ty2) [<"body" :- ([<"x" :- ty1], ty2)]

STLC : TypeSTLC .Signature
STLC = MkSig OpSTLC $ \case
  App => [<Z, Z]
  Lam => [<S Z]

Ex1 : STLC .Term Var (B -:> (B -:> B) -:> B) [<]
Ex1 =
  Alg $ Op Lam [<Bind [<"x"] $
  Alg $ Op Lam [<Bind [<"f"] $
    Alg $ Op App [<[] (Var (%% "f")), [] (Var (%% "x"))]]]

beta :
  {0 body : STLC .Term Var ty2 (ctx :< (x :- ty1))} ->
  Singleton (Alg $ Op App [<[] (Alg $ Op Lam [<Bind [<x] body]), [] t]) ->
  STLC .Term Var ty2 ctx
beta (Val $ Alg $ Op App [<Bind [<] $ Alg $ Op Lam [<Bind [<x] body], Bind [<] t]) =
  (STLC .Term Var).sub body t

eta : STLC .Term Var (ty1 -:> ty2) ctx -> STLC .Term Var (ty1 -:> ty2) ctx
eta t =
  Alg $ Op Lam [<Bind [<"x"] $
    Alg $ Op App [<[] ((STLC .Term Var).wkn t), [] (Var $ %% "x")]]

Ex2 : STLC .Term Var (B -:> B) [<]
Ex2 =
  Alg $ Op App
    [<[] (Alg $ Op Lam [<Bind [<"f"] $
          Alg $ Op Lam [<Bind [<"x"] $
          Alg $ Op App [<[] (Var $ (%% "f") {pos = There Here}), [] (Var $ %% "x")]]])
    , [] (Alg $ Op Lam [<Bind [<"x"] $ Var $ %% "x"])]

Ex3 : STLC .Term Var (B -:> B) [<]
Ex3 = eta $ beta $ Val Ex2
