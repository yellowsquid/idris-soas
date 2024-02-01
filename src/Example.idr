module Example

import Data.Singleton
import SOAS

infixr 3 -:>

-- Writing the descriptions directly is fine
-- but deriving their functoriality and strength is annoying
-- and not needed with enough metaprogramming

data TypeSTLC = B | (-:>) TypeSTLC TypeSTLC

data STLC : TypeSTLC .SortedFunctor  where
  App : (f : a (ty1 -:> ty2) ctx) ->
        (x : a ty1 ctx) -> STLC a ty2 ctx
  Lam : (x : String) ->
        (body : a ty2 (ctx :< (x :- ty1))) ->
        STLC a (ty1 -:> ty2) ctx

%hint
strSTLC : Strength STLC
strSTLC = MkStrength
  { strength = \p,x,mon => \case
    (App f x) => \theta => App (f theta) (x theta)
    (Lam str {ty1} body) => \theta =>
        Lam str $ body $ p.extend (mon.var (%% str))
      $ \v => mon.ren (theta v)
                      (\u => ThereVar u) -- Bug: can't eta-reduce
  }

%hint
functorialitySTLC : STLC .Map
functorialitySTLC = MkMap
  { map = \h => \case
    (App f x) => App (h f) (h x)
    (Lam str body) => Lam str (h body)
  }

data Term : (meta : type.SortedFamily) -> type.SortedFamily where
  Va : Var -|> Term meta
  Me : meta -|> Term meta ^ Term meta
  Op : STLC (Term meta) -|> Term meta
--   -- La : (x : String) -> bind [< x :- ty1 ] (Term meta) ty2 -||> Term meta (ty1 -:> ty2)
--   -- bug: unification error in Ex1
--   La : (x : String) -> Term meta ty2 (ctx :< (x :- ty1)) -> Term meta (ty1 -:> ty2) ctx
--   -- Ap : Term meta (ty1 -:> ty2) -||> Term meta ty1 =||> Term meta ty2
--   Ap : Term meta (ty1 -:> ty2) ctx -> Term meta ty1 ctx -> Term meta ty2 ctx

%hint
TermMetaAlg : STLC .MetaAlg meta (Term meta)
TermMetaAlg = MkMetaAlg
  { alg = Op
  , var = Va
  , mvar = Me
  }

%hint
TermInitial : STLC .Initial meta (Term meta)
TermInitial = MkInitial
  { metalg = TermMetaAlg
  , bang = bang
  }
  where
    bang : (0 b : TypeSTLC .SortedFamily) -> (metalg : STLC .MetaAlg meta b) -> Term meta -|> b
    bang b metalg (Va v) = metalg.var v
    bang b metalg (Me m theta) = metalg.mvar m (\v => bang b metalg (theta v))
    bang b metalg (Op (Lam str body)) = metalg.alg (Lam str (bang b metalg body))
    bang b metalg (Op (App f x)) = metalg.alg (App (bang b metalg f) (bang b metalg x))

Ex1 : Term Var (B -:> (B -:> B) -:> B) [<]
Ex1 = Op $ Lam "x" $ Op $ Lam "f" $ Op $ App (Va $ %% "f") (Va $ %% "x")

beta :
  {0 body : Term Var ty2 (ctx :< (x :- ty1))} ->
  Singleton (Op $ App (Op $ Lam x body) t) -> Term Var ty2 ctx
beta (Val (Op $ App (Op $ Lam x body) t)) = TermInitial .monStruct.sub body t

Ex2 : Term Var (B -:> B) [<]
Ex2 = Op $ App
        (Op $ Lam "f" $ Op $ Lam "x" $ Op $ App (Va $ %% "f") (Va $ (%% "x") {pos = Here}))
        (Op $ Lam "x" $ Va $ %% "x")

Ex3 : Term Var (B -:> B) [<]
Ex3 = beta $ Val Ex2
