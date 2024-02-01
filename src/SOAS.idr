module SOAS

import public SOAS.Algebra
import public SOAS.Context
import public SOAS.Family
import public SOAS.Strength
import public SOAS.Structure
import public SOAS.Syntax
import public SOAS.Theory
import public SOAS.Var

-- -- TODO: (Setoid) coalgebras

-- -- Does this follow from everything else?
-- mapSubstPos : {0 a,b : type.SortedFamily} -> (a -|> b) -> {0 ctx : type.Ctx} ->
--   {0 ctx' : type.Ctx} ->
--   a.subst ctx ctx' -> b.substNamed ctx ctx'
-- mapSubstPos f {ctx = (ctx :< (x :- ty))} theta Here
--   = f $ theta {ty} $ (%% _) {pos = Here}
-- mapSubstPos f {ctx = (ctx :< sy)} theta (There pos)
--   = mapSubstPos {a,b} f (theta . ThereVar) pos

-- mapSubst : {0 a,b : type.SortedFamily} -> (a -|> b) -> {0 ctx : type.Ctx} ->
--    (a.subst ctx -||> b.subst ctx)
-- mapSubst f {ctx = ctx0} theta v = mapSubstPos {a,b} f theta v.pos

-- (.MetaCtx) : Type -> Type
-- type.MetaCtx = SnocList (type.Ctx, type)

-- (.metaEnv) : type.SortedFamily -> type.MetaCtx -> type.Family
-- x.metaEnv [<]            ctx = ()
-- x.metaEnv (mctx :< meta) ctx =
--   (x.metaEnv mctx ctx, (x <<< (fst meta)) (snd meta) ctx)

-- {- alas, non obviously strictly positive because we can't tell
--    Idris that signature must be strictly positive.

--    It will be, though, if we complete the termination project
-- -}

-- data (.Term) : (signature : type.SortedFunctor) ->
--                type.SortedFamily -> type.SortedFamily where
--   Op : {0 signature : type.SortedFunctor} ->
--        signature (signature.Term x) ty ctx ->
--        signature.Term x ty ctx
--   Va : Var ty ctx -> signature.Term x ty ctx
--   Me : {0 ctx1, ctx2 : type.Ctx} ->
--        {0 signature : type.SortedFunctor} ->
--        x ty ctx2 ->
--        (signature.Term x).subst ctx2 ctx1 ->
--        signature.Term {type} x ty ctx1

-- (.sem) : (0 a : type.SortedFamily) ->
--          {0 signature : type.SortedFunctor} ->
--          (functoriality : signature.Map) =>
--          (str : Strength signature) =>
--          (metalg : signature.MetaAlg x a) =>
--          signature.Term x -|> a
-- a.sem (Op args) = metalg.alg $ functoriality.map a.sem args
-- a.sem (Va x   ) = MetaAlg.var metalg x
-- a.sem (Me  m env)
--   = MetaAlg.mvar metalg m
--   $ mapSubst {a=signature.Term x, b = a} a.sem env

-- (.envSem) : (0 a : type.SortedFamily) ->
--             {0 signature : type.SortedFunctor} ->
--             (str : Strength signature) =>
--             (functoriality : signature.Map) =>
--             (metalg : signature.MetaAlg x a) =>
--             {mctx : type.MetaCtx} ->
--             (signature.Term x).metaEnv mctx ctx ->
--                              a.metaEnv mctx ctx

-- a.envSem {mctx = [<]         } menv = ()
-- a.envSem {mctx = mctx :< meta} (menv,v) = (a.envSem menv, a.sem v)

-- -- Not sure these are useful
-- data (+) : (signature1, signature2 : type.SortedFunctor) ->
--   type.SortedFunctor where
--   Lft  :  {signature1, signature2 : type.SortedFunctor} ->
--     (op : sig1 x ty ctx) -> (sig1 + sig2) x ty ctx
--   Rgt :  {signature1, signature2 : type.SortedFunctor} ->
--     (op : sig2 x ty ctx) -> (sig1 + sig2) x ty ctx

-- sum : (signatures : List $ (String, type.SortedFunctor)) ->
--   type.SortedFunctor
-- (sum signatures) x ty ctx = Any (\(name,sig) => sig x ty ctx) signatures

-- prod : (signatures : List $ type.SortedFunctor) ->
--   type.SortedFunctor
-- (prod signatures) x ty ctx = All (\sig => sig x ty ctx) signatures
