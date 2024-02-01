module SOAS.Family

import SOAS.Context

infixr 3 -|> , -||> , -<>, =||> , =|> , >>> , ^
infixl 3 <<<

public export
(.Family), ( .SortedFamily) : Type -> Type
type.Family = type.Ctx -> Type
type.SortedFamily = type -> type.Family

public export 0
(-||>) : {type : Type} -> (src,tgt : type.Family) -> Type
(src -||> tgt) = {0 ctx : type.Ctx} -> src ctx -> tgt ctx

public export 0
(-|>) : {type : Type} -> (src,tgt : type.SortedFamily) -> Type
(src -|> tgt) = {0 ty : type} -> src ty -||> tgt ty

public export
(<<<) : type.SortedFamily -> type.Ctx -> type.SortedFamily
(f <<< ctx0) ty ctx = f ty (ctx ++ ctx0)

public export
(>>>) : type.SortedFamily -> type.Ctx -> type.SortedFamily
(f >>> ctx0) ty ctx = f ty (ctx0 ++ ctx)

public export 0
(-<>) : (src, tgt : type.SortedFamily) -> type.SortedFamily
(src -<> tgt) ty ctx = src ty -||> (tgt >>> ctx) ty

public export
(=||>) : (src, tgt : type.Family) -> type.Family
(src =||> tgt) ctx = src ctx -> tgt ctx

public export
(=|>) : (src, tgt : type.SortedFamily) -> type.SortedFamily
(src =|> tgt) ty = src ty =||> tgt ty

public export 0
(.gensubst) : (type : Type) -> (from,to : type.SortedFamily) -> (src,tgt : type.Ctx) -> Type
type.gensubst from to src tgt = {0 ty : type} -> from ty src -> to ty tgt
