-- The minimal signature with a binder of VARIABLE ARITY:
-- `letN n p e body` binds n term variables at once in `body`.

expr : Type
pat  : Type

app  : expr -> expr -> expr
lam  : (expr -> expr) -> expr
pnil : pat
pcons: pat -> pat
letN : #n -> pat -> expr -> (expr ^ n -> expr) -> expr
