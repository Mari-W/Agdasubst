-- Signature for System F with external (unscoped) literal arguments

-- the sorts
ty : Type
tm : Type

-- the constructors for ty
arr : ty -> ty -> ty
all : (ty -> ty) -> ty

-- the constructors for tm
app  : tm -> tm -> tm
lam  : ty -> (tm -> tm) -> tm
tapp : tm -> ty -> tm
tlam : (ty -> tm) -> tm

-- external (unscoped) constructors
const  : "String" -> tm
tagged : "String" -> tm -> tm
pair   : "String" -> "ℕ" -> tm -> tm -> tm
