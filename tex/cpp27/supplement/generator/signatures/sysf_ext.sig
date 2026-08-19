% open import Data.String using (String)
% open import Data.Nat using (ℕ)

-- Signature for System F with external (unscoped) literal arguments
-- and unicode constructor / sort names.

ty : Type
tm : Type

arr : ty -> ty -> ty
all : (ty -> ty) -> ty

app  : tm -> tm -> tm
lam  : ty -> (tm -> tm) -> tm
tapp : tm -> ty -> tm
tlam : (ty -> tm) -> tm

-- External (unscoped) constructors carrying literal Agda values.
const  : "String" -> tm
tagged : "String" -> tm -> tm
pair   : "String" -> "ℕ" -> tm -> tm -> tm

-- Unicode-named constructors.
α→β  : tm -> tm -> tm
mkℕ′ : "ℕ" -> tm
