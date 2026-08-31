-- Martin-Lof type theory, core.
-- ONE syntactic sort: types ARE terms.

tm : Type

-- dependent function type and its introduction/elimination
Pi   : tm -> (tm -> tm) -> tm
lam  : tm -> (tm -> tm) -> tm
app  : tm -> tm -> tm

-- a universe
U    : tm

-- natural numbers with the dependent eliminator
Nat    : tm
zeroN  : tm
sucN   : tm -> tm
natrec : (tm -> tm) -> tm -> (tm -> tm -> tm) -> tm -> tm
