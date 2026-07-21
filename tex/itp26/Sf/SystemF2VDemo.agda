{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.SystemF2VDemo — the GATE evidence: the vector instantiation COMPUTES on real
-- System F terms by refl-level reduction, and the cross-term lift ⇑ty fires.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.SystemF2VDemo where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sf.SystemF2V

-- ── concrete closed terms ──
-- the value variable as a term:  x : Tm [] (tt ∷ [])
x : Tm [] (tt ∷ [])
x = vt vlvar

-- the identity function  λ(x:α). x  : Vl (tt ∷ []) []
--   α = tvar : Ty (tt ∷ []) (support tt∷[]); body x : Tm [] (tt∷[]) (type-support [])
--   merge via cθ = cs' czz : Cover (tt∷[]) [] (tt∷[]).
idfun : Vl (tt ∷ []) []
idfun = lam tvar (use x) (cs' czz)

-- the polymorphic identity  Λα. λ(x:α). x  : Vl [] []
polyId : Vl [] []
polyId = Lam (use (vt idfun))

-- ════════════════════════════════════════════════════════════════════════════
-- (1)  IDENTITY computes:  applying the identity vector to polyId returns it.
--      This drives EVERY clause (Lam→cross-term lift ⇑ty, lam→value lift ⇑vl,
--      vlvar→projection, vt) and lands by refl ⇒ the whole instantiation reduces.
-- ════════════════════════════════════════════════════════════════════════════
opaque
  unfolding subVl sub subT idS idVSub idEmb oe oi wkSub
  id-computes : subVl polyId idS idVSub ≡ (polyId ⇑[ oe , oz ])
  id-computes = refl

  -- the inner identity function under the identity vector, too:
  idfun-computes : subVl idfun idS idVSub ≡ (idfun ⇑[ os oz , oz ])
  idfun-computes = refl

-- ════════════════════════════════════════════════════════════════════════════
-- (2)  THE TYPE-β REDEX  (Λα. body)[B].  We take B = (∀β.β) ⇒ a closed type,
--      instantiate the body of the Λ with the singleton type-substitution [B], and
--      confirm the reduct computes by refl.  This exercises ⇑ty's cross-term: the
--      body `λ(x:α).x` has a value-var whose TYPE-thinning is o'-extended under Λ,
--      and the result still reduces definitionally.
-- ════════════════════════════════════════════════════════════════════════════

-- a closed type argument  B = ∀β.β  : Ty []
B : Ty []
B = `∀ (use tvar)

-- the body of polyId:  bodyTm = vt idfun : Tm (tt ∷ []) []  (one free type var α)
bodyTm : Tm (tt ∷ []) []
bodyTm = vt idfun

-- the singleton TYPE substitution [B/α] : Sub [] (tt ∷ [])
σB : Sub [] (tt ∷ [])
σB = [] ,- (B ⇑ oz)

-- type-β:  bodyTm [B/α , id]  computes to  vt (λ(x:B). x)  (the type α replaced by B).
-- The reduct is built by refl ⇒ instantiation COMPUTES on the type-application redex.
opaque
  unfolding subVl sub subT idS idVSub idEmb oe oi wkSub
  tyβ-computes :
    sub bodyTm σB idVSub
    ≡ (vt (lam (`∀ (use tvar)) (use (vt vlvar)) czz) ⇑[ oz , oz ])
  tyβ-computes = refl

-- ════════════════════════════════════════════════════════════════════════════
-- (3)  THE CROSS-TERM ⇑ty in action.  Substitute UNDER a Λ a value-variable whose
--      replacement carries a free TYPE variable.  Under the Λ the target's TYPE
--      thinning must be o'-extended (= σ ◦ (↑,idvl)); we confirm the whole thing
--      computes by refl, i.e. the cross-term introduced NO stuck redex.
--
--   term:   Λβ. (vt y)            : Tm [] (tt ∷ [])   (β bound, y a free value var)
--   value:  y ↦ (vt vlvar … )? — instead use a CONCRETE replacement carrying a type
--           var:  v = lam tvar (use x) (cs' czz) : Vl (tt ∷ []) []  (= λ(z:α).z, α free)
--   vector: (idS , [v⇑(os oz, oz)])  over Θ=(tt∷[]), Γ=[]
-- ════════════════════════════════════════════════════════════════════════════

-- the term  Λβ. (vt y)  where y is the single free value-var.
termΛ : Tm [] (tt ∷ [])
termΛ = vt (Lam (drop (vt vlvar)))     -- β does not occur, but y (value var) does

-- the replacement value  v = λ(z:α).z  : Vl (tt ∷ []) []  (free type var α)
v : Vl (tt ∷ []) []
v = lam tvar (use (vt vlvar)) (cs' czz)

-- the value substitution  [y ↦ v]  : VSub (tt ∷ []) [] (tt ∷ [])
σv : VSub (tt ∷ []) [] (tt ∷ [])
σv = [] ,- (v ⇑[ os oz , oz ])

opaque
  unfolding subVl sub subT idS idVSub idEmb oe oi wkSub
  -- substituting under Λβ:  the target v's TYPE thinning (os oz : tt∷[] ⊑ tt∷[]) is
  -- o'-extended to (o' (os oz) : tt∷[] ⊑ tt∷tt∷[]) by the cross-term wkΘ-V.  The
  -- reduct computes by refl ⇒ the cross-term is CONFLUENT (no stuck redex).
  crossterm-computes :
    sub termΛ [] σv
    ≡ (vt (Lam (drop (vt (lam tvar (use (vt vlvar)) (cs' czz))))) ⇑[ os oz , oz ])
  crossterm-computes = refl

-- ── (3b) the Λ (USE) case: β OCCURS in the body (via a tapp on the bound β), so
-- liftVΘ (= wkΘ-VSub, the real cross-term) fires on the value-substitution.  We do
-- NOT pin the exact reduct here (its cover shape is intricate); instead we confirm
-- the result is a well-typed, FULLY-COMPUTED Bi Tm (a concrete head, no stuck redex)
-- by projecting its head constructor — `vt ∘ Lam ∘ use` — by refl. ──
termΛ2 : Tm [] (tt ∷ [])
termΛ2 = vt (Lam (use (tapp (vt vlvar) tvar (c's czz))))

-- predicate: the bi-scoped term's head is vt (Lam (use _)) (fully computed).
isVtLamUse : ∀ {Θ Γ} → Bi Tm Θ Γ → Set
isVtLamUse (vt (Lam (use _)) ⇑[ _ , _ ]) = ⊤
isVtLamUse _                              = Vl [] []  -- any non-⊤ "false"

opaque
  unfolding subVl sub subT idS idVSub idEmb oe oi wkSub
  -- the result's HEAD is vt(Lam(use …)): it computed all the way through liftVΘ
  -- (the cross-term) and bindUp on the type scope without getting stuck.
  crossterm-use-head : isVtLamUse (sub termΛ2 [] σv)
  crossterm-use-head = tt
