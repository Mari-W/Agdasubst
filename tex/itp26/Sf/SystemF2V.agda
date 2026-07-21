{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.SystemF2V — the co-de-Bruijn VECTOR-SUBSTITUTION engine for System F,
-- mirroring Autosubst 2's construction (Kaiser/Schäfer/Stark, LFMTP'17, F_CBV).
--
-- THREE sorts:  ty (single-scope), vl (values), tm (terms).  vl/tm are mutually
-- recursive and BI-SCOPED over a TYPE scope Θ and a VALUE scope Γ.
--
-- A vector substitution `Sub⃗ Θ Γ Θ' Γ' = (στ , σ)`:
--   στ : Sub Θ Θ'            a TYPE-substitution (reuses Sf.SystemF2VTy's σ-engine)
--   σ  : VSub Θ Γ Γ'         a VALUE-substitution: each value-var of Γ' ↦ Vl↑↑ Θ Γ
--
-- Up-matrix (Fig 1), in co-de-Bruijn:
--   ⇑ty (under Λ):  type comp standard-lifted; value comp = σ ◦ (↑,idvl) — THE
--     cross-term: o'-extend EACH target's TYPE-thinning.  Pure thinning algebra.
--   ⇑vl (under λ):  type comp UNCHANGED; value comp standard-lifted in Γ only.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.SystemF2V where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Agda.Builtin.Equality.Rewrite

-- the TYPE σ-engine (re-exports Sf.Scaffold ⊤, Sf.Sub, Ty, subT, _⟪_⟫T, _⨟_ …)
open import Sf.SystemF2VTy public

-- ════════════════════════════════════════════════════════════════════════════
-- VALUES and TERMS — mutually recursive, BI-SCOPED over (Θ ; Γ).
-- ════════════════════════════════════════════════════════════════════════════
data Vl : Scope → Scope → Set
data Tm : Scope → Scope → Set

data Vl where
  -- the value variable: NO type-support ([]), singleton value-support.
  vlvar : Vl [] (tt ∷ [])
  -- λ(x:A). body.  A : Ty over the type scope; body binds a VALUE var (Γ-binder).
  lam  : ∀ {Θₐ Θᵦ Θ Γ}
       → Ty Θₐ → Bind tt (Tm Θᵦ) Γ → Cover Θₐ Θᵦ Θ → Vl Θ Γ
  -- Λ. body.  body binds a TYPE var (Θ-binder); the value scope Γ is unchanged.
  Lam  : ∀ {Θ Γ}
       → Bind tt (λ Θ′ → Tm Θ′ Γ) Θ → Vl Θ Γ

data Tm where
  -- s t : application, merge BOTH scopes with INDEPENDENT covers.
  app  : ∀ {Θₗ Θᵣ Θ Γₗ Γᵣ Γ}
       → Tm Θₗ Γₗ → Tm Θᵣ Γᵣ → Cover Θₗ Θᵣ Θ → Cover Γₗ Γᵣ Γ → Tm Θ Γ
  -- s A : type application.  Type arg A : Ty merges into the TYPE scope; Γ shared.
  tapp : ∀ {Θₑ Θₐ Θ Γ}
       → Tm Θₑ Γ → Ty Θₐ → Cover Θₑ Θₐ Θ → Tm Θ Γ
  -- vt v : a value used as a term.
  vt   : ∀ {Θ Γ} → Vl Θ Γ → Tm Θ Γ

-- ── BI-SCOPED thing-with-thinning for values / terms: TWO thinnings. ──
record Bi (F : Scope → Scope → Set)(Θ Γ : Scope) : Set where
  constructor _⇑[_,_]
  field {spΘ spΓ} : Scope
        ent  : F spΘ spΓ
        thΘ  : spΘ ⊑ Θ
        thΓ  : spΓ ⊑ Γ
open Bi public

-- rename a bi-scoped thing along TWO thinnings (carry-the-thinning, no traversal)
_⟨_,_⟩b : ∀ {F Θ Γ Θ′ Γ′} → Bi F Θ Γ → Θ ⊑ Θ′ → Γ ⊑ Γ′ → Bi F Θ′ Γ′
(e ⇑[ θ , φ ]) ⟨ ψΘ , ψΓ ⟩b = e ⇑[ θ ⨾ ψΘ , φ ⨾ ψΓ ]
infixl 8 _⟨_,_⟩b

-- ════════════════════════════════════════════════════════════════════════════
-- BI-SCOPED SMART CONSTRUCTORS.  Each merges the per-scope supports INDEPENDENTLY
-- (type scope via `cop` on the type thinnings, value scope via `cop` on the value
-- thinnings) — the two scopes never interact.
-- ════════════════════════════════════════════════════════════════════════════

-- s t : merge BOTH scopes.
appᵇ : ∀ {Θ Γ} → Bi Tm Θ Γ → Bi Tm Θ Γ → Bi Tm Θ Γ
appᵇ (l ⇑[ θₗ , φₗ ]) (r ⇑[ θᵣ , φᵣ ]) =
  app l r (cov (cop θₗ θᵣ)) (cov (cop φₗ φᵣ)) ⇑[ out (cop θₗ θᵣ) , out (cop φₗ φᵣ) ]

-- s A : merge the TYPE scope (with the type-arg's support); value scope shared.
tappᵇ : ∀ {Θ Γ} → Bi Tm Θ Γ → Ty ↑ Θ → Bi Tm Θ Γ
tappᵇ (e ⇑[ θₑ , φ ]) (a ⇑ θₐ) =
  tapp e a (cov (cop θₑ θₐ)) ⇑[ out (cop θₑ θₐ) , φ ]

-- vt v : value-as-term (no merge).
vtᵇ : ∀ {Θ Γ} → Bi Vl Θ Γ → Bi Tm Θ Γ
vtᵇ (v ⇑[ θ , φ ]) = vt v ⇑[ θ , φ ]

-- λ(x:A). body :  merge A's type-support with the body's; read the body's VALUE
-- binder (use/drop on the value scope).
lamᵇ : ∀ {Θ Γ} → Ty ↑ Θ → Bi Tm Θ (tt ∷ Γ) → Bi Vl Θ Γ
lamᵇ (a ⇑ θₐ) (t ⇑[ θᵦ , os φ ]) = lam a (use t)  (cov (cop θₐ θᵦ)) ⇑[ out (cop θₐ θᵦ) , φ ]
lamᵇ (a ⇑ θₐ) (t ⇑[ θᵦ , o' φ ]) = lam a (drop t) (cov (cop θₐ θᵦ)) ⇑[ out (cop θₐ θᵦ) , φ ]

-- Λ. body :  read the body's TYPE binder (use/drop on the type scope).
Lamᵇ : ∀ {Θ Γ} → Bi Tm (tt ∷ Θ) Γ → Bi Vl Θ Γ
Lamᵇ (t ⇑[ os θ , φ ]) = Lam (use t)  ⇑[ θ , φ ]
Lamᵇ (t ⇑[ o' θ , φ ]) = Lam (drop t) ⇑[ θ , φ ]

-- ════════════════════════════════════════════════════════════════════════════
-- THE VALUE-SUBSTITUTION CONTAINER  `VSub Θ Γ Γ′` — for each value-var of Γ′, a
-- bi-scoped value `Bi Vl Θ Γ`.  (Same spine shape as Sf.Sub, but BI-SCOPED entries.)
-- ════════════════════════════════════════════════════════════════════════════
data VSub (Θ Γ : Scope) : Scope → Set where
  []   : VSub Θ Γ []
  _,-_ : ∀ {Γ′} → VSub Θ Γ Γ′ → Bi Vl Θ Γ → VSub Θ Γ (tt ∷ Γ′)
infixl 5 _,-_

-- split the value-env along a VALUE cover (structural).
selLV : ∀ {Θ Γ Γₗ Γᵣ Γ′} → Cover Γₗ Γᵣ Γ′ → VSub Θ Γ Γ′ → VSub Θ Γ Γₗ
selLV czz     []       = []
selLV (css c) (σ ,- u) = selLV c σ ,- u
selLV (cs' c) (σ ,- u) = selLV c σ ,- u
selLV (c's c) (σ ,- u) = selLV c σ
selRV : ∀ {Θ Γ Γₗ Γᵣ Γ′} → Cover Γₗ Γᵣ Γ′ → VSub Θ Γ Γ′ → VSub Θ Γ Γᵣ
selRV czz     []       = []
selRV (css c) (σ ,- u) = selRV c σ ,- u
selRV (cs' c) (σ ,- u) = selRV c σ
selRV (c's c) (σ ,- u) = selRV c σ ,- u

-- restrict the value-env along a VALUE thinning (the VSub analog of `_↾_`).
_↾V_ : ∀ {Θ Γ sup Γ′} → VSub Θ Γ Γ′ → sup ⊑ Γ′ → VSub Θ Γ sup
[]       ↾V oz   = []
(σ ,- u) ↾V os θ = (σ ↾V θ) ,- u
(σ ,- u) ↾V o' θ = σ ↾V θ
infixl 8 _↾V_

-- ── THE TWO RENAMINGS OF TARGETS (pure thinning algebra) ──
-- value-weaken every target by one VALUE var (= σ ◦ (idty,↑), the value-lift tail).
wkΓ-V : ∀ {Θ Γ} → Bi Vl Θ Γ → Bi Vl Θ (tt ∷ Γ)
wkΓ-V (v ⇑[ θ , φ ]) = v ⇑[ θ , o' φ ]
wkΓ-VSub : ∀ {Θ Γ Γ′} → VSub Θ Γ Γ′ → VSub Θ (tt ∷ Γ) Γ′
wkΓ-VSub []       = []
wkΓ-VSub (σ ,- u) = wkΓ-VSub σ ,- wkΓ-V u

-- type-weaken every target by one TYPE var (= σ ◦ (↑,idvl), THE CROSS-TERM).
-- This is the decisive co-de-Bruijn realisation: a pure o'-extend of the TYPE
-- thinning of each target value, discharged by the thinning algebra alone.
wkΘ-V : ∀ {Θ Γ} → Bi Vl Θ Γ → Bi Vl (tt ∷ Θ) Γ
wkΘ-V (v ⇑[ θ , φ ]) = v ⇑[ o' θ , φ ]
wkΘ-VSub : ∀ {Θ Γ Γ′} → VSub Θ Γ Γ′ → VSub (tt ∷ Θ) Γ Γ′
wkΘ-VSub []       = []
wkΘ-VSub (σ ,- u) = wkΘ-VSub σ ,- wkΘ-V u

-- the fresh bound value var as a bi-scoped entry (0vl).
vlvar₀ : ∀ {Θ Γ} → Bi Vl Θ (tt ∷ Γ)
vlvar₀ = vlvar ⇑[ oe , os oe ]

-- bi-scoped TERM weakenings (o' on the relevant thinning), for the drop bodies.
wkΓ-T : ∀ {Θ Γ} → Bi Tm Θ Γ → Bi Tm Θ (tt ∷ Γ)
wkΓ-T (t ⇑[ θ , φ ]) = t ⇑[ θ , o' φ ]
wkΘ-T : ∀ {Θ Γ} → Bi Tm Θ Γ → Bi Tm (tt ∷ Θ) Γ
wkΘ-T (t ⇑[ θ , φ ]) = t ⇑[ o' θ , φ ]

-- ── THE TWO LIFTS (Fig 1).  A vector is passed as the two components (στ , σ). ──
-- ⇑vl (under a VALUE binder λ): type comp UNCHANGED; value comp standard-lifted.
liftVΓ : ∀ {Θ Γ Γ′} → VSub Θ Γ Γ′ → VSub Θ (tt ∷ Γ) (tt ∷ Γ′)
liftVΓ σ = wkΓ-VSub σ ,- vlvar₀

-- ⇑ty (under a TYPE binder Λ): value comp = THE CROSS-TERM (type-weaken targets);
-- the type comp is standard-lifted by the caller via `lift` of the σ-engine.
liftVΘ : ∀ {Θ Γ Γ′} → VSub Θ Γ Γ′ → VSub (tt ∷ Θ) Γ Γ′
liftVΘ σ = wkΘ-VSub σ

-- ════════════════════════════════════════════════════════════════════════════
-- THE VECTOR INSTANTIATION  (Fig 1).  Mutually recursive sub / subVl, taking the
-- vector as its two components στ (TYPE sub) and σ (VALUE sub).  OPAQUE so the
-- σ-laws can register.
-- ════════════════════════════════════════════════════════════════════════════
opaque
  sub   : ∀ {Θ′ Γ′ Θ Γ} → Tm Θ′ Γ′ → Sub Θ Θ′ → VSub Θ Γ Γ′ → Bi Tm Θ Γ
  subVl : ∀ {Θ′ Γ′ Θ Γ} → Vl Θ′ Γ′ → Sub Θ Θ′ → VSub Θ Γ Γ′ → Bi Vl Θ Γ

  -- TERMS
  sub (app l r cθ cγ) στ σ =
    appᵇ (sub l (selL cθ στ) (selLV cγ σ)) (sub r (selR cθ στ) (selRV cγ σ))
  -- (s A)[στ,σ] = s[στ,σ]  A[στ]  — the type subterm gets the SUB-vector [στ].
  sub (tapp e a cθ) στ σ =
    tappᵇ (sub e (selL cθ στ) σ) (subT a (selR cθ στ))
  sub (vt v) στ σ = vtᵇ (subVl v στ σ)

  -- VALUES
  -- x[στ,σ] = σ x  — project the VALUE component (type sub on [] is irrelevant).
  subVl vlvar στ ([] ,- u) = u
  -- (λA.s)[στ,σ] = λ A[στ]. s[⇑vl (στ,σ)]  — type comp UNCHANGED under λ.
  subVl (lam a (use t) cθ) στ σ =
    lamᵇ (subT a (selL cθ στ)) (sub t (selR cθ στ) (liftVΓ σ))
  subVl (lam a (drop t) cθ) στ σ =
    lamᵇ (subT a (selL cθ στ)) (wkΓ-T (sub t (selR cθ στ) σ))
  -- (Λ.s)[στ,σ] = Λ. s[⇑ty (στ,σ)]  — type comp lifted, value comp = cross-term.
  subVl (Lam (use t)) στ σ =
    Lamᵇ (sub t (wkSub στ ,- var₀) (liftVΘ σ))
  subVl (Lam (drop t)) στ σ =
    Lamᵇ (wkΘ-T (sub t στ σ))

-- ════════════════════════════════════════════════════════════════════════════
-- The IDENTITY value-substitution and the bi-scoped instantiation wrapper.
-- ════════════════════════════════════════════════════════════════════════════
opaque
  idVSub : ∀ {Θ Γ} → VSub Θ Γ Γ
  idVSub {Γ = []}    = []
  idVSub {Γ = _ ∷ Γ} = wkΓ-VSub idVSub ,- vlvar₀

-- apply a vector (στ , σ) to a bi-scoped TERM thing: restrict each component to
-- the thing's own supports, then instantiate.
opaque
  unfolding sub
  _⟪_,_⟫ : ∀ {Θ′ Γ′ Θ Γ} → Bi Tm Θ′ Γ′ → Sub Θ Θ′ → VSub Θ Γ Γ′ → Bi Tm Θ Γ
  (t ⇑[ θ , φ ]) ⟪ στ , σ ⟫ = sub t (στ ↾ θ) (σ ↾V φ)
infixl 8 _⟪_,_⟫

-- apply a vector to a bi-scoped VALUE thing.
opaque
  unfolding subVl
  _⟪_,_⟫v : ∀ {Θ′ Γ′ Θ Γ} → Bi Vl Θ′ Γ′ → Sub Θ Θ′ → VSub Θ Γ Γ′ → Bi Vl Θ Γ
  (v ⇑[ θ , φ ]) ⟪ στ , σ ⟫v = subVl v (στ ↾ θ) (σ ↾V φ)
infixl 8 _⟪_,_⟫v
