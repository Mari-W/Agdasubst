{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.SystemF2Typing — extrinsic typing for the TWO-SCOPE (bi-scoped) co-de-Bruijn
-- System F of Sf.SystemF2.  This file is the VALIDATION GATE for the hypothesis
-- that separating the single interleaved scope into a TYPE scope Θ and a TERM
-- scope Γ dissolves the tight-context wall.
--
--   • TERM context `Φ : TmCx Θ Γ` is TIGHT — restricted to the term-support Γ.
--     Each stored entry is a `Ty ↑ Θ` over the FULL type scope Θ, NOT over Γ.  So
--     restricting Φ on the term scope NEVER touches the stored types ⇒ no type
--     restriction, no `factor (os φ)(o' θ)`, term-variable typing is FREE.
--   • TYPE scope Θ is FULL — types only ever WEAKEN (re-embedded along the
--     independent TYPE-cover-thinnings), never the partial restriction.
--
-- GATE SCOPE: `⊢var`, `⊢app` (the cohL/cohR term-context split), `⊢App`.  We
-- confirm the uninhabited `factor (os φ)(o' θ)` case never arises.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.SystemF2Typing where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
open import Sf.SystemF2
-- Fac-L/Fac-R as rewrites on the OPAQUE thinL/thinR (used for the TYPE thinnings):
-- `thinL (cov (cop θ φ)) ⨾ out (cop θ φ) ≡ θ`, so the smart-app's type thinnings
-- collapse definitionally.  (Same algebra serves the type scope; ⊤-instanced.)
open import Sf.Fac ⊤ public

-- ════════════════════════════════════════════════════════════════════════════
-- TERM CONTEXT  `TmCx Θ Γ` — one stored type `Ty ↑ Θ` per term-var of Γ.  The
-- type scope Θ is a uniform index over the whole context (it is FULL: every entry
-- is over the same Θ).  The term scope Γ is what gets RESTRICTED.
-- ════════════════════════════════════════════════════════════════════════════
data TmCx (Θ : Scope) : Scope → Set where
  ε    : TmCx Θ []
  _,-_ : ∀ {Γ} → TmCx Θ Γ → Ty ↑ Θ → TmCx Θ (tt ∷ Γ)
infixl 5 _,-_

-- ── RESTRICT the term context to the term-support picked out by a Γ-thinning.
-- Purely on the TERM scope; the stored types (over Θ) are carried along UNTOUCHED.
-- This is the verbatim STLC/Context `rest`, only the classifier is now `Ty ↑ Θ`. ──
restᵗ : ∀ {Θ Δ Γ} → Δ ⊑ Γ → TmCx Θ Γ → TmCx Θ Δ
restᵗ oz     ε        = ε
restᵗ (os θ) (Φ ,- A) = restᵗ θ Φ ,- A
restᵗ (o' θ) (Φ ,- A) = restᵗ θ Φ

-- transparent cover-thinnings on the TERM scope (Context's thL/thR pattern).
thLᵗ : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Γₗ ⊑ Γ
thLᵗ czz = oz ; thLᵗ (css c) = os (thLᵗ c) ; thLᵗ (cs' c) = os (thLᵗ c) ; thLᵗ (c's c) = o' (thLᵗ c)
thRᵗ : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Γᵣ ⊑ Γ
thRᵗ czz = oz ; thRᵗ (css c) = os (thRᵗ c) ; thRᵗ (cs' c) = o' (thRᵗ c) ; thRᵗ (c's c) = os (thRᵗ c)

-- context split = restriction along the term-cover-thinning (so "split = restrict"
-- is refl, and split COMPUTES).
splitLᵗ : ∀ {Θ Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → TmCx Θ Γ → TmCx Θ Γₗ
splitLᵗ cv Φ = restᵗ (thLᵗ cv) Φ
splitRᵗ : ∀ {Θ Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → TmCx Θ Γ → TmCx Θ Γᵣ
splitRᵗ cv Φ = restᵗ (thRᵗ cv) Φ

-- ── TERM-SCOPE CONTEXT COHERENCES (verbatim Sf.Context, classifier = Ty ↑ Θ).
-- These confirm the decisive point: cohL/cohR/rest-oe operate PURELY on the term
-- scope; the stored types `A : Ty ↑ Θ` are carried UNCHANGED by the `,- A` clause.
-- There is NO operation here that restricts the type scope.  Registering them as
-- rewrites makes the smart constructors below definitional. ──
open import Relation.Binary.PropositionalEquality using (cong)
opaque
  unfolding oi
  restᵗ-oi : ∀ {Θ Δ}(Φ : TmCx Θ Δ) → restᵗ oi Φ ≡ Φ
  restᵗ-oi ε        = refl
  restᵗ-oi (Φ ,- A) = cong (_,- A) (restᵗ-oi Φ)
{-# REWRITE restᵗ-oi #-}
opaque
  unfolding oi covL covR full
  thLᵗ-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ) → thLᵗ (covL φ) ≡ oi
  thLᵗ-covL oz = refl ; thLᵗ-covL (os φ) = cong os (thLᵗ-covL φ) ; thLᵗ-covL (o' φ) = cong os (thLᵗ-covL φ)
  thRᵗ-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ) → thRᵗ (covL φ) ≡ φ
  thRᵗ-covL oz = refl ; thRᵗ-covL (os φ) = cong os (thRᵗ-covL φ) ; thRᵗ-covL (o' φ) = cong o' (thRᵗ-covL φ)
  thLᵗ-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ) → thLᵗ (covR θ) ≡ θ
  thLᵗ-covR oz = refl ; thLᵗ-covR (os θ) = cong os (thLᵗ-covR θ) ; thLᵗ-covR (o' θ) = cong o' (thLᵗ-covR θ)
  thRᵗ-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ) → thRᵗ (covR θ) ≡ oi
  thRᵗ-covR oz = refl ; thRᵗ-covR (os θ) = cong os (thRᵗ-covR θ) ; thRᵗ-covR (o' θ) = cong os (thRᵗ-covR θ)
  thLᵗ-full : ∀ {Γ} → thLᵗ (full {Γ}) ≡ oi
  thLᵗ-full {[]} = refl ; thLᵗ-full {_ ∷ Γ} = cong os thLᵗ-full
  thRᵗ-full : ∀ {Γ} → thRᵗ (full {Γ}) ≡ oi
  thRᵗ-full {[]} = refl ; thRᵗ-full {_ ∷ Γ} = cong os thRᵗ-full
{-# REWRITE thLᵗ-covL thRᵗ-covL thLᵗ-covR thRᵗ-covR thLᵗ-full thRᵗ-full #-}
opaque
  unfolding cop
  cohLᵗ : ∀ {Θ Γₗ Γᵣ Δ}(θ : Γₗ ⊑ Δ)(φ : Γᵣ ⊑ Δ)(Φ : TmCx Θ Δ)
        → restᵗ (thLᵗ (cov (cop θ φ))) (restᵗ (out (cop θ φ)) Φ) ≡ restᵗ θ Φ
  cohLᵗ oz     oz     ε        = refl
  cohLᵗ (os θ) (os φ) (Φ ,- A) = cong (_,- A) (cohLᵗ θ φ Φ)
  cohLᵗ (os θ) (o' φ) (Φ ,- A) = cong (_,- A) (cohLᵗ θ φ Φ)
  cohLᵗ (o' θ) (os φ) (Φ ,- A) = cohLᵗ θ φ Φ
  cohLᵗ (o' θ) (o' φ) (Φ ,- A) = cohLᵗ θ φ Φ
  cohRᵗ : ∀ {Θ Γₗ Γᵣ Δ}(θ : Γₗ ⊑ Δ)(φ : Γᵣ ⊑ Δ)(Φ : TmCx Θ Δ)
        → restᵗ (thRᵗ (cov (cop θ φ))) (restᵗ (out (cop θ φ)) Φ) ≡ restᵗ φ Φ
  cohRᵗ oz     oz     ε        = refl
  cohRᵗ (os θ) (os φ) (Φ ,- A) = cong (_,- A) (cohRᵗ θ φ Φ)
  cohRᵗ (os θ) (o' φ) (Φ ,- A) = cohRᵗ θ φ Φ
  cohRᵗ (o' θ) (os φ) (Φ ,- A) = cong (_,- A) (cohRᵗ θ φ Φ)
  cohRᵗ (o' θ) (o' φ) (Φ ,- A) = cohRᵗ θ φ Φ
{-# REWRITE cohLᵗ cohRᵗ #-}
opaque
  unfolding oe
  restᵗ-oe : ∀ {Θ Δ}(Φ : TmCx Θ Δ) → restᵗ oe Φ ≡ ε
  restᵗ-oe ε        = refl
  restᵗ-oe (Φ ,- A) = restᵗ-oe Φ
{-# REWRITE restᵗ-oe #-}

-- ── TYPE-WEAKENING of the WHOLE term context (the clean total weakening the
-- two-scope scheme promises).  Under `Λα` the type scope grows by one ty-var, so
-- every stored type weakens by `wk↑ ty`.  TOTAL, distributive, structural,
-- subst-free — NEVER the partial restriction.  This is the only residual
-- type-side lemma the binder needs, and it is the CLEAN kind. ──
wkCx : ∀ {Θ Γ} → TmCx Θ Γ → TmCx (tt ∷ Θ) Γ
wkCx ε        = ε
wkCx (Φ ,- A) = wkCx Φ ,- wk↑ tt A

-- ════════════════════════════════════════════════════════════════════════════
-- TYPE re-embedding.  A subterm's type-support is SMALLER than the full type
-- scope Θ; the judgement carries a TYPE thinning `θ : Θₜ ⊑ Θ` (the term's own
-- type-support into the full Θ).  This is the Option-A scheme but RESTRICTED TO
-- THE TYPE SCOPE: the TERM scope stays TIGHT (like STLC), only the TYPE thinning
-- weakens — total, distributive, never the partial restriction.
-- ════════════════════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════════════════════
-- THE TYPING JUDGEMENT  `Φ ⊢[ θ ] t ∶ A`.
--   Φ : TmCx Θ Γ   (term context TIGHT over Γ, types over the FULL Θ),
--   t : Tm Θₜ Γ    (term over its OWN type-support Θₜ, term-support Γ = tight),
--   θ : Θₜ ⊑ Θ     (the TYPE thinning; the TERM scope carries NO thinning),
--   A : Ty ↑ Θ     (type over the full Θ).
-- ════════════════════════════════════════════════════════════════════════════
data _⊢[_]_∶_ : ∀ {Θₜ Θ Γ} → TmCx Θ Γ → Θₜ ⊑ Θ → Tm Θₜ Γ → Ty ↑ Θ → Set where
  -- THE GATE'S CORE.  The sole term variable.  Its TYPE-support is `[]` (so θ is
  -- the empty type thinning `oe`) and its TERM-support is the singleton; the tight
  -- term context restricted to that support is `ε ,- A`.  A : Ty ↑ Θ is FREE.  No
  -- lookup, no factor.  This is STLC's ⊢var verbatim on the TERM side — the wall is
  -- GONE because the type rides on the (full, independent) Θ, not on Γ.
  ⊢var : ∀ {Θ}{A : Ty ↑ Θ} → (ε ,- A) ⊢[ oe ] tmvar ∶ A
  -- application.  cγ splits the TERM context (cohL/cohR, term scope only); cθ
  -- merges the TYPE supports.  The subterm TYPE thinnings compose through the TYPE
  -- cover `thinL cθ ⨾ θ` / `thinR cθ ⨾ θ` — TOTAL composition, never a factor.
  ⊢app : ∀ {Θₗ Θᵣ Θₜ Θ Γₗ Γᵣ Γ}{Φ : TmCx Θ Γ}
           {l : Tm Θₗ Γₗ}{r : Tm Θᵣ Γᵣ}{cθ : Cover Θₗ Θᵣ Θₜ}{θ : Θₜ ⊑ Θ}
           {cγ : Cover Γₗ Γᵣ Γ}{A B : Ty ↑ Θ}
       → splitLᵗ cγ Φ ⊢[ thinL cθ ⨾ θ ] l ∶ (A ⇒↑ B)
       → splitRᵗ cγ Φ ⊢[ thinR cθ ⨾ θ ] r ∶ A
       → Φ ⊢[ θ ] app l r cθ cγ ∶ B
  -- type application  e [a].  e : ∀↑ B over the full Θ (via the type thinning
  -- thinL cθ ⨾ θ); arg a embedded along thinR cθ ⨾ θ.  Result B[a] via the TYPE
  -- substitution `_⟪_⟫T`.  The type scope is FULL throughout — no factor.
  ⊢App : ∀ {Θₑ Θₐ Θₜ Θ Γ}{Φ : TmCx Θ Γ}
           {e : Tm Θₑ Γ}{a : Ty Θₐ}{cθ : Cover Θₑ Θₐ Θₜ}{θ : Θₜ ⊑ Θ}
           {B : Ty ↑ (tt ∷ Θ)}
       → Φ ⊢[ thinL cθ ⨾ θ ] e ∶ ∀↑ B
       → Φ ⊢[ θ ] `App e a cθ ∶ (B ⟪ idS ,- (a ⇑ (thinR cθ ⨾ θ)) ⟫T)
  -- λ(x:a). body.  The body binds a TERM variable (a Γ-extension — TIGHT, exactly
  -- like STLC's ⊢lamᵘ).  The domain type `a` is re-embedded into Θ via its TYPE
  -- thinning `thinL cθ ⨾ θ`; the body's TYPE thinning is `thinR cθ ⨾ θ`.  No type
  -- restriction — the term context simply GROWS by one tight entry.  No factor.
  ⊢lamᵘ : ∀ {Θₐ Θᵦ Θₜ Θ Γ}{Φ : TmCx Θ Γ}{a : Ty Θₐ}{body : Tm Θᵦ (tt ∷ Γ)}
            {cθ : Cover Θₐ Θᵦ Θₜ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ Θ}
        → (Φ ,- (a ⇑ (thinL cθ ⨾ θ))) ⊢[ thinR cθ ⨾ θ ] body ∶ B
        → Φ ⊢[ θ ] lam a (use body) cθ ∶ ((a ⇑ (thinL cθ ⨾ θ)) ⇒↑ B)
  -- the drop body: the bound term var is ABSENT, so the body is typed in the
  -- UN-extended context Φ (term scope Γ) — exactly STLC's ⊢lamᵈ.  The TERM scope
  -- stays tight; only the domain type rides on Θ.  No factor.
  ⊢lamᵈ : ∀ {Θₐ Θᵦ Θₜ Θ Γ}{Φ : TmCx Θ Γ}{a : Ty Θₐ}{body : Tm Θᵦ Γ}
            {cθ : Cover Θₐ Θᵦ Θₜ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ Θ}
        → Φ ⊢[ thinR cθ ⨾ θ ] body ∶ B
        → Φ ⊢[ θ ] lam a (drop body) cθ ∶ ((a ⇑ (thinL cθ ⨾ θ)) ⇒↑ B)
  -- Λα. body.  The body binds a TYPE variable — the TYPE scope GROWS.  The whole
  -- term context is WEAKENED by one ty-var via `wkCx` (wk↑ ty on each stored type)
  -- — a TOTAL, distributive type-weakening, NEVER a restriction.  No factor.
  ⊢Lamᵘ : ∀ {Θₜ Θ Γ}{Φ : TmCx Θ Γ}{body : Tm (tt ∷ Θₜ) Γ}{θ : Θₜ ⊑ Θ}
            {B : Ty ↑ (tt ∷ Θ)}
        → wkCx Φ ⊢[ os θ ] body ∶ B
        → Φ ⊢[ θ ] `Lam (use body) ∶ ∀↑ B
  ⊢Lamᵈ : ∀ {Θₜ Θ Γ}{Φ : TmCx Θ Γ}{body : Tm Θₜ Γ}{θ : Θₜ ⊑ Θ}
            {B : Ty ↑ (tt ∷ Θ)}
        → wkCx Φ ⊢[ o' θ ] body ∶ B
        → Φ ⊢[ θ ] `Lam (drop body) ∶ ∀↑ B
infix 4 _⊢[_]_∶_

-- ════════════════════════════════════════════════════════════════════════════
-- A BI-SCOPED thing-with-thinning for terms carries TWO thinnings: a TYPE thinning
-- (its type-support into Θ) and a TERM thinning (its term-support into Γ).  Typing
-- of such a thing restricts the term context to the term-support (TIGHT) and keeps
-- the type over the full Θ via the type thinning.
-- ════════════════════════════════════════════════════════════════════════════
record Tm↑↑ (Θ Γ : Scope) : Set where
  constructor _⇑[_,_]
  field {supΘ supΓ} : Scope
        tm     : Tm supΘ supΓ
        thnΘ   : supΘ ⊑ Θ        -- TYPE thinning  (full type scope)
        thnΓ   : supΓ ⊑ Γ        -- TERM thinning  (tight term scope)
open Tm↑↑ public

-- typing of a bi-scoped thing-with-thinning: TIGHT-restrict the term context to the
-- term-support, keep the type over the full Θ via the type thinning.  This is the
-- two-scope analog of STLC's `_⊢↑_∶_` — and CRUCIALLY the restriction `restᵗ` is
-- on the TERM scope ONLY; the type thinning is total composition, never a factor.
_⊢↑_∶_ : ∀ {Θ Γ} → TmCx Θ Γ → Tm↑↑ Θ Γ → Ty ↑ Θ → Set
Φ ⊢↑ (t ⇑[ θ , φ ]) ∶ A = restᵗ φ Φ ⊢[ θ ] t ∶ A
infix 4 _⊢↑_∶_

-- ════════════════════════════════════════════════════════════════════════════
-- THE DECISIVE GATE CONSTRUCTOR: the smart `⊢app↑`.  It merges two typed
-- bi-scoped things-with-thinnings, doing a `cop` on the TERM scope (cover cγ) AND
-- a `cop` on the TYPE scope (cover cθ) — INDEPENDENTLY.  This is exactly the place
-- where the SINGLE-SORTED System F was forced into the type-uninhabited
-- `factor (os φ)(o' θ)` (a type keeping a ty-var the term-restriction drops).
--
-- HERE that case CANNOT arise:
--   • the TERM cover-merge `cov (cop φ_l φ_r)` restricts the term context via the
--     cohL/cohR rewrites (term scope only) — definitional, no factor;
--   • the TYPE cover-merge `cov (cop θ_l θ_r)` only THINS the types (total `_⨾_`
--     through the type cover) — never restricts.
-- The two scopes never interact, so no "type keeps a dropped variable" obligation.
-- It typechecks ⇒ the gate PASSES. ──
⊢app↑ : ∀ {Θ Γ}{Φ : TmCx Θ Γ}{A B : Ty ↑ Θ}
        (l′ r′ : Tm↑↑ Θ Γ)
      → Φ ⊢↑ l′ ∶ (A ⇒↑ B) → Φ ⊢↑ r′ ∶ A
      → Φ ⊢↑ record { tm   = app (tm l′) (tm r′) (cov (cop (thnΘ l′) (thnΘ r′)))
                                                 (cov (cop (thnΓ l′) (thnΓ r′)))
                    ; thnΘ = out (cop (thnΘ l′) (thnΘ r′))
                    ; thnΓ = out (cop (thnΓ l′) (thnΓ r′)) } ∶ B
⊢app↑ {Φ = Φ} (l ⇑[ θₗ , φₗ ]) (r ⇑[ θᵣ , φᵣ ]) ⊢l ⊢r =
  ⊢app {Φ = restᵗ (out (cop φₗ φᵣ)) Φ}
       {cθ = cov (cop θₗ θᵣ)} {θ = out (cop θₗ θᵣ)}
       {cγ = cov (cop φₗ φᵣ)} ⊢l ⊢r

-- the FRESH term variable, typed.  The tight term context restricted to the var's
-- singleton support is `ε ,- A` (restᵗ-oe fires).  DEFINITIONAL: it IS ⊢var.
-- θ = oe : [] ⊑ Θ is the var's empty TYPE thinning.  No factor.
⊢fresh : ∀ {Θ Γ}{Ψ : TmCx Θ Γ}{A : Ty ↑ Θ}
       → (Ψ ,- A) ⊢↑ (tmvar ⇑[ oe , os oe ]) ∶ A
⊢fresh = ⊢var

-- the smart `⊢App↑`: type-application, merging the TYPE supports (cop on Θ), term
-- scope shared.  Result type B[a] via the TYPE substitution.  DEFINITIONAL via Fac.
⊢App↑ : ∀ {Θ Γ}{Φ : TmCx Θ Γ}{supΘₑ supΓ : Scope}
          (B : Ty ↑ (tt ∷ Θ))(e : Tm supΘₑ supΓ)(θₑ : supΘₑ ⊑ Θ)(φ : supΓ ⊑ Γ)
          {supΘₐ}(a : Ty supΘₐ)(θₐ : supΘₐ ⊑ Θ)
      → restᵗ φ Φ ⊢[ θₑ ] e ∶ ∀↑ B
      → Φ ⊢↑ (`App e a (cov (cop θₑ θₐ)) ⇑[ out (cop θₑ θₐ) , φ ]) ∶ (B ⟪ idS ,- (a ⇑ θₐ) ⟫T)
⊢App↑ B e θₑ φ a θₐ ⊢e = ⊢App {cθ = cov (cop θₑ θₐ)} {θ = out (cop θₑ θₐ)} {B = B} ⊢e

-- the smart `⊢Lam↑`: type-binder Λ.  Reads the body's TYPE-binder (use/drop).  The
-- TYPE scope grows; the whole term context weakens via `wkCx` (total).  No factor.
-- The premise SHAPE per binder: a use-binder types the body in `wkCx Φ` at `os θ`
-- (the bound ty-var present); a drop-binder at `o' θ` (absent).
BindTyP : ∀ {Θₜ Θ Γ} → TmCx Θ Γ → Ty ↑ (tt ∷ Θ) → Θₜ ⊑ Θ
        → Bind tt (λ Θ′ → Tm Θ′ Γ) Θₜ → Set
BindTyP Φ B θ (use body)  = wkCx Φ ⊢[ os θ ] body ∶ B
BindTyP Φ B θ (drop body) = wkCx Φ ⊢[ o' θ ] body ∶ B
⊢Lam↑ : ∀ {Θₜ Θ Γ}{Φ : TmCx Θ Γ}{B : Ty ↑ (tt ∷ Θ)}{θ : Θₜ ⊑ Θ}
        (bnd : Bind tt (λ Θ′ → Tm Θ′ Γ) Θₜ)
      → BindTyP Φ B θ bnd
      → Φ ⊢[ θ ] `Lam bnd ∶ ∀↑ B
⊢Lam↑ (use body)  ⊢t = ⊢Lamᵘ ⊢t
⊢Lam↑ (drop body) ⊢t = ⊢Lamᵈ ⊢t
