{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.SystemF2VTyping — extrinsic typing + SUBJECT REDUCTION for the co-de-Bruijn
-- VECTOR System F (3 sorts: ty, vl, tm).  Mirrors Sf.STLCTyping's SR template,
-- specialised to the two-scope vector engine of Sf.SystemF2V.
--
--   • VALUE context `Φ : TmCx Θ Γ` is TIGHT over the value scope Γ; each stored
--     type is `Ty ↑ Θ` over the FULL type scope Θ.  Value-variable typing is FREE
--     (no factor), exactly as in the validated Sf.SystemF2Typing gate.
--   • The TYPE scope Θ is FULL; types only WEAKEN along the type-cover thinnings.
--   • Term/value RENAMING is genuinely free: there is NO `⊢-ren`.  The two scopes'
--     covers stay INDEPENDENT (value side via cohLᵗ/cohRᵗ, type side via Fac-L/R).
-- ════════════════════════════════════════════════════════════════════════════
module Sf.SystemF2VTyping where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite
open import Sf.SystemF2V
open import Sf.SystemF2VCoh                 -- type-distribution rewrites
open import Sf.Fac ⊤ public                 -- Fac-L/R for the TYPE thinnings

-- ════════════════════════════════════════════════════════════════════════════
-- VALUE CONTEXT `TmCx Θ Γ` — one stored type `Ty ↑ Θ` per value-var of Γ.
-- (verbatim Sf.SystemF2Typing.)
-- ════════════════════════════════════════════════════════════════════════════
data TmCx (Θ : Scope) : Scope → Set where
  ε    : TmCx Θ []
  _,-_ : ∀ {Γ} → TmCx Θ Γ → Ty ↑ Θ → TmCx Θ (tt ∷ Γ)
infixl 5 _,-_

restᵗ : ∀ {Θ Δ Γ} → Δ ⊑ Γ → TmCx Θ Γ → TmCx Θ Δ
restᵗ oz     ε        = ε
restᵗ (os θ) (Φ ,- A) = restᵗ θ Φ ,- A
restᵗ (o' θ) (Φ ,- A) = restᵗ θ Φ

thLᵗ : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Γₗ ⊑ Γ
thLᵗ czz = oz ; thLᵗ (css c) = os (thLᵗ c) ; thLᵗ (cs' c) = os (thLᵗ c) ; thLᵗ (c's c) = o' (thLᵗ c)
thRᵗ : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Γᵣ ⊑ Γ
thRᵗ czz = oz ; thRᵗ (css c) = os (thRᵗ c) ; thRᵗ (cs' c) = o' (thRᵗ c) ; thRᵗ (c's c) = os (thRᵗ c)

splitLᵗ : ∀ {Θ Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → TmCx Θ Γ → TmCx Θ Γₗ
splitLᵗ cv Φ = restᵗ (thLᵗ cv) Φ
splitRᵗ : ∀ {Θ Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → TmCx Θ Γ → TmCx Θ Γᵣ
splitRᵗ cv Φ = restᵗ (thRᵗ cv) Φ

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

-- TYPE-weakening of the whole value context (under Λ).
wkCx : ∀ {Θ Γ} → TmCx Θ Γ → TmCx (tt ∷ Θ) Γ
wkCx ε        = ε
wkCx (Φ ,- A) = wkCx Φ ,- wk↑ tt A

-- ════════════════════════════════════════════════════════════════════════════
-- THE TYPING JUDGEMENTS  (mutually recursive for values and terms).
--   Φ : TmCx Θ Γ   tight value context, types over the FULL Θ
--   θ : Θₜ ⊑ Θ     the TYPE thinning (value scope carries NO thinning)
--   A : Ty ↑ Θ
-- ════════════════════════════════════════════════════════════════════════════
data _⊢v[_]_∶_ : ∀ {Θₜ Θ Γ} → TmCx Θ Γ → Θₜ ⊑ Θ → Vl Θₜ Γ → Ty ↑ Θ → Set
data _⊢t[_]_∶_ : ∀ {Θₜ Θ Γ} → TmCx Θ Γ → Θₜ ⊑ Θ → Tm Θₜ Γ → Ty ↑ Θ → Set
infix 4 _⊢v[_]_∶_
infix 4 _⊢t[_]_∶_

data _⊢v[_]_∶_ where
  -- the value variable.  TYPE-support [] (θ = oe); value context = ε ,- A.  FREE.
  ⊢vlvar : ∀ {Θ}{A : Ty ↑ Θ} → (ε ,- A) ⊢v[ oe ] vlvar ∶ A
  -- λ(x:a). body — body binds a VALUE var (tight context GROWS).
  ⊢lamᵘ : ∀ {Θₐ Θᵦ Θₜ Θ Γ}{Φ : TmCx Θ Γ}{a : Ty Θₐ}{body : Tm Θᵦ (tt ∷ Γ)}
            {cθ : Cover Θₐ Θᵦ Θₜ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ Θ}
        → (Φ ,- (a ⇑ (thinL cθ ⨾ θ))) ⊢t[ thinR cθ ⨾ θ ] body ∶ B
        → Φ ⊢v[ θ ] lam a (use body) cθ ∶ ((a ⇑ (thinL cθ ⨾ θ)) ⇒↑ B)
  ⊢lamᵈ : ∀ {Θₐ Θᵦ Θₜ Θ Γ}{Φ : TmCx Θ Γ}{a : Ty Θₐ}{body : Tm Θᵦ Γ}
            {cθ : Cover Θₐ Θᵦ Θₜ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ Θ}
        → Φ ⊢t[ thinR cθ ⨾ θ ] body ∶ B
        → Φ ⊢v[ θ ] lam a (drop body) cθ ∶ ((a ⇑ (thinL cθ ⨾ θ)) ⇒↑ B)
  -- Λα. body — body binds a TYPE var (type scope GROWS, wkCx).
  ⊢Lamᵘ : ∀ {Θₜ Θ Γ}{Φ : TmCx Θ Γ}{body : Tm (tt ∷ Θₜ) Γ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ (tt ∷ Θ)}
        → wkCx Φ ⊢t[ os θ ] body ∶ B
        → Φ ⊢v[ θ ] Lam (use body) ∶ ∀↑ B
  ⊢Lamᵈ : ∀ {Θₜ Θ Γ}{Φ : TmCx Θ Γ}{body : Tm Θₜ Γ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ (tt ∷ Θ)}
        → wkCx Φ ⊢t[ o' θ ] body ∶ B
        → Φ ⊢v[ θ ] Lam (drop body) ∶ ∀↑ B

data _⊢t[_]_∶_ where
  -- vt v : a value used as a term.
  ⊢vt : ∀ {Θₜ Θ Γ}{Φ : TmCx Θ Γ}{v : Vl Θₜ Γ}{θ : Θₜ ⊑ Θ}{A : Ty ↑ Θ}
      → Φ ⊢v[ θ ] v ∶ A → Φ ⊢t[ θ ] vt v ∶ A
  -- s t : application.  cγ splits the value context; cθ merges the type supports.
  ⊢app : ∀ {Θₗ Θᵣ Θₜ Θ Γₗ Γᵣ Γ}{Φ : TmCx Θ Γ}
           {l : Tm Θₗ Γₗ}{r : Tm Θᵣ Γᵣ}{cθ : Cover Θₗ Θᵣ Θₜ}{θ : Θₜ ⊑ Θ}
           {cγ : Cover Γₗ Γᵣ Γ}{A B : Ty ↑ Θ}
       → splitLᵗ cγ Φ ⊢t[ thinL cθ ⨾ θ ] l ∶ (A ⇒↑ B)
       → splitRᵗ cγ Φ ⊢t[ thinR cθ ⨾ θ ] r ∶ A
       → Φ ⊢t[ θ ] app l r cθ cγ ∶ B
  -- s a : type application.  Result B[a] via the singleton TYPE substitution.
  ⊢tapp : ∀ {Θₑ Θₐ Θₜ Θ Γ}{Φ : TmCx Θ Γ}
            {e : Tm Θₑ Γ}{a : Ty Θₐ}{cθ : Cover Θₑ Θₐ Θₜ}{θ : Θₜ ⊑ Θ}{B : Ty ↑ (tt ∷ Θ)}
        → Φ ⊢t[ thinL cθ ⨾ θ ] e ∶ ∀↑ B
        → Φ ⊢t[ θ ] tapp e a cθ ∶ (B ⟪ idS ,- (a ⇑ (thinR cθ ⨾ θ)) ⟫T)

-- ════════════════════════════════════════════════════════════════════════════
-- TYPING of BI-SCOPED things-with-thinnings: restrict the value context to the
-- value-support (TIGHT), type at the type-thinning.
-- ════════════════════════════════════════════════════════════════════════════
_⊢t↑_∶_ : ∀ {Θ Γ} → TmCx Θ Γ → Bi Tm Θ Γ → Ty ↑ Θ → Set
Φ ⊢t↑ (t ⇑[ θ , φ ]) ∶ A = restᵗ φ Φ ⊢t[ θ ] t ∶ A
infix 4 _⊢t↑_∶_
_⊢v↑_∶_ : ∀ {Θ Γ} → TmCx Θ Γ → Bi Vl Θ Γ → Ty ↑ Θ → Set
Φ ⊢v↑ (v ⇑[ θ , φ ]) ∶ A = restᵗ φ Φ ⊢v[ θ ] v ∶ A
infix 4 _⊢v↑_∶_

-- ── typed smart constructors (DEFINITIONAL via cohLᵗ/cohRᵗ + Fac-L/R) ──
-- s t : merge both scopes; value context split via the value cover, type supports
-- merged via the type cover.  No factor — the two scopes are independent.
⊢appᵇ : ∀ {Θ Γ}{Φ : TmCx Θ Γ}{A B : Ty ↑ Θ}(l′ r′ : Bi Tm Θ Γ)
      → Φ ⊢t↑ l′ ∶ (A ⇒↑ B) → Φ ⊢t↑ r′ ∶ A → Φ ⊢t↑ (appᵇ l′ r′) ∶ B
⊢appᵇ {Φ = Φ} (l ⇑[ θₗ , φₗ ]) (r ⇑[ θᵣ , φᵣ ]) ⊢l ⊢r =
  ⊢app {Φ = restᵗ (out (cop φₗ φᵣ)) Φ} {cθ = cov (cop θₗ θᵣ)} {θ = out (cop θₗ θᵣ)}
       {cγ = cov (cop φₗ φᵣ)} ⊢l ⊢r

-- vt v : value-as-term.
⊢vtᵇ : ∀ {Θ Γ}{Φ : TmCx Θ Γ}{A : Ty ↑ Θ}(v′ : Bi Vl Θ Γ)
     → Φ ⊢v↑ v′ ∶ A → Φ ⊢t↑ (vtᵇ v′) ∶ A
⊢vtᵇ (v ⇑[ θ , φ ]) ⊢v = ⊢vt ⊢v

-- s a : type application.  Result B[a] via the singleton TYPE substitution.
⊢tappᵇ : ∀ {Θ Γ}{Φ : TmCx Θ Γ}{supΘₑ : Scope}(B : Ty ↑ (tt ∷ Θ))
           (e : Tm supΘₑ Γ)(θₑ : supΘₑ ⊑ Θ)
           {supΘₐ}(a : Ty supΘₐ)(θₐ : supΘₐ ⊑ Θ)
       → Φ ⊢t[ θₑ ] e ∶ ∀↑ B
       → Φ ⊢t↑ (tappᵇ (e ⇑[ θₑ , oi ]) (a ⇑ θₐ)) ∶ (B ⟪ idS ,- (a ⇑ θₐ) ⟫T)
⊢tappᵇ B e θₑ a θₐ ⊢e = ⊢tapp {cθ = cov (cop θₑ θₐ)} {θ = out (cop θₑ θₐ)} {B = B} ⊢e

-- ════════════════════════════════════════════════════════════════════════════
-- WELL-TYPED VECTOR SUBSTITUTION.  A vector (στ , σ) is well-typed from source
-- context Φ′ (over Θ′) to target Φ (over Θ): each VALUE entry of σ has the type
-- stored in Φ′, TRANSPORTED by the type substitution στ (= A⟪στ⟫T).  The TYPE
-- component στ : Sub Θ Θ′ is unconstrained (types are kind-trivial in System F).
-- ════════════════════════════════════════════════════════════════════════════
data WtVSub {Θ′ Θ Γ : Scope}(στ : Sub Θ Θ′)
     : ∀ {Γ′} → VSub Θ Γ Γ′ → TmCx Θ′ Γ′ → TmCx Θ Γ → Set where
  []   : ∀ {Φ : TmCx Θ Γ} → WtVSub στ [] ε Φ
  _,-_ : ∀ {Γ′}{σ : VSub Θ Γ Γ′}{Φ′ : TmCx Θ′ Γ′}{Φ : TmCx Θ Γ}{u}{A}
       → WtVSub στ σ Φ′ Φ → Φ ⊢v↑ u ∶ (A ⟪ στ ⟫T) → WtVSub στ (σ ,- u) (Φ′ ,- A) Φ

-- ════════════════════════════════════════════════════════════════════════════
-- VECTOR-SUBSTITUTION PRESERVATION HELPERS.  The value cover splits the SOURCE
-- value context; στ is THREADED UNCHANGED (the cover acts on Γ′, not on στ).
-- ════════════════════════════════════════════════════════════════════════════
selLV-pres : ∀ {Θ′ Θ Γ Γₗ Γᵣ Γ′}{στ : Sub Θ Θ′}{σ : VSub Θ Γ Γ′}{Φ′ : TmCx Θ′ Γ′}{Φ : TmCx Θ Γ}
             (cv : Cover Γₗ Γᵣ Γ′) → WtVSub στ σ Φ′ Φ → WtVSub στ (selLV cv σ) (splitLᵗ cv Φ′) Φ
selLV-pres czz     []         = []
selLV-pres (css c) (wσ ,- ⊢u) = selLV-pres c wσ ,- ⊢u
selLV-pres (cs' c) (wσ ,- ⊢u) = selLV-pres c wσ ,- ⊢u
selLV-pres (c's c) (wσ ,- ⊢u) = selLV-pres c wσ
selRV-pres : ∀ {Θ′ Θ Γ Γₗ Γᵣ Γ′}{στ : Sub Θ Θ′}{σ : VSub Θ Γ Γ′}{Φ′ : TmCx Θ′ Γ′}{Φ : TmCx Θ Γ}
             (cv : Cover Γₗ Γᵣ Γ′) → WtVSub στ σ Φ′ Φ → WtVSub στ (selRV cv σ) (splitRᵗ cv Φ′) Φ
selRV-pres czz     []         = []
selRV-pres (css c) (wσ ,- ⊢u) = selRV-pres c wσ ,- ⊢u
selRV-pres (cs' c) (wσ ,- ⊢u) = selRV-pres c wσ
selRV-pres (c's c) (wσ ,- ⊢u) = selRV-pres c wσ ,- ⊢u

-- ── VALUE-binder lift (⇑vl): value-weaken targets, cons the fresh value var. ──
-- value-weakening a typed value: o' on the value thinning, restᵗ(o' φ)(Φ,-C)=restᵗ φ Φ.
⊢wkΓ-v : ∀ {Θ Γ}{Φ : TmCx Θ Γ}(C : Ty ↑ Θ){A : Ty ↑ Θ}(u : Bi Vl Θ Γ)
       → Φ ⊢v↑ u ∶ A → (Φ ,- C) ⊢v↑ (wkΓ-V u) ∶ A
⊢wkΓ-v C (v ⇑[ θ , φ ]) ⊢u = ⊢u

wkΓ-VSub-pres : ∀ {Θ′ Θ Γ Γ′}{στ : Sub Θ Θ′}{σ : VSub Θ Γ Γ′}{Φ′ : TmCx Θ′ Γ′}{Φ : TmCx Θ Γ}(C : Ty ↑ Θ)
              → WtVSub στ σ Φ′ Φ → WtVSub στ (wkΓ-VSub σ) Φ′ (Φ ,- C)
wkΓ-VSub-pres C []          = []
wkΓ-VSub-pres C (_,-_ {u = u} wσ ⊢u) = wkΓ-VSub-pres C wσ ,- ⊢wkΓ-v C u ⊢u

-- the fresh bound value var, typed (restᵗ-oe fires ⇒ context = ε ,- A).  It is ⊢vlvar.
⊢freshv : ∀ {Θ Γ}{Φ : TmCx Θ Γ}{A : Ty ↑ Θ} → (Φ ,- A) ⊢v↑ vlvar₀ ∶ A
⊢freshv {A = A} = ⊢vlvar {A = A}

-- ════════════════════════════════════════════════════════════════════════════
-- TYPE-SCOPE RENAMING of a derivation (the cross-term's typing cost).  A type
-- thinning ψ : Θ ⊑ Θ′ re-embeds the WHOLE derivation: the value context's stored
-- types get ⟨ψ⟩, the type thinning becomes θ⨾ψ, the result type A⟨ψ⟩.  This is the
-- ONLY place SR uses `subst` on the TYPE side — it is the type-former-distribution
-- residue (⇒↑/∀↑ commuting with renaming), which CANNOT be a confluent rewrite.
-- The VALUE scope is untouched ⇒ value/term renaming stays FREE (no value ⊢-ren).
-- ════════════════════════════════════════════════════════════════════════════
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

renCx : ∀ {Θ Θ′ Γ} → Θ ⊑ Θ′ → TmCx Θ Γ → TmCx Θ′ Γ
renCx ψ ε        = ε
renCx ψ (Φ ,- A) = renCx ψ Φ ,- (A ⟨ ψ ⟩)

-- renCx commutes with restᵗ (value-scope restriction touches only which entries
-- survive, ⟨ψ⟩ rides along) — structural, no subst.
renCx-restᵗ : ∀ {Θ Θ′ Δ Γ}(ψ : Θ ⊑ Θ′)(φ : Δ ⊑ Γ)(Φ : TmCx Θ Γ)
            → restᵗ φ (renCx ψ Φ) ≡ renCx ψ (restᵗ φ Φ)
renCx-restᵗ ψ oz     ε        = refl
renCx-restᵗ ψ (os φ) (Φ ,- A) = cong (_,- (A ⟨ ψ ⟩)) (renCx-restᵗ ψ φ Φ)
renCx-restᵗ ψ (o' φ) (Φ ,- A) = renCx-restᵗ ψ φ Φ

-- renCx commutes with wkCx (type-context weakening), modulo wk↑/⟨os ψ⟩.
opaque
  unfolding _⨾_
  wk↑-⟨os⟩ : ∀ {Θ Θ′}(ψ : Θ ⊑ Θ′)(A : Ty ↑ Θ) → (wk↑ tt A) ⟨ os ψ ⟩ ≡ wk↑ tt (A ⟨ ψ ⟩)
  wk↑-⟨os⟩ ψ (a ⇑ ξ) = refl
renCx-wkCx : ∀ {Θ Θ′ Γ}(ψ : Θ ⊑ Θ′)(Φ : TmCx Θ Γ) → wkCx (renCx ψ Φ) ≡ renCx (os ψ) (wkCx Φ)
renCx-wkCx ψ ε        = refl
renCx-wkCx ψ (Φ ,- A) = cong₂ _,-_ (renCx-wkCx ψ Φ) (sym (wk↑-⟨os⟩ ψ A))
  where open import Relation.Binary.PropositionalEquality using (cong₂)

-- the renamed value var: oe ⨾ ψ ≡ oe (oi⨾ rewrite handles oe via library), so direct.
opaque
  unfolding oe _⨾_
  oe⨾ψ : ∀ {Θ Θ′}(ψ : Θ ⊑ Θ′) → oe ⨾ ψ ≡ oe
  oe⨾ψ oz     = refl
  oe⨾ψ (os ψ) = cong o' (oe⨾ψ ψ)
  oe⨾ψ (o' ψ) = cong o' (oe⨾ψ ψ)
opaque
  unfolding _⨾_
  ⨾-osos : ∀ {Θₜ Θ Θ′}(θ : Θₜ ⊑ Θ)(ψ : Θ ⊑ Θ′) → os θ ⨾ os ψ ≡ os (θ ⨾ ψ)
  ⨾-osos θ ψ = refl
  ⨾-o'os : ∀ {Θₜ Θ Θ′}(θ : Θₜ ⊑ Θ)(ψ : Θ ⊑ Θ′) → o' θ ⨾ os ψ ≡ o' (θ ⨾ ψ)
  ⨾-o'os θ ψ = refl

-- the THE TYPE-RENAMING preservation (mutual).  ψ : Θ ⊑ Θ′ re-embeds a derivation.
⊢ren-v : ∀ {Θₜ Θ Θ′ Γ}{Φ : TmCx Θ Γ}{θ : Θₜ ⊑ Θ}{v : Vl Θₜ Γ}{A : Ty ↑ Θ}(ψ : Θ ⊑ Θ′)
       → Φ ⊢v[ θ ] v ∶ A → renCx ψ Φ ⊢v[ θ ⨾ ψ ] v ∶ (A ⟨ ψ ⟩)
⊢ren-t : ∀ {Θₜ Θ Θ′ Γ}{Φ : TmCx Θ Γ}{θ : Θₜ ⊑ Θ}{t : Tm Θₜ Γ}{A : Ty ↑ Θ}(ψ : Θ ⊑ Θ′)
       → Φ ⊢t[ θ ] t ∶ A → renCx ψ Φ ⊢t[ θ ⨾ ψ ] t ∶ (A ⟨ ψ ⟩)

⊢ren-v {A = A} ψ (⊢vlvar {A = A0}) =
  subst (λ φ → (ε ,- (A0 ⟨ ψ ⟩)) ⊢v[ φ ] vlvar ∶ (A0 ⟨ ψ ⟩)) (sym (oe⨾ψ ψ)) ⊢vlvar
⊢ren-v {Φ = Φ} ψ (⊢lamᵘ {a = a}{cθ = cθ}{θ = θ}{B = B} ⊢t) =
  subst (λ T → renCx ψ Φ ⊢v[ θ ⨾ ψ ] _ ∶ T) (sym (→↑-⟨⟩ (a ⇑ (thinL cθ ⨾ θ)) B ψ))
    (⊢lamᵘ {cθ = cθ}{θ = θ ⨾ ψ}{B = B ⟨ ψ ⟩} (⊢ren-t ψ ⊢t))
⊢ren-v {Φ = Φ} ψ (⊢lamᵈ {a = a}{cθ = cθ}{θ = θ}{B = B} ⊢t) =
  subst (λ T → renCx ψ Φ ⊢v[ θ ⨾ ψ ] _ ∶ T) (sym (→↑-⟨⟩ (a ⇑ (thinL cθ ⨾ θ)) B ψ))
    (⊢lamᵈ {cθ = cθ}{θ = θ ⨾ ψ}{B = B ⟨ ψ ⟩} (⊢ren-t ψ ⊢t))
⊢ren-v ψ (⊢Lamᵘ {Φ = Φ}{θ = θ}{B = B} ⊢t) =
  subst (λ T → renCx ψ Φ ⊢v[ θ ⨾ ψ ] _ ∶ T) (sym (∀↑-⟨⟩ B ψ))
    (⊢Lamᵘ {θ = θ ⨾ ψ}{B = B ⟨ os ψ ⟩}
      (subst (λ Ψ → Ψ ⊢t[ os (θ ⨾ ψ) ] _ ∶ (B ⟨ os ψ ⟩)) (renCx-wkCx ψ Φ)
        (subst (λ φ → renCx (os ψ) (wkCx Φ) ⊢t[ φ ] _ ∶ (B ⟨ os ψ ⟩)) (⨾-osos θ ψ) (⊢ren-t (os ψ) ⊢t))))
⊢ren-v ψ (⊢Lamᵈ {Φ = Φ}{θ = θ}{B = B} ⊢t) =
  subst (λ T → renCx ψ Φ ⊢v[ θ ⨾ ψ ] _ ∶ T) (sym (∀↑-⟨⟩ B ψ))
    (⊢Lamᵈ {θ = θ ⨾ ψ}{B = B ⟨ os ψ ⟩}
      (subst (λ Ψ → Ψ ⊢t[ o' (θ ⨾ ψ) ] _ ∶ (B ⟨ os ψ ⟩)) (renCx-wkCx ψ Φ)
        (subst (λ φ → renCx (os ψ) (wkCx Φ) ⊢t[ φ ] _ ∶ (B ⟨ os ψ ⟩)) (⨾-o'os θ ψ) (⊢ren-t (os ψ) ⊢t))))

⊢ren-t ψ (⊢vt ⊢v) = ⊢vt (⊢ren-v ψ ⊢v)
⊢ren-t ψ (⊢app {Φ = Φ}{cθ = cθ}{θ = θ}{cγ = cγ}{A = A}{B = B} ⊢l ⊢r) =
  ⊢app {cθ = cθ}{θ = θ ⨾ ψ}{cγ = cγ}{A = A ⟨ ψ ⟩}{B = B ⟨ ψ ⟩}
    (subst (λ Ψ → Ψ ⊢t[ thinL cθ ⨾ (θ ⨾ ψ) ] _ ∶ ((A ⟨ ψ ⟩) ⇒↑ (B ⟨ ψ ⟩)))
           (sym (renCx-restᵗ ψ (thLᵗ cγ) Φ))
           (subst (λ T → renCx ψ (splitLᵗ cγ Φ) ⊢t[ thinL cθ ⨾ (θ ⨾ ψ) ] _ ∶ T)
                  (→↑-⟨⟩ A B ψ) (⊢ren-t ψ ⊢l)))
    (subst (λ Ψ → Ψ ⊢t[ thinR cθ ⨾ (θ ⨾ ψ) ] _ ∶ (A ⟨ ψ ⟩)) (sym (renCx-restᵗ ψ (thRᵗ cγ) Φ)) (⊢ren-t ψ ⊢r))
⊢ren-t ψ (⊢tapp {cθ = cθ}{θ = θ}{B = B} ⊢e) = {!!}
