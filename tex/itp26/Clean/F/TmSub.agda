{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.F.TmSub — the TERM-substitution engine for System F (pure term-sub).
--
-- A term-sub maps each TERM-position of Γ to a BI-SCOPED term `Bi Tm Θ Δ`.  The
-- TYPE scope Θ is ambient/shared (a term-sub never changes types) — `subTm` only
-- THREADS a free type-thinning `Θ′ ⊑ Θ` that embeds each source subterm's tight
-- type-scope, and RENAMES annotations by it.  Two lifts:
--   liftΓ (under λ): standard term-lift  (var₀ᵇ ∙ wkΓ-targets)
--   liftΘ (under Λ): o'-extend every target's TYPE-thinning  — the free cross-term.
-- No bundled vector: the off-scope component is a thinning, carried for free.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.TmSub where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Agda.Builtin.Equality.Rewrite
open import Clean.F.Ty using (Ty)
open import Clean.F.Tm public   -- Tm, Bi, var₀ᵇ/appᵇ/lamᵇ/Lamᵇ/Appᵇ, + Pos/Scaffold/Thin
postulate funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g

-- ── the term-substitution container ──
TmSub : Scope → Scope → Scope → Set
TmSub Θ Δ Γ = Pos Γ → Bi Tm Θ Δ
_↾_ : ∀ {Θ Δ sup Γ} → TmSub Θ Δ Γ → sup ⊑ Γ → TmSub Θ Δ sup
(σ ↾ θ) p = σ (p ⨾ θ)
infixl 8 _↾_
selL : ∀ {Θ Δ Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → TmSub Θ Δ Γ → TmSub Θ Δ Γₗ
selL cv σ = σ ↾ thinL cv
selR : ∀ {Θ Δ Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → TmSub Θ Δ Γ → TmSub Θ Δ Γᵣ
selR cv σ = σ ↾ thinR cv

-- target weakenings on whole subs (wkΓ-T/wkΘ-T come from Clean.F.Tm)
wkΓ-Sub : ∀ {Θ Δ Γ} → TmSub Θ Δ Γ → TmSub Θ (tt ∷ Δ) Γ
wkΓ-Sub σ p = wkΓ-T (σ p)
wkΘ-Sub : ∀ {Θ Δ Γ} → TmSub Θ Δ Γ → TmSub (tt ∷ Θ) Δ Γ
wkΘ-Sub σ p = wkΘ-T (σ p)

-- ── PRIMITIVES (opaque) ──
opaque
  idS  : ∀ {Θ Γ} → TmSub Θ Γ Γ
  ↑ₛ   : ∀ {Θ Γ} → TmSub Θ (tt ∷ Γ) Γ
  _∙_  : ∀ {Θ Δ Γ} → Bi Tm Θ Δ → TmSub Θ Δ Γ → TmSub Θ Δ (tt ∷ Γ)
  idS p = tmvar ⇑[ oe , p ]
  ↑ₛ  p = tmvar ⇑[ oe , o' p ]
  (u ∙ σ) (os p) = u
  (u ∙ σ) (o' p) = σ p
infixr 5 _∙_
-- NB: the cons-APPLICATION clauses ((u∙σ)(os/o' p)) CANNOT be rewrites — they are
-- non-confluent with IdCons (var₀ᵇ∙↑ₛ≡idS) / SCons.  Consumers needing them (liftΓ-pres)
-- unfold `_∙_` in a local Layer-A island instead.

-- the two lifts (transparent — re-expressed in primitives for the laws later)
liftΓ : ∀ {Θ Δ Γ} → TmSub Θ Δ Γ → TmSub Θ (tt ∷ Δ) (tt ∷ Γ)
liftΓ σ = var₀ᵇ ∙ wkΓ-Sub σ
liftΘ : ∀ {Θ Δ Γ} → TmSub Θ Δ Γ → TmSub (tt ∷ Θ) Δ Γ
liftΘ σ = wkΘ-Sub σ

-- ── THE TERM-SUBSTITUTION ACTION ──
-- subTm t φ σ : substitute the term-vars of `t : Tm Θ′ Γ` by σ, embedding t's
-- type-scope into the ambient Θ via φ (annotations are RENAMED by the composed φ).
subTm : ∀ {Θ′ Θ Γ Δ} → Tm Θ′ Γ → Θ′ ⊑ Θ → TmSub Θ Δ Γ → Bi Tm Θ Δ
subTm tmvar               φ σ = σ oi
subTm (app l r cθ cγ)     φ σ =
  appᵇ (subTm l (thinL cθ ⨾ φ) (selL cγ σ)) (subTm r (thinR cθ ⨾ φ) (selR cγ σ))
subTm (lam a (use t) cθ)  φ σ =
  lamᵇ (a ⇑ (thinL cθ ⨾ φ)) (subTm t (thinR cθ ⨾ φ) (liftΓ σ))
subTm (lam a (drop t) cθ) φ σ =
  lamᵇ (a ⇑ (thinL cθ ⨾ φ)) (wkΓ-T (subTm t (thinR cθ ⨾ φ) σ))
subTm (Lam (use t))       φ σ = Lamᵇ (subTm t (os φ) (liftΘ σ))
subTm (Lam (drop t))      φ σ = Lamᵇ (wkΘ-T (subTm t φ σ))
subTm (App e a cθ)        φ σ = Appᵇ (subTm e (thinL cθ ⨾ φ) σ) (a ⇑ (thinR cθ ⨾ φ))

-- apply a term-sub to a bi-scoped term: the type-thinning becomes φ, the term-thinning restricts σ
opaque
  _⟪_⟫ : ∀ {Θ Δ Γ} → Bi Tm Θ Γ → TmSub Θ Δ Γ → Bi Tm Θ Δ
  (t ⇑[ θ , φ ]) ⟪ σ ⟫ = subTm t θ (σ ↾ φ)
infixl 8 _⟪_⟫

-- term-sub composition (the type scope Θ is shared throughout — a term-sub never touches types)
opaque
  unfolding _⟪_⟫
  _⨟_ : ∀ {Θ Δ Ξ Γ} → TmSub Θ Δ Γ → TmSub Θ Ξ Δ → TmSub Θ Ξ Γ
  (σ ⨟ τ) p = (σ p) ⟪ τ ⟫
infixl 6 _⨟_
