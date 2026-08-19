{-# OPTIONS --rewriting --local-confluence-check #-}
-- ⚠ MEASUREMENT PROBE — NOT PART OF THE DEVELOPMENT ⚠
-- This file is EXPECTED TO FAIL.  `agda SemRewriteProbeO.agda` → exit 42.
-- Round 3: ⊛ᵀ made `opaque`; record η still on; 6 rules.
-- Measured: 7 non-joinable pairs; RewriteLHSReduces 1 → 0, so the `opaque` fix works.
-- Nothing imports this file.  It exists so that §7 of
-- REPORT-adequacy.md is reproducible.
-- ════════════════════════════════════════════════════════════════════
-- EXPERIMENT: can the SEMANTIC transfer lemmas be registered as REWRITE
-- rules alongside SystemF-strat's syntactic σ-calculus?
--
-- ROUND 1 (recorded, then superseded).  Registering the single-variable
-- instance `⟦ T [ T′ ]* ⟧ᵀ η ↦ ⟦ T ⟧ᵀ (⟦ T′ ⟧ᵀ η ∷ η)` on its own, with
-- `Env*` as a `Setω` datatype, FAILS local confluence with 4 pairs:
--   vs `compositionalityˢˢ`, vs `beta-fold`,
--   vs `_[_]ˢ-clause1` (the `` ` α `` clause), vs `_[_]ˢ-clause3` (∀).
-- Diagnosis: a single-variable instance cannot join against the general
-- σ-laws; one needs the GENERAL semantic law plus a semantic mirror of
-- the whole σ-calculus (an action of renamings/substitutions on semantic
-- environments, with its own lift/compose/identity laws).
--
-- ROUND 2 (this file).  Those environment laws are equations between
-- semantic environments, so they can only be REWRITE rules if `Env*` is
-- an ordinary `Set` — Agda's `BUILTIN REWRITE` is `_≡_`, and there is no
-- `≡ω` rewriting.  So `Env*` is re-defined as a LEVEL-COMPUTING
-- RECURSIVE FUNCTION into `Set (maxL Δ)`, exactly like SystemF-strat's
-- `Env` and this development's `𝓓⟦_⟧`.  Then the semantic σ-calculus is
-- registrable in principle.  This file measures whether it is.
-- ════════════════════════════════════════════════════════════════════
module SemRewriteProbeO where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool)
open import Level using (Lift; lift; lower)
open import Function using (id)

open import SystemF-strat hiding (fundamental)

-- ── semantic environments as an ordinary Set (the round-2 move) ──
Env* : (Δ : LCtx) → Set (maxL Δ)
Env* ∅       = ⊤
Env* (l ∙ Δ) = Set l × Env* Δ

lookupᵀ : ∀ {Δ l} → Δ ∋ˡ l → Env* Δ → Set l
lookupᵀ here      η = proj₁ η
lookupᵀ (there α) η = lookupᵀ α (proj₂ η)

⟦_⟧ᵀ : ∀ {Δ l} → Type Δ l → Env* Δ → Set l
⟦ base l ⟧ᵀ        η = Lift l Bool
⟦ T₁ ⇒ T₂ ⟧ᵀ       η = ⟦ T₁ ⟧ᵀ η → ⟦ T₂ ⟧ᵀ η
⟦ ` α ⟧ᵀ           η = lookupᵀ α η
⟦ ∀α_ {l = l} T ⟧ᵀ η = (A : Set l) → ⟦ T ⟧ᵀ (A , η)

-- ══════════════ ROUND 3: the operations made `opaque` ══════════════
-- Round 2 measured (see SemRewriteProbeM.agda):
--   * `⊛ᵀ-lift` REJECTED with `RewriteLHSReduces`, because `⊛ᵀ` is a
--     transparent function that computes on Δ;
--   * `lookupᵀ-⊛ᵀ` registered but NON-CONFLUENT against `⊛ᵀ`'s own two
--     defining clauses (2 pairs).
-- Both are the documented "function-like things must be opaque" failure.
-- Round 3 wraps `⊛ᵀ` in `opaque`, exactly as SystemF-strat wraps its
-- syntactic maps, and re-measures.

opaque
  ⊛ᵀ : ∀ {Δ₁ Δ₂} → Ren Δ₁ Δ₂ → Env* Δ₂ → Env* Δ₁
  ⊛ᵀ {∅}       ζ η = tt
  ⊛ᵀ {l ∙ Δ₁}  ζ η = lookupᵀ (here &ᴿ ζ) η , ⊛ᵀ (wkᴿ ⨟ᴿ ζ) η

  lookupᵀ-⊛ᵀ : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
               lookupᵀ α (⊛ᵀ ζ η) ≡ lookupᵀ (α &ᴿ ζ) η
  lookupᵀ-⊛ᵀ here      ζ η = refl
  lookupᵀ-⊛ᵀ (there α) ζ η = lookupᵀ-⊛ᵀ α (wkᴿ ⨟ᴿ ζ) η

  ⊛ᵀ-wk : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (A : Set l) (η : Env* Δ₂) →
          ⊛ᵀ (ζ ⨟ᴿ wkᴿ) (A , η) ≡ ⊛ᵀ ζ η
  ⊛ᵀ-wk {Δ₁ = ∅}      ζ A η = refl
  ⊛ᵀ-wk {Δ₁ = l ∙ Δ₁} ζ A η = cong (lookupᵀ (here &ᴿ ζ) η ,_) (⊛ᵀ-wk (wkᴿ ⨟ᴿ ζ) A η)

  ⊛ᵀ-lift : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (A : Set l) (η : Env* Δ₂) →
            ⊛ᵀ (ζ ↑ᴿ) (A , η) ≡ (A , ⊛ᵀ ζ η)
  ⊛ᵀ-lift ζ A η = cong (A ,_) (⊛ᵀ-wk ζ A η)

  ⊛ᵀ-wk₀ : ∀ {Δ l} (A : Set l) (η : Env* Δ) → ⊛ᵀ wkᴿ (A , η) ≡ η
  ⊛ᵀ-wk₀ {Δ = ∅}     A η = refl
  ⊛ᵀ-wk₀ {Δ = l ∙ Δ} A η =
    cong (proj₁ η ,_) (trans (⊛ᵀ-wk wkᴿ A η) (⊛ᵀ-wk₀ (proj₁ η) (proj₂ η)))

  ⊛ᵀ-id : ∀ {Δ} (η : Env* Δ) → ⊛ᵀ idᴿ η ≡ η
  ⊛ᵀ-id {∅}     η = refl
  ⊛ᵀ-id {l ∙ Δ} η = cong (proj₁ η ,_) (trans (⊛ᵀ-wk idᴿ (proj₁ η) (proj₂ η)) (⊛ᵀ-id (proj₂ η)))

  ⊛ᵀ-comp : ∀ {Δ₁ Δ₂ Δ₃} (ζ₁ : Ren Δ₁ Δ₂) (ζ₂ : Ren Δ₂ Δ₃) (η : Env* Δ₃) →
            ⊛ᵀ (ζ₁ ⨟ᴿ ζ₂) η ≡ ⊛ᵀ ζ₁ (⊛ᵀ ζ₂ η)
  ⊛ᵀ-comp {Δ₁ = ∅}      ζ₁ ζ₂ η = refl
  ⊛ᵀ-comp {Δ₁ = l ∙ Δ₁} ζ₁ ζ₂ η =
    cong₂ _,_ (sym (lookupᵀ-⊛ᵀ (here &ᴿ ζ₁) ζ₂ η)) (⊛ᵀ-comp (wkᴿ ⨟ᴿ ζ₁) ζ₂ η)

opaque
  unfolding ⊛ᵀ
  ⟦⟧ᵀ-ren : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
            ⟦ T [ ζ ]ᴿ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊛ᵀ ζ η)
  ⟦⟧ᵀ-ren (base l)  ζ η = refl
  ⟦⟧ᵀ-ren (` α)     ζ η = sym (lookupᵀ-⊛ᵀ α ζ η)
  ⟦⟧ᵀ-ren (T₁ ⇒ T₂) ζ η = cong₂ (λ A B → A → B) (⟦⟧ᵀ-ren T₁ ζ η) (⟦⟧ᵀ-ren T₂ ζ η)
  ⟦⟧ᵀ-ren (∀α_ {l = l} T) ζ η =
    cong (λ f → (A : Set l) → f A)
         (fun-ext λ A → trans (⟦⟧ᵀ-ren T (ζ ↑ᴿ) (A , η))
                              (cong ⟦ T ⟧ᵀ (⊛ᵀ-lift ζ A η)))

-- REGISTRATION: the renaming half of the semantic σ-calculus.
{-# REWRITE lookupᵀ-⊛ᵀ ⊛ᵀ-lift ⊛ᵀ-wk₀ ⊛ᵀ-id ⊛ᵀ-comp ⟦⟧ᵀ-ren #-}

-- FIRING PROBES
probe-ren-abstract : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
                     ⟦ T [ ζ ]ᴿ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊛ᵀ ζ η)
probe-ren-abstract T ζ η = refl

probe-ren-⇒ : ∀ {Δ₁ Δ₂ l₁ l₂} (T₁ : Type Δ₁ l₁) (T₂ : Type Δ₁ l₂)
              (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
              ⟦ (T₁ ⇒ T₂) [ ζ ]ᴿ ⟧ᵀ η ≡ (⟦ T₁ ⟧ᵀ (⊛ᵀ ζ η) → ⟦ T₂ ⟧ᵀ (⊛ᵀ ζ η))
probe-ren-⇒ T₁ T₂ ζ η = refl

probe-ren-∀ : ∀ {Δ₁ Δ₂ lα l′} (T : Type (lα ∙ Δ₁) l′) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
              ⟦ (∀α_ {l = lα} T) [ ζ ]ᴿ ⟧ᵀ η ≡ ((A : Set lα) → ⟦ T ⟧ᵀ (A , ⊛ᵀ ζ η))
probe-ren-∀ T ζ η = refl

probe-weaken : ∀ {Δ l l′} (T : Type Δ l′) (A : Set l) (η : Env* Δ) →
               ⟦ weaken T ⟧ᵀ (A , η) ≡ ⟦ T ⟧ᵀ η
probe-weaken T A η = refl

probe-weaken-∀ : ∀ {Δ l lα l′} (T : Type (lα ∙ Δ) l′) (A : Set l) (η : Env* Δ) →
                 ⟦ weaken (∀α_ {l = lα} T) ⟧ᵀ (A , η) ≡ ((B : Set lα) → ⟦ T ⟧ᵀ (B , η))
probe-weaken-∀ T A η = refl
