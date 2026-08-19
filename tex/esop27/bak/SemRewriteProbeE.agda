{-# OPTIONS --rewriting --local-confluence-check #-}
-- ⚠ MEASUREMENT PROBE — NOT PART OF THE DEVELOPMENT ⚠
-- This file is EXPECTED TO FAIL.  `agda SemRewriteProbeE.agda` → exit 42.
-- Round 3e: no-eta + the λσ⇑ discipline (opaque `ext`, lifting never expanded to a cons).
-- Measured: 4 non-joinable pairs — the push/lift survivor of round 3c is GONE; all 4 are `⟦⟧ᵀ-ren` lacking companion laws.
-- Nothing imports this file.  It exists so that §7 of
-- REPORT-adequacy.md is reproducible.
-- ROUND 3e: `no-eta-equality` + the λσ⇑ DISCIPLINE.
--
-- Round 3c (no-eta, isolated) left exactly ONE non-joinable pair:
--     lookupᵀ-⊛ᵀ  vs  ⊛ᵀ-lift
-- i.e. push (`lookupᵀ` through `⊛ᵀ`) against lift-expansion
-- (`⊛ᵀ (ζ ↑ᴿ) (A , η) ↦ (A , ⊛ᵀ ζ η)`), non-joinable at an ABSTRACT type
-- variable.  That is NOT an η problem — it is the very overlap that
-- SystemF-strat's SYNTACTIC calculus avoids by keeping lifting
-- first-class and NEVER expanding `ζ ↑ᴿ` into a cons (λσ⇑ style; the
-- rules `beta-lift-zero`/`beta-lift-suc` case on the VARIABLE instead).
--
-- This round transplants that discipline: environment extension becomes
-- an opaque `ext`, and the lift law is oriented so that `ext` is pushed
-- INSIDE `⊛ᵀ` rather than `⊛ᵀ (ζ ↑ᴿ)` being expanded outwards:
--     ext A (⊛ᵀ ζ η)  ↦  ⊛ᵀ (ζ ↑ᴿ) (ext A η)
-- Prediction: the push/lift overlap disappears, because neither rule's
-- LHS is a subterm of the other's.
module SemRewriteProbeE where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool)
open import Level using (Lift; lift; lower)
open import Function using (id)

open import SystemF-strat hiding (fundamental)

record Pair {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  pattern
  constructor _,_
  field
    fst : A
    snd : B
open Pair public

Env* : (Δ : LCtx) → Set (maxL Δ)
Env* ∅       = ⊤
Env* (l ∙ Δ) = Pair (Set l) (Env* Δ)

opaque
  -- environment extension, FIRST-CLASS and opaque (the analogue of
  -- strat's opaque `_↑ᴿ`)
  ext : ∀ {Δ l} → Set l → Env* Δ → Env* (l ∙ Δ)
  ext A η = A , η

  lookupᵀ : ∀ {Δ l} → Δ ∋ˡ l → Env* Δ → Set l
  lookupᵀ here      η = fst η
  lookupᵀ (there α) η = lookupᵀ α (snd η)

  lookupᵀ-here : ∀ {Δ l} (A : Set l) (η : Env* Δ) → lookupᵀ here (ext A η) ≡ A
  lookupᵀ-here A η = refl

  lookupᵀ-there : ∀ {Δ l l′} (α : Δ ∋ˡ l) (A : Set l′) (η : Env* Δ) →
                  lookupᵀ (there α) (ext A η) ≡ lookupᵀ α η
  lookupᵀ-there α A η = refl

⟦_⟧ᵀ : ∀ {Δ l} → Type Δ l → Env* Δ → Set l
⟦ base l ⟧ᵀ        η = Lift l Bool
⟦ T₁ ⇒ T₂ ⟧ᵀ       η = ⟦ T₁ ⟧ᵀ η → ⟦ T₂ ⟧ᵀ η
⟦ ` α ⟧ᵀ           η = lookupᵀ α η
⟦ ∀α_ {l = l} T ⟧ᵀ η = (A : Set l) → ⟦ T ⟧ᵀ (ext A η)

opaque
  unfolding ext lookupᵀ
  ⊛ᵀ : ∀ {Δ₁ Δ₂} → Ren Δ₁ Δ₂ → Env* Δ₂ → Env* Δ₁
  ⊛ᵀ {∅}       ζ η = tt
  ⊛ᵀ {l ∙ Δ₁}  ζ η = ext (lookupᵀ (here &ᴿ ζ) η) (⊛ᵀ (wkᴿ ⨟ᴿ ζ) η)

  -- PUSH (their `beta-fold` analogue)
  lookupᵀ-⊛ᵀ : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
               lookupᵀ α (⊛ᵀ ζ η) ≡ lookupᵀ (α &ᴿ ζ) η
  lookupᵀ-⊛ᵀ here      ζ η = refl
  lookupᵀ-⊛ᵀ (there α) ζ η = lookupᵀ-⊛ᵀ α (wkᴿ ⨟ᴿ ζ) η

  ⊛ᵀ-wk : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (A : Set l) (η : Env* Δ₂) →
          ⊛ᵀ (ζ ⨟ᴿ wkᴿ) (ext A η) ≡ ⊛ᵀ ζ η
  ⊛ᵀ-wk {Δ₁ = ∅}      ζ A η = refl
  ⊛ᵀ-wk {Δ₁ = l ∙ Δ₁} ζ A η =
    cong (ext (lookupᵀ (here &ᴿ ζ) η)) (⊛ᵀ-wk (wkᴿ ⨟ᴿ ζ) A η)

  -- LIFT, oriented λσ⇑-style: `ext` is pushed INSIDE `⊛ᵀ`.
  -- (The opposite orientation `⊛ᵀ (ζ ↑ᴿ) (ext A η) ↦ ext A (⊛ᵀ ζ η)` is
  --  what round 3c registered, and is what collided with PUSH.)
  ext-⊛ᵀ : ∀ {Δ₁ Δ₂ l} (A : Set l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
           ext A (⊛ᵀ ζ η) ≡ ⊛ᵀ (ζ ↑ᴿ) (ext A η)
  ext-⊛ᵀ A ζ η = cong (ext A) (sym (⊛ᵀ-wk ζ A η))

opaque
  unfolding ext lookupᵀ ⊛ᵀ
  ⟦⟧ᵀ-ren : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
            ⟦ T [ ζ ]ᴿ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊛ᵀ ζ η)
  ⟦⟧ᵀ-ren (base l)  ζ η = refl
  ⟦⟧ᵀ-ren (` α)     ζ η = sym (lookupᵀ-⊛ᵀ α ζ η)
  ⟦⟧ᵀ-ren (T₁ ⇒ T₂) ζ η = cong₂ (λ A B → A → B) (⟦⟧ᵀ-ren T₁ ζ η) (⟦⟧ᵀ-ren T₂ ζ η)
  ⟦⟧ᵀ-ren (∀α_ {l = l} T) ζ η =
    cong (λ f → (A : Set l) → f A)
         (fun-ext λ A → trans (⟦⟧ᵀ-ren T (ζ ↑ᴿ) (ext A η))
                              (cong ⟦ T ⟧ᵀ (sym (ext-⊛ᵀ A ζ η))))

-- STEP 1 of the probe: the four "local" rules only.
{-# REWRITE lookupᵀ-here lookupᵀ-there lookupᵀ-⊛ᵀ ext-⊛ᵀ #-}

-- STEP 2: add the semantic renaming law itself.
{-# REWRITE ⟦⟧ᵀ-ren #-}

-- ── firing probes ──
probe-push : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
             lookupᵀ α (⊛ᵀ ζ η) ≡ lookupᵀ (α &ᴿ ζ) η
probe-push α ζ η = refl

probe-ren-abstract : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
                     ⟦ T [ ζ ]ᴿ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊛ᵀ ζ η)
probe-ren-abstract T ζ η = refl

probe-ren-∀ : ∀ {Δ₁ Δ₂ lα l′} (T : Type (lα ∙ Δ₁) l′) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
              ⟦ (∀α_ {l = lα} T) [ ζ ]ᴿ ⟧ᵀ η
              ≡ ((A : Set lα) → ⟦ T ⟧ᵀ (ext A (⊛ᵀ ζ η)))
probe-ren-∀ T ζ η = refl

-- weakening: `⟦ weaken T ⟧ᵀ (ext A η) ≡ ⟦ T ⟧ᵀ η` requires ⊛ᵀ wkᴿ (ext A η) ≡ η,
-- which is NOT registered here — so this is a CONTROL that must FAIL.
-- probe-weaken : ∀ {Δ l l′} (T : Type Δ l′) (A : Set l) (η : Env* Δ) →
--                ⟦ weaken T ⟧ᵀ (ext A η) ≡ ⟦ T ⟧ᵀ η
-- probe-weaken T A η = refl
