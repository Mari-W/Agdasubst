{-# OPTIONS --rewriting --local-confluence-check #-}
-- ⚠ MEASUREMENT PROBE — NOT PART OF THE DEVELOPMENT ⚠
-- This file is EXPECTED TO FAIL.  `agda SemRewriteProbeN.agda` → exit 42.
-- Round 3c: round 3b + `no-eta-equality` (+ `pattern`) on the environment carrier.
-- Measured: 1 non-joinable pair — the 2 η-caused pairs of round 3b are GONE; the survivor is the λσ⇑ push/lift overlap, not an η problem.
-- Nothing imports this file.  It exists so that §7 of
-- REPORT-adequacy.md is reproducible.
-- ROUND 3c: exactly ROUND 3b (SemRewriteProbeO2.agda), but with the
-- semantic environment built from a `no-eta-equality` record instead of
-- stdlib `_×_`.
--
-- Round 3b measured 3 non-joinable pairs and I attributed all three to
-- record η-expansion (Agda printed `⊛ᵀ ζ η .proj₁`).  `no-eta-equality`
-- disables exactly that.  `Pair` is PARAMETERISED, not indexed, so the
-- sort still computes and no inductive family is needed.
--
-- This file isolates the question: which of the 3 pairs were caused by
-- η, and which were not?
module SemRewriteProbeN where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool)
open import Level using (Lift; lift; lower)
open import Function using (id)

open import SystemF-strat hiding (fundamental)

-- ── the η-free product ──
record Pair {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  no-eta-equality
  -- `pattern` is REQUIRED: disabling η also disables pattern matching on
  -- the record by default.  Without it we would be measuring the cost of
  -- losing pattern matching, not the cost of losing η.
  pattern
  constructor _,_
  field
    fst : A
    snd : B
open Pair public

-- ── semantic environments over it ──
Env* : (Δ : LCtx) → Set (maxL Δ)
Env* ∅       = ⊤
Env* (l ∙ Δ) = Pair (Set l) (Env* Δ)

opaque
  lookupᵀ : ∀ {Δ l} → Δ ∋ˡ l → Env* Δ → Set l
  lookupᵀ here      η = fst η
  lookupᵀ (there α) η = lookupᵀ α (snd η)

  lookupᵀ-here : ∀ {Δ l} (A : Set l) (η : Env* Δ) → lookupᵀ here (A , η) ≡ A
  lookupᵀ-here A η = refl

  lookupᵀ-there : ∀ {Δ l l′} (α : Δ ∋ˡ l) (A : Set l′) (η : Env* Δ) →
                  lookupᵀ (there α) (A , η) ≡ lookupᵀ α η
  lookupᵀ-there α A η = refl

⟦_⟧ᵀ : ∀ {Δ l} → Type Δ l → Env* Δ → Set l
⟦ base l ⟧ᵀ        η = Lift l Bool
⟦ T₁ ⇒ T₂ ⟧ᵀ       η = ⟦ T₁ ⟧ᵀ η → ⟦ T₂ ⟧ᵀ η
⟦ ` α ⟧ᵀ           η = lookupᵀ α η
⟦ ∀α_ {l = l} T ⟧ᵀ η = (A : Set l) → ⟦ T ⟧ᵀ (A , η)

opaque
  unfolding lookupᵀ
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

  -- COST OF LOSING η (1/2): `η` must be MATCHED, because
  -- `(fst η , snd η) ≡ η` no longer holds definitionally.
  ⊛ᵀ-wk₀ : ∀ {Δ l} (A : Set l) (η : Env* Δ) → ⊛ᵀ wkᴿ (A , η) ≡ η
  ⊛ᵀ-wk₀ {Δ = ∅}     A η       = refl
  ⊛ᵀ-wk₀ {Δ = l ∙ Δ} A (x , η) =
    cong (x ,_) (trans (⊛ᵀ-wk wkᴿ A (x , η)) (⊛ᵀ-wk₀ x η))

  -- COST OF LOSING η (2/2)
  ⊛ᵀ-id : ∀ {Δ} (η : Env* Δ) → ⊛ᵀ idᴿ η ≡ η
  ⊛ᵀ-id {∅}     η       = refl
  ⊛ᵀ-id {l ∙ Δ} (x , η) = cong (x ,_) (trans (⊛ᵀ-wk idᴿ x η) (⊛ᵀ-id η))

-- ISOLATION RUN: same six rules as round 3b.
{-# REWRITE lookupᵀ-here lookupᵀ-there lookupᵀ-⊛ᵀ ⊛ᵀ-lift ⊛ᵀ-wk₀ ⊛ᵀ-id #-}

probe-lookup : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
               lookupᵀ α (⊛ᵀ ζ η) ≡ lookupᵀ (α &ᴿ ζ) η
probe-lookup α ζ η = refl
