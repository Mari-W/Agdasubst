{-# OPTIONS --rewriting --local-confluence-check #-}
-- ⚠ MEASUREMENT PROBE — NOT PART OF THE DEVELOPMENT ⚠
-- This file is EXPECTED TO FAIL.  `agda SemRewriteProbeG.agda` → exit 42.
-- Round 4: full mirror of strat's set, INWARD orientation, incl. `lkp-lift-ext` ≈ `beta-lift-ren-∙`; 14 rules.
-- Measured: 9 non-joinable pairs + 1 undecidable overlap, all against strat's FOLD rules (compositionalityᴿᴿ/ˢᴿ, beta-fold-ˢᴿ, `beta-lift-fusion).
-- Nothing imports this file.  It exists so that §7 of
-- REPORT-adequacy.md is reproducible.
-- ROUND 4: semantic σ-calculus mirroring strat (INWARD orientation), incl. the `beta-lift-ren-∙` mirror `lkp-lift-ext`.
-- Measured: 9 pairs + 1 undecidable overlap — all against strat's FOLD rules (compositionalityᴿᴿ/ˢᴿ, beta-fold-ˢᴿ, beta-lift-fusion).
-- Evidence for §7 of REPORT-adequacy.md.  Nothing imports it.
-- ⚠ MEASUREMENT PROBE for REPORT-adequacy.md §7 ⚠
-- ROUND 4: the semantic σ-calculus, curated by MIRRORING strat's own
-- rule set rather than inventing one.
--
-- The dictionary (strat's syntactic op  ↦  our semantic op):
--     _∙ˢ_   (cons)                    ↦  ext
--     _&ˢ_   (lookup)                  ↦  lookupᵀ
--     ⟨_⟩ ⨟ˢ _  (renaming action)      ↦  ⊛ᵀ
--     _⨟ˢ_  (substitution action)      ↦  ⊙ᵀ
--
-- Round 3c's residual pair was
--     lookupᵀ α (⊛ᵀ (ζ ↑ᴿ) (ext A η))  ⇉  push / lift-cons
-- and strat resolves the SAME overlap not by dropping either rule but
-- with a third rule at the VARIABLE-LOOKUP level:
--     beta-lift-ren-∙ : (α &ᴿ (ζ ↑ᴿ)) &ˢ (T ∙ˢ η) ≡ α &ˢ (T ∙ˢ (⟨ ζ ⟩ ⨟ˢ η))
-- Its mirror image is `lkp-lift-ext` below.  That is the whole idea of
-- this round: same discipline, one layer up.
module SemRewriteProbeG where

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
  ext : ∀ {Δ l} → Set l → Env* Δ → Env* (l ∙ Δ)
  ext A η = A , η

  lookupᵀ : ∀ {Δ l} → Δ ∋ˡ l → Env* Δ → Set l
  lookupᵀ here      η = fst η
  lookupᵀ (there α) η = lookupᵀ α (snd η)

  -- ≈ beta-ext-zero / beta-ext-suc
  lkp-ext-zero : ∀ {Δ l} (A : Set l) (η : Env* Δ) → lookupᵀ here (ext A η) ≡ A
  lkp-ext-zero A η = refl

  lkp-ext-suc : ∀ {Δ l l′} (α : Δ ∋ˡ l) (A : Set l′) (η : Env* Δ) →
                lookupᵀ (there α) (ext A η) ≡ lookupᵀ α η
  lkp-ext-suc α A η = refl

⟦_⟧ᵀ : ∀ {Δ l} → Type Δ l → Env* Δ → Set l
⟦ base l ⟧ᵀ        η = Lift l Bool
⟦ T₁ ⇒ T₂ ⟧ᵀ       η = ⟦ T₁ ⟧ᵀ η → ⟦ T₂ ⟧ᵀ η
⟦ ` α ⟧ᵀ           η = lookupᵀ α η
⟦ ∀α_ {l = l} T ⟧ᵀ η = (A : Set l) → ⟦ T ⟧ᵀ (ext A η)

-- ══════════════ renaming action ══════════════
opaque
  unfolding ext lookupᵀ
  ⊛ᵀ : ∀ {Δ₁ Δ₂} → Ren Δ₁ Δ₂ → Env* Δ₂ → Env* Δ₁
  ⊛ᵀ {∅}      ζ η = tt
  ⊛ᵀ {l ∙ Δ₁} ζ η = ext (lookupᵀ (here &ᴿ ζ) η) (⊛ᵀ (wkᴿ ⨟ᴿ ζ) η)

  -- ≈ beta-⟨⟩-⨟   (PUSH at the variable)
  lkp-⊛ : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
          lookupᵀ α (⊛ᵀ ζ η) ≡ lookupᵀ (α &ᴿ ζ) η
  lkp-⊛ here      ζ η = refl
  lkp-⊛ (there α) ζ η = lkp-⊛ α (wkᴿ ⨟ᴿ ζ) η

  ⊛ᵀ-wk : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (A : Set l) (η : Env* Δ₂) →
          ⊛ᵀ (ζ ⨟ᴿ wkᴿ) (ext A η) ≡ ⊛ᵀ ζ η
  ⊛ᵀ-wk {Δ₁ = ∅}      ζ A η = refl
  ⊛ᵀ-wk {Δ₁ = l ∙ Δ₁} ζ A η =
    cong (ext (lookupᵀ (here &ᴿ ζ) η)) (⊛ᵀ-wk (wkᴿ ⨟ᴿ ζ) A η)

  -- ≈ lift-cons
  ⊛ᵀ-lift-ext : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (A : Set l) (η : Env* Δ₂) →
                ⊛ᵀ (ζ ↑ᴿ) (ext A η) ≡ ext A (⊛ᵀ ζ η)
  ⊛ᵀ-lift-ext ζ A η = cong (ext A) (⊛ᵀ-wk ζ A η)

  -- ★ ≈ beta-lift-ren-∙ : the rule that JOINS push against lift-cons ★
  lkp-lift-ext : ∀ {Δ₁ Δ₂ l l′} (α : (l′ ∙ Δ₁) ∋ˡ l) (ζ : Ren Δ₁ Δ₂)
                 (A : Set l′) (η : Env* Δ₂) →
                 lookupᵀ (α &ᴿ (ζ ↑ᴿ)) (ext A η) ≡ lookupᵀ α (ext A (⊛ᵀ ζ η))
  lkp-lift-ext here      ζ A η = refl
  lkp-lift-ext (there α) ζ A η = sym (lkp-⊛ α ζ η)

  -- ≈ interact
  ⊛ᵀ-wk-ext : ∀ {Δ l} (A : Set l) (η : Env* Δ) → ⊛ᵀ wkᴿ (ext A η) ≡ η
  ⊛ᵀ-wk-ext {Δ = ∅}     A η       = refl
  ⊛ᵀ-wk-ext {Δ = l ∙ Δ} A (x , η) =
    cong (ext x) (trans (⊛ᵀ-wk wkᴿ A (x , η)) (⊛ᵀ-wk-ext x η))

  -- ≈ comp-idₗ
  ⊛ᵀ-id : ∀ {Δ} (η : Env* Δ) → ⊛ᵀ idᴿ η ≡ η
  ⊛ᵀ-id {∅}     η       = refl
  ⊛ᵀ-id {l ∙ Δ} (x , η) = cong (ext x) (trans (⊛ᵀ-wk idᴿ x η) (⊛ᵀ-id η))

opaque
  unfolding ext lookupᵀ ⊛ᵀ
  ⟦⟧ᵀ-ren : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
            ⟦ T [ ζ ]ᴿ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊛ᵀ ζ η)
  ⟦⟧ᵀ-ren (base l)  ζ η = refl
  ⟦⟧ᵀ-ren (` α)     ζ η = sym (lkp-⊛ α ζ η)
  ⟦⟧ᵀ-ren (T₁ ⇒ T₂) ζ η = cong₂ (λ A B → A → B) (⟦⟧ᵀ-ren T₁ ζ η) (⟦⟧ᵀ-ren T₂ ζ η)
  ⟦⟧ᵀ-ren (∀α_ {l = l} T) ζ η =
    cong (λ f → (A : Set l) → f A)
         (fun-ext λ A → trans (⟦⟧ᵀ-ren T (ζ ↑ᴿ) (ext A η))
                              (cong ⟦ T ⟧ᵀ (⊛ᵀ-lift-ext ζ A η)))

-- ══════════════ substitution action ══════════════
opaque
  unfolding ext lookupᵀ ⊛ᵀ ⟦⟧ᵀ-ren
  ⊙ᵀ : ∀ {Δ₁ Δ₂} → Sub Δ₁ Δ₂ → Env* Δ₂ → Env* Δ₁
  ⊙ᵀ {∅}      σ η = tt
  ⊙ᵀ {l ∙ Δ₁} σ η = ext (⟦ here &ˢ σ ⟧ᵀ η) (⊙ᵀ (⟨ wkᴿ ⟩ ⨟ˢ σ) η)

  -- ≈ beta-fold
  lkp-⊙ : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (σ : Sub Δ₁ Δ₂) (η : Env* Δ₂) →
          lookupᵀ α (⊙ᵀ σ η) ≡ ⟦ α &ˢ σ ⟧ᵀ η
  lkp-⊙ here      σ η = refl
  lkp-⊙ (there α) σ η = lkp-⊙ α (⟨ wkᴿ ⟩ ⨟ˢ σ) η

  -- ≈ coincidence (ˢ → ᴿ, matching strat's orientation)
  ⊙ᵀ-⟨⟩ : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) → ⊙ᵀ ⟨ ζ ⟩ η ≡ ⊛ᵀ ζ η
  ⊙ᵀ-⟨⟩ {Δ₁ = ∅}      ζ η = refl
  ⊙ᵀ-⟨⟩ {Δ₁ = l ∙ Δ₁} ζ η = cong (ext (lookupᵀ (here &ᴿ ζ) η)) (⊙ᵀ-⟨⟩ (wkᴿ ⨟ᴿ ζ) η)

  -- ≈ distributivity
  ⊙ᵀ-cons : ∀ {Δ₁ Δ₂ l} (T : Type Δ₂ l) (σ : Sub Δ₁ Δ₂) (η : Env* Δ₂) →
            ⊙ᵀ (T ∙ˢ σ) η ≡ ext (⟦ T ⟧ᵀ η) (⊙ᵀ σ η)
  ⊙ᵀ-cons T σ η = refl

  ⊙ᵀ-wk : ∀ {Δ₁ Δ₂ l} (σ : Sub Δ₁ Δ₂) (A : Set l) (η : Env* Δ₂) →
          ⊙ᵀ (σ ⨟ˢ ⟨ wkᴿ ⟩) (ext A η) ≡ ⊙ᵀ σ η
  ⊙ᵀ-wk {Δ₁ = ∅}      σ A η = refl
  ⊙ᵀ-wk {Δ₁ = l ∙ Δ₁} σ A η =
    cong₂ ext (trans (⟦⟧ᵀ-ren (here &ˢ σ) wkᴿ (ext A η))
                     (cong ⟦ here &ˢ σ ⟧ᵀ (⊛ᵀ-wk-ext A η)))
              (⊙ᵀ-wk (⟨ wkᴿ ⟩ ⨟ˢ σ) A η)

  -- ≈ lift-cons
  ⊙ᵀ-lift-ext : ∀ {Δ₁ Δ₂ l} (σ : Sub Δ₁ Δ₂) (A : Set l) (η : Env* Δ₂) →
                ⊙ᵀ (σ ↑ˢ) (ext A η) ≡ ext A (⊙ᵀ σ η)
  ⊙ᵀ-lift-ext σ A η = cong (ext A) (⊙ᵀ-wk σ A η)

  -- ★ ≈ beta-lift-ren-∙, substitution version ★
  lkp-lift-ext-ˢ : ∀ {Δ₁ Δ₂ l l′} (α : (l′ ∙ Δ₁) ∋ˡ l) (σ : Sub Δ₁ Δ₂)
                   (A : Set l′) (η : Env* Δ₂) →
                   ⟦ α &ˢ (σ ↑ˢ) ⟧ᵀ (ext A η) ≡ lookupᵀ α (ext A (⊙ᵀ σ η))
  lkp-lift-ext-ˢ here      σ A η = refl
  lkp-lift-ext-ˢ (there α) σ A η =
    trans (trans (⟦⟧ᵀ-ren (α &ˢ σ) wkᴿ (ext A η))
                 (cong ⟦ α &ˢ σ ⟧ᵀ (⊛ᵀ-wk-ext A η)))
          (sym (lkp-⊙ α σ η))

  ⊙ᵀ-id : ∀ {Δ} (η : Env* Δ) → ⊙ᵀ idˢ η ≡ η
  ⊙ᵀ-id η = trans (⊙ᵀ-⟨⟩ idᴿ η) (⊛ᵀ-id η)

opaque
  unfolding ext lookupᵀ ⊛ᵀ ⊙ᵀ ⟦⟧ᵀ-ren
  ⟦⟧ᵀ-sub : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (σ : Sub Δ₁ Δ₂) (η : Env* Δ₂) →
            ⟦ T [ σ ]ˢ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊙ᵀ σ η)
  ⟦⟧ᵀ-sub (base l)  σ η = refl
  ⟦⟧ᵀ-sub (` α)     σ η = sym (lkp-⊙ α σ η)
  ⟦⟧ᵀ-sub (T₁ ⇒ T₂) σ η = cong₂ (λ A B → A → B) (⟦⟧ᵀ-sub T₁ σ η) (⟦⟧ᵀ-sub T₂ σ η)
  ⟦⟧ᵀ-sub (∀α_ {l = l} T) σ η =
    cong (λ f → (A : Set l) → f A)
         (fun-ext λ A → trans (⟦⟧ᵀ-sub T (σ ↑ˢ) (ext A η))
                              (cong ⟦ T ⟧ᵀ (⊙ᵀ-lift-ext σ A η)))

-- ══════════════ REGISTRATION: both halves TOGETHER ══════════════
{-# REWRITE
  lkp-ext-zero lkp-ext-suc
  lkp-⊛ lkp-lift-ext ⊛ᵀ-lift-ext ⊛ᵀ-wk-ext ⊛ᵀ-id ⟦⟧ᵀ-ren
  lkp-⊙ lkp-lift-ext-ˢ ⊙ᵀ-⟨⟩ ⊙ᵀ-lift-ext ⊙ᵀ-id ⟦⟧ᵀ-sub
#-}

-- ══════════════ FIRING PROBES ══════════════
probe-ren : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
            ⟦ T [ ζ ]ᴿ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊛ᵀ ζ η)
probe-ren T ζ η = refl

probe-sub : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (σ : Sub Δ₁ Δ₂) (η : Env* Δ₂) →
            ⟦ T [ σ ]ˢ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊙ᵀ σ η)
probe-sub T σ η = refl

probe-sub-∀ : ∀ {Δ₁ Δ₂ lα l′} (T : Type (lα ∙ Δ₁) l′) (σ : Sub Δ₁ Δ₂) (η : Env* Δ₂) →
              ⟦ (∀α_ {l = lα} T) [ σ ]ˢ ⟧ᵀ η ≡ ((A : Set lα) → ⟦ T ⟧ᵀ (ext A (⊙ᵀ σ η)))
probe-sub-∀ T σ η = refl

-- the three the adequacy development actually needs
probe-weaken : ∀ {Δ l l′} (T : Type Δ l′) (A : Set l) (η : Env* Δ) →
               ⟦ weaken T ⟧ᵀ (ext A η) ≡ ⟦ T ⟧ᵀ η
probe-weaken T A η = refl

probe-single : ∀ {Δ l l′} (T : Type (l ∙ Δ) l′) (T′ : Type Δ l) (η : Env* Δ) →
               ⟦ T [ T′ ]* ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (ext (⟦ T′ ⟧ᵀ η) η)
probe-single T T′ η = refl

probe-closing : ∀ {Δ l} (T : Type Δ l) (σ : Sub Δ ∅) →
                ⟦ T [ σ ]ˢ ⟧ᵀ tt ≡ ⟦ T ⟧ᵀ (⊙ᵀ σ tt)
probe-closing T σ = refl
