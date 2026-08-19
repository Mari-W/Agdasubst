{-# OPTIONS --rewriting --local-confluence-check #-}
-- ⚠ MEASUREMENT PROBE — NOT PART OF THE DEVELOPMENT ⚠
-- This file is EXPECTED TO FAIL.  `agda SemRewriteProbeI.agda` → exit 42.
-- Round 6: configuration FIXED at round 4's; per-pair completion begins; + ⊛ᵀ-assoc, ⊙ᵀ-assoc, lkp-⊙ refolded; 16 rules.
-- Measured: 27 non-joinable pairs — adding associativity exposes strat's whole `-⨟` companion family at once.
-- Nothing imports this file.  It exists so that §7 of
-- REPORT-adequacy.md is reproducible.
-- ROUND 6: per-pair completion, INWARD orientation fixed; +⊛ᵀ-assoc, ⊙ᵀ-assoc, lkp-⊙ refolded.
-- Measured: 27 pairs — assoc exposes strat's whole -⨟ companion family.
-- Evidence for §7 of REPORT-adequacy.md.  Nothing imports it.
-- ⚠ MEASUREMENT PROBE for REPORT-adequacy.md §7 ⚠
-- ROUND 6.  Configuration FIXED at round 4's (INWARD orientation).
-- No orientation swapping.  Round 4's residual pairs were enumerated
-- individually and each was closed by copying strat's syntactic closer:
--
--   P1  lkp-lift-ext  vs `beta-lift-fusion   → ⊛ᵀ-assoc   (≈ `associativity)
--   P2  ⟦⟧ᵀ-ren       vs compositionalityᴿᴿ  → ⊛ᵀ-assoc
--   P3  ⟦⟧ᵀ-ren       vs compositionalityˢᴿ  → ⊙ᵀ-assoc + ⊙ᵀ-⟨⟩
--   P4  ⟦⟧ᵀ-ren       vs beta-fold-ˢᴿ        → reorient lkp-⊙ to FOLD
--   P5  lkp-⊙         vs lkp-⊛ (undecidable) → dissolves once lkp-⊙ folds
--   P6  lkp-lift-ext-ˢ vs beta-lift-ren-↑    → ⊙ᵀ-assoc + ⊙ᵀ-⟨⟩
--   P7  lkp-lift-ext-ˢ vs beta-lift-suc      → ⊛ᵀ-interact (≈ `interact)
--   P8  ⟦⟧ᵀ-sub       vs compositionalityᴿˢ  → ⊙ᵀ-assoc + ⊙ᵀ-⟨⟩
--   P9  ⟦⟧ᵀ-sub       vs compositionalityˢˢ  → ⊙ᵀ-assoc  (≈ associativity)
--   P10 ⟦⟧ᵀ-sub       vs beta-fold           → ⊙ᵀ-assoc + folded lkp-⊙
--   P11 probe-single failed                  → ⊙ᵀ-cons   (≈ distributivity)
--
-- NB strat's own set is not uniform either: it PUSHES at a variable for
-- renamings, FOLDS for substitutions, and carries shape-specific
-- interaction rules.  We copy that, mixed shapes and all.
module SemRewriteProbeI where

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

  -- PUSH at the variable (≈ `beta-comp)
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

  -- ≈ beta-lift-ren-∙
  lkp-lift-ext : ∀ {Δ₁ Δ₂ l l′} (α : (l′ ∙ Δ₁) ∋ˡ l) (ζ : Ren Δ₁ Δ₂)
                 (A : Set l′) (η : Env* Δ₂) →
                 lookupᵀ (α &ᴿ (ζ ↑ᴿ)) (ext A η) ≡ lookupᵀ α (ext A (⊛ᵀ ζ η))
  lkp-lift-ext here      ζ A η = refl
  lkp-lift-ext (there α) ζ A η = sym (lkp-⊛ α ζ η)

  -- ★ CLOSER for P7 — ≈ `interact.  Also exactly `probe-weaken`'s need.
  ⊛ᵀ-interact : ∀ {Δ l} (A : Set l) (η : Env* Δ) → ⊛ᵀ wkᴿ (ext A η) ≡ η
  ⊛ᵀ-interact {Δ = ∅}     A η       = refl
  ⊛ᵀ-interact {Δ = l ∙ Δ} A (x , η) =
    cong (ext x) (trans (⊛ᵀ-wk wkᴿ A (x , η)) (⊛ᵀ-interact x η))

  ⊛ᵀ-id : ∀ {Δ} (η : Env* Δ) → ⊛ᵀ idᴿ η ≡ η
  ⊛ᵀ-id {∅}     η       = refl
  ⊛ᵀ-id {l ∙ Δ} (x , η) = cong (ext x) (trans (⊛ᵀ-wk idᴿ x η) (⊛ᵀ-id η))

  -- ★ CLOSER for P1, P2 — ≈ `associativity (UNFOLD, right-associating)
  ⊛ᵀ-assoc : ∀ {Δ₁ Δ₂ Δ₃} (ζ₁ : Ren Δ₁ Δ₂) (ζ₂ : Ren Δ₂ Δ₃) (η : Env* Δ₃) →
             ⊛ᵀ (ζ₁ ⨟ᴿ ζ₂) η ≡ ⊛ᵀ ζ₁ (⊛ᵀ ζ₂ η)
  ⊛ᵀ-assoc {Δ₁ = ∅}      ζ₁ ζ₂ η = refl
  ⊛ᵀ-assoc {Δ₁ = l ∙ Δ₁} ζ₁ ζ₂ η =
    cong₂ ext (sym (lkp-⊛ (here &ᴿ ζ₁) ζ₂ η)) (⊛ᵀ-assoc (wkᴿ ⨟ᴿ ζ₁) ζ₂ η)

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

  -- ★ P4/P5/P10: FOLD, not push.  (strat folds for substitutions.)
  lkp-⊙ : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (σ : Sub Δ₁ Δ₂) (η : Env* Δ₂) →
          ⟦ α &ˢ σ ⟧ᵀ η ≡ lookupᵀ α (⊙ᵀ σ η)
  lkp-⊙ here      σ η = refl
  lkp-⊙ (there α) σ η = lkp-⊙ α (⟨ wkᴿ ⟩ ⨟ˢ σ) η

  -- ≈ coincidence
  ⊙ᵀ-⟨⟩ : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) → ⊙ᵀ ⟨ ζ ⟩ η ≡ ⊛ᵀ ζ η
  ⊙ᵀ-⟨⟩ {Δ₁ = ∅}      ζ η = refl
  ⊙ᵀ-⟨⟩ {Δ₁ = l ∙ Δ₁} ζ η = cong (ext (lookupᵀ (here &ᴿ ζ) η)) (⊙ᵀ-⟨⟩ (wkᴿ ⨟ᴿ ζ) η)

  -- ★ CLOSER for P11 — ≈ distributivity
  ⊙ᵀ-cons : ∀ {Δ₁ Δ₂ l} (T : Type Δ₂ l) (σ : Sub Δ₁ Δ₂) (η : Env* Δ₂) →
            ⊙ᵀ (T ∙ˢ σ) η ≡ ext (⟦ T ⟧ᵀ η) (⊙ᵀ σ η)
  ⊙ᵀ-cons T σ η = refl

  ⊙ᵀ-wk : ∀ {Δ₁ Δ₂ l} (σ : Sub Δ₁ Δ₂) (A : Set l) (η : Env* Δ₂) →
          ⊙ᵀ (σ ⨟ˢ ⟨ wkᴿ ⟩) (ext A η) ≡ ⊙ᵀ σ η
  ⊙ᵀ-wk {Δ₁ = ∅}      σ A η = refl
  ⊙ᵀ-wk {Δ₁ = l ∙ Δ₁} σ A η =
    cong₂ ext (trans (⟦⟧ᵀ-ren (here &ˢ σ) wkᴿ (ext A η))
                     (cong ⟦ here &ˢ σ ⟧ᵀ (⊛ᵀ-interact A η)))
              (⊙ᵀ-wk (⟨ wkᴿ ⟩ ⨟ˢ σ) A η)

  ⊙ᵀ-lift-ext : ∀ {Δ₁ Δ₂ l} (σ : Sub Δ₁ Δ₂) (A : Set l) (η : Env* Δ₂) →
                ⊙ᵀ (σ ↑ˢ) (ext A η) ≡ ext A (⊙ᵀ σ η)
  ⊙ᵀ-lift-ext σ A η = cong (ext A) (⊙ᵀ-wk σ A η)

  ⊙ᵀ-id : ∀ {Δ} (η : Env* Δ) → ⊙ᵀ idˢ η ≡ η
  ⊙ᵀ-id η = trans (⊙ᵀ-⟨⟩ idᴿ η) (⊛ᵀ-id η)

opaque
  unfolding ext lookupᵀ ⊛ᵀ ⊙ᵀ ⟦⟧ᵀ-ren
  ⟦⟧ᵀ-sub : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (σ : Sub Δ₁ Δ₂) (η : Env* Δ₂) →
            ⟦ T [ σ ]ˢ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊙ᵀ σ η)
  ⟦⟧ᵀ-sub (base l)  σ η = refl
  ⟦⟧ᵀ-sub (` α)     σ η = lkp-⊙ α σ η
  ⟦⟧ᵀ-sub (T₁ ⇒ T₂) σ η = cong₂ (λ A B → A → B) (⟦⟧ᵀ-sub T₁ σ η) (⟦⟧ᵀ-sub T₂ σ η)
  ⟦⟧ᵀ-sub (∀α_ {l = l} T) σ η =
    cong (λ f → (A : Set l) → f A)
         (fun-ext λ A → trans (⟦⟧ᵀ-sub T (σ ↑ˢ) (ext A η))
                              (cong ⟦ T ⟧ᵀ (⊙ᵀ-lift-ext σ A η)))

opaque
  unfolding ext lookupᵀ ⊛ᵀ ⊙ᵀ ⟦⟧ᵀ-ren ⟦⟧ᵀ-sub
  -- ★ CLOSER for P3, P6, P8, P9, P10 — ≈ associativity (UNFOLD)
  ⊙ᵀ-assoc : ∀ {Δ₁ Δ₂ Δ₃} (σ₁ : Sub Δ₁ Δ₂) (σ₂ : Sub Δ₂ Δ₃) (η : Env* Δ₃) →
             ⊙ᵀ (σ₁ ⨟ˢ σ₂) η ≡ ⊙ᵀ σ₁ (⊙ᵀ σ₂ η)
  ⊙ᵀ-assoc {Δ₁ = ∅}      σ₁ σ₂ η = refl
  ⊙ᵀ-assoc {Δ₁ = l ∙ Δ₁} σ₁ σ₂ η =
    cong₂ ext (⟦⟧ᵀ-sub (here &ˢ σ₁) σ₂ η) (⊙ᵀ-assoc (⟨ wkᴿ ⟩ ⨟ˢ σ₁) σ₂ η)

{-# REWRITE
  lkp-ext-zero lkp-ext-suc
  lkp-⊛ lkp-lift-ext ⊛ᵀ-lift-ext ⊛ᵀ-interact ⊛ᵀ-id ⊛ᵀ-assoc ⟦⟧ᵀ-ren
  lkp-⊙ ⊙ᵀ-⟨⟩ ⊙ᵀ-cons ⊙ᵀ-lift-ext ⊙ᵀ-id ⊙ᵀ-assoc ⟦⟧ᵀ-sub
#-}

-- ══════════════ FIRING PROBES ══════════════
-- the three the adequacy development needs
probe-weaken : ∀ {Δ l l′} (T : Type Δ l′) (A : Set l) (η : Env* Δ) →
               ⟦ weaken T ⟧ᵀ (ext A η) ≡ ⟦ T ⟧ᵀ η
probe-weaken T A η = refl

probe-single : ∀ {Δ l l′} (T : Type (l ∙ Δ) l′) (T′ : Type Δ l) (η : Env* Δ) →
               ⟦ T [ T′ ]* ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (ext (⟦ T′ ⟧ᵀ η) η)
probe-single T T′ η = refl

probe-closing : ∀ {Δ l} (T : Type Δ l) (σ : Sub Δ ∅) →
                ⟦ T [ σ ]ˢ ⟧ᵀ tt ≡ ⟦ T ⟧ᵀ (⊙ᵀ σ tt)
probe-closing T σ = refl

probe-ren : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Env* Δ₂) →
            ⟦ T [ ζ ]ᴿ ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⊛ᵀ ζ η)
probe-ren T ζ η = refl

probe-sub-∀ : ∀ {Δ₁ Δ₂ lα l′} (T : Type (lα ∙ Δ₁) l′) (σ : Sub Δ₁ Δ₂) (η : Env* Δ₂) →
              ⟦ (∀α_ {l = lα} T) [ σ ]ˢ ⟧ᵀ η ≡ ((A : Set lα) → ⟦ T ⟧ᵀ (ext A (⊙ᵀ σ η)))
probe-sub-∀ T σ η = refl
