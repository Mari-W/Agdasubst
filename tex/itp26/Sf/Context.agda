{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.Context — LANGUAGE-INDEPENDENT context machinery for co-de-Bruijn typing.
--
-- A context `Cx Γ` carries one CLASSIFIER (`Ent : Scope → I → Set`) per support
-- variable of Γ.  Restriction `rest θ` keeps the variables picked out by a
-- thinning; the cover-split `splitL/splitR` is DEFINED as `rest ∘ thinL/thinR`,
-- so the "split = restrict" coherences are refl.  The cop/context coherences
-- cohL/cohR and rest-oe are proven here and registered as REWRITES — closing
-- exactly the critical pairs with the cover/coproduct completion in Sf.Thin.
--
-- Generic over the classifier `Ent`, so STLC's simple types and System F's
-- (type-indexed) contexts both reuse this.  For a non-dependent classifier the
-- entry ignores the sort; that is the STLC instance.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.Context (I : Set)(Ent : I → Set) where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite
open import Sf.Scaffold I

-- a context: one CLOSED classifier `Ent s` per s-variable of the support.
-- (System F's type-indexed contexts will need a Γ-dependent generalisation of
-- this module; for STLC the classifier is a closed simple type.)
data Cx : Scope → Set where
  ε    : Cx []
  _,-_ : ∀ {s Γ} → Cx Γ → Ent s → Cx (s ∷ Γ)
infixl 5 _,-_

-- restrict a context to the support picked out by a thinning
rest : ∀ {sup Δ} → sup ⊑ Δ → Cx Δ → Cx sup
rest oz     ε        = ε
rest (os θ) (Φ ,- A) = rest θ Φ ,- A
rest (o' θ) (Φ ,- A) = rest θ Φ

-- cover → its two embedding thinnings.  TRANSPARENT here (the typing layer wants
-- `splitL` to compute); this is a distinct copy from Sf.Thin's opaque `thinL`,
-- which must stay opaque to carry the cover-thinning COMPLETION rewrites.
thL : ∀ {sₗ sᵣ Γ} → Cover sₗ sᵣ Γ → sₗ ⊑ Γ
thL czz = oz ; thL (css c) = os (thL c) ; thL (cs' c) = os (thL c) ; thL (c's c) = o' (thL c)
thR : ∀ {sₗ sᵣ Γ} → Cover sₗ sᵣ Γ → sᵣ ⊑ Γ
thR czz = oz ; thR (css c) = os (thR c) ; thR (cs' c) = o' (thR c) ; thR (c's c) = os (thR c)

-- a context split is DEFINED as restriction along the cover-thinning, so the
-- "rest = split" coherences are refl, and (thL transparent) splitL COMPUTES.
splitL : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Cx Γ → Cx Γₗ
splitL cv Φ = rest (thL cv) Φ
splitR : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Cx Γ → Cx Γᵣ
splitR cv Φ = rest (thR cv) Φ

-- ── CONTEXT-COHERENCE rewrites ──
-- rest oi Ψ = Ψ  (LHS stuck outside since oi is opaque ⇒ sound rewrite)
opaque
  unfolding oi
  rest-oi : ∀ {Δ}(Ψ : Cx Δ) → rest oi Ψ ≡ Ψ
  rest-oi ε        = refl
  rest-oi (Ψ ,- A) = cong (_,- A) (rest-oi Ψ)
{-# REWRITE rest-oi #-}

-- COVER-THINNING completion (for the transparent `thL`/`thR`): closes the
-- cohL/cohR critical pairs against cop's unit laws cop-oiL/cop-oiR.  Each LHS is
-- stuck outside (covL/covR/full/oi opaque), so registration is sound.
opaque
  unfolding oi covL covR full
  thL-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ) → thL (covL φ) ≡ oi
  thL-covL oz = refl ; thL-covL (os φ) = cong os (thL-covL φ) ; thL-covL (o' φ) = cong os (thL-covL φ)
  thR-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ) → thR (covL φ) ≡ φ
  thR-covL oz = refl ; thR-covL (os φ) = cong os (thR-covL φ) ; thR-covL (o' φ) = cong o' (thR-covL φ)
  thL-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ) → thL (covR θ) ≡ θ
  thL-covR oz = refl ; thL-covR (os θ) = cong os (thL-covR θ) ; thL-covR (o' θ) = cong o' (thL-covR θ)
  thR-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ) → thR (covR θ) ≡ oi
  thR-covR oz = refl ; thR-covR (os θ) = cong os (thR-covR θ) ; thR-covR (o' θ) = cong os (thR-covR θ)
  thL-full : ∀ {Γ} → thL (full {Γ}) ≡ oi
  thL-full {[]} = refl ; thL-full {_ ∷ Γ} = cong os thL-full
  thR-full : ∀ {Γ} → thR (full {Γ}) ≡ oi
  thR-full {[]} = refl ; thR-full {_ ∷ Γ} = cong os thR-full
-- ── REWRITE GROUP: COVER-THINNING completion ──
{-# REWRITE thL-covL thR-covL thL-covR thR-covR thL-full thR-full #-}

-- the cop/context coherence (McBride §6): the cover-split of the merged context
-- is the per-side restriction.  Stated on the UNFOLDED rest∘thL form (splitL
-- unfolds eagerly).  The completion above closes their pairs with cop-oiL/R.
opaque
  unfolding cop
  cohL : ∀ {sₗ sᵣ Δ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(Ψ : Cx Δ)
       → rest (thL (cov (cop θ φ))) (rest (out (cop θ φ)) Ψ) ≡ rest θ Ψ
  cohL oz     oz     ε        = refl
  cohL (os θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohL θ φ Ψ)
  cohL (os θ) (o' φ) (Ψ ,- A) = cong (_,- A) (cohL θ φ Ψ)
  cohL (o' θ) (os φ) (Ψ ,- A) = cohL θ φ Ψ
  cohL (o' θ) (o' φ) (Ψ ,- A) = cohL θ φ Ψ
  cohR : ∀ {sₗ sᵣ Δ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(Ψ : Cx Δ)
       → rest (thR (cov (cop θ φ))) (rest (out (cop θ φ)) Ψ) ≡ rest φ Ψ
  cohR oz     oz     ε        = refl
  cohR (os θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohR θ φ Ψ)
  cohR (os θ) (o' φ) (Ψ ,- A) = cohR θ φ Ψ
  cohR (o' θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohR θ φ Ψ)
  cohR (o' θ) (o' φ) (Ψ ,- A) = cohR θ φ Ψ
{-# REWRITE cohL cohR #-}

-- restricting any context by the empty thinning yields ε.  (oe opaque outside ⇒
-- no `oe → o' oe` competing redex ⇒ sound rewrite.)
opaque
  unfolding oe
  rest-oe : ∀ {Δ}(Ψ : Cx Δ) → rest oe Ψ ≡ ε
  rest-oe ε        = refl
  rest-oe (Ψ ,- A) = rest-oe Ψ
{-# REWRITE rest-oe #-}

-- REST FUNCTORIALITY:  rest (ψ ⨾ θ) Φ ≡ rest ψ (rest θ Φ).  Needed for the CBV
-- congruence cases (a reduced subterm re-embedded along the cover-thinning lands
-- back in the IH's context).  Stated unfolding _⨾_ to recurse; the LHS `ψ ⨾ θ`
-- is a redex of the THINNING MONOID, but the os/o' clauses keep it confluent.
opaque
  unfolding _⨾_
  rest-⨾ : ∀ {sup Δ Δ′}(ψ : sup ⊑ Δ)(θ : Δ ⊑ Δ′)(Φ : Cx Δ′) → rest (ψ ⨾ θ) Φ ≡ rest ψ (rest θ Φ)
  rest-⨾ ψ      oz     ε        = refl
  rest-⨾ (os ψ) (os θ) (Φ ,- A) = cong (_,- A) (rest-⨾ ψ θ Φ)
  rest-⨾ (o' ψ) (os θ) (Φ ,- A) = rest-⨾ ψ θ Φ
  rest-⨾ ψ      (o' θ) (Φ ,- A) = rest-⨾ ψ θ Φ
{-# REWRITE rest-⨾ #-}
