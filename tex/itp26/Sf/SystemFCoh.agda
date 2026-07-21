{-# OPTIONS --rewriting --local-confluence-check #-}
-- Sf.SystemFCoh — the SUBSTITUTION coherence for System F, registered as rewrites.
-- `selL-cop`/`selR-cop` (the Sub analog of the context coherence cohL/cohR) say that
-- splitting a restricted substitution along the merged cover = restricting per-side.
-- Registrable because `cop` is opaque, so `cov (cop θ φ)` is a stable rewrite head —
-- the same trick `Fac` uses for `thinL`.  The `cop`-unit completion (selL/selR on
-- covL/covR/full, and `↾ oi`) closes the critical pairs.  With these, substitution
-- distributes over every type/term former DEFINITIONALLY.
module Sf.SystemFCoh where
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Sf.SystemF
open import Sf.SystemF
open import Sf.Fac Sort
opaque
  unfolding covL covR full oi
  selL-covL : ∀ {Γ Δ Θ}(φ : Γ ⊑ Δ)(τ : Sub Θ Δ) → selL (covL φ) τ ≡ τ
  selL-covL oz [] = refl
  selL-covL (os φ) (τ ,- u) = cong (_,- u) (selL-covL φ τ)
  selL-covL (o' φ) (τ ,- u) = cong (_,- u) (selL-covL φ τ)
  selR-covL : ∀ {Γ Δ Θ}(φ : Γ ⊑ Δ)(τ : Sub Θ Δ) → selR (covL φ) τ ≡ τ ↾ φ
  selR-covL oz [] = refl
  selR-covL (os φ) (τ ,- u) = cong (_,- u) (selR-covL φ τ)
  selR-covL (o' φ) (τ ,- u) = selR-covL φ τ
  selL-covR : ∀ {Γ Δ Θ}(θ : Γ ⊑ Δ)(τ : Sub Θ Δ) → selL (covR θ) τ ≡ τ ↾ θ
  selL-covR oz [] = refl
  selL-covR (os θ) (τ ,- u) = cong (_,- u) (selL-covR θ τ)
  selL-covR (o' θ) (τ ,- u) = selL-covR θ τ
  selR-covR : ∀ {Γ Δ Θ}(θ : Γ ⊑ Δ)(τ : Sub Θ Δ) → selR (covR θ) τ ≡ τ
  selR-covR oz [] = refl
  selR-covR (os θ) (τ ,- u) = cong (_,- u) (selR-covR θ τ)
  selR-covR (o' θ) (τ ,- u) = cong (_,- u) (selR-covR θ τ)
  selL-full : ∀ {Γ Θ}(τ : Sub Θ Γ) → selL (full {Γ}) τ ≡ τ
  selL-full {[]} [] = refl
  selL-full {_ ∷ Γ} (τ ,- u) = cong (_,- u) (selL-full τ)
  selR-full : ∀ {Γ Θ}(τ : Sub Θ Γ) → selR (full {Γ}) τ ≡ τ
  selR-full {[]} [] = refl
  selR-full {_ ∷ Γ} (τ ,- u) = cong (_,- u) (selR-full τ)
  ↾-oi : ∀ {Δ Θ}(τ : Sub Θ Δ) → τ ↾ oi ≡ τ
  ↾-oi {[]} [] = refl
  ↾-oi {_ ∷ Δ} (τ ,- u) = cong (_,- u) (↾-oi τ)
{-# REWRITE selL-covL selR-covL selL-covR selR-covR selL-full selR-full ↾-oi selL-cop selR-cop #-}
