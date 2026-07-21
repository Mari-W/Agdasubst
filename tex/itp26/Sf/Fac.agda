{-# OPTIONS --rewriting --local-confluence-check #-}
-- Sf.Fac — the cover/coproduct completion for the OPAQUE thinL/thinR, plus the
-- coproduct INJECTION-FACTORISATION laws (the triangle of `cop`).  Together these
-- make the thinned typed smart-app `⊢app↑` definitional in the full-context typing
-- scheme: no context restriction — just thinning composition.
module Sf.Fac (I : Set) where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite
open import Sf.Thin I

opaque
  unfolding cop thinL thinR _⨾_ oi covL covR full
  -- cover-thinning completion (closes the cop-unit critical pairs with Fac)
  thinL-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ) → thinL (covL φ) ≡ oi
  thinL-covL oz     = refl
  thinL-covL (os φ) = cong os (thinL-covL φ)
  thinL-covL (o' φ) = cong os (thinL-covL φ)
  thinR-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ) → thinR (covL φ) ≡ φ
  thinR-covL oz     = refl
  thinR-covL (os φ) = cong os (thinR-covL φ)
  thinR-covL (o' φ) = cong o' (thinR-covL φ)
  thinL-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ) → thinL (covR θ) ≡ θ
  thinL-covR oz     = refl
  thinL-covR (os θ) = cong os (thinL-covR θ)
  thinL-covR (o' θ) = cong o' (thinL-covR θ)
  thinR-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ) → thinR (covR θ) ≡ oi
  thinR-covR oz     = refl
  thinR-covR (os θ) = cong os (thinR-covR θ)
  thinR-covR (o' θ) = cong os (thinR-covR θ)
  thinL-full : ∀ {Γ} → thinL (full {Γ}) ≡ oi
  thinL-full {[]}    = refl
  thinL-full {_ ∷ Γ} = cong os thinL-full
  thinR-full : ∀ {Γ} → thinR (full {Γ}) ≡ oi
  thinR-full {[]}    = refl
  thinR-full {_ ∷ Γ} = cong os thinR-full
{-# REWRITE thinL-covL thinR-covL thinL-covR thinR-covR thinL-full thinR-full #-}

opaque
  unfolding cop thinL thinR _⨾_ oi
  Fac-L : ∀ {Γ₁ Γ₂ Δ}(θ : Γ₁ ⊑ Δ)(φ : Γ₂ ⊑ Δ) → thinL (cov (cop θ φ)) ⨾ out (cop θ φ) ≡ θ
  Fac-L oz     oz     = refl
  Fac-L (os θ) (os φ) = cong os (Fac-L θ φ)
  Fac-L (os θ) (o' φ) = cong os (Fac-L θ φ)
  Fac-L (o' θ) (os φ) = cong o' (Fac-L θ φ)
  Fac-L (o' θ) (o' φ) = cong o' (Fac-L θ φ)
  Fac-R : ∀ {Γ₁ Γ₂ Δ}(θ : Γ₁ ⊑ Δ)(φ : Γ₂ ⊑ Δ) → thinR (cov (cop θ φ)) ⨾ out (cop θ φ) ≡ φ
  Fac-R oz     oz     = refl
  Fac-R (os θ) (os φ) = cong os (Fac-R θ φ)
  Fac-R (os θ) (o' φ) = cong o' (Fac-R θ φ)
  Fac-R (o' θ) (os φ) = cong os (Fac-R θ φ)
  Fac-R (o' θ) (o' φ) = cong o' (Fac-R θ φ)
  -- post-composed forms (close the ⨾-associativity critical pairs)
  Fac-L⨾ : ∀ {Γ₁ Γ₂ Δ Θ}(θ : Γ₁ ⊑ Δ)(φ : Γ₂ ⊑ Δ)(ψ : Δ ⊑ Θ)
         → thinL (cov (cop θ φ)) ⨾ (out (cop θ φ) ⨾ ψ) ≡ θ ⨾ ψ
  Fac-L⨾ θ φ ψ = cong (_⨾ ψ) (Fac-L θ φ)
  Fac-R⨾ : ∀ {Γ₁ Γ₂ Δ Θ}(θ : Γ₁ ⊑ Δ)(φ : Γ₂ ⊑ Δ)(ψ : Δ ⊑ Θ)
         → thinR (cov (cop θ φ)) ⨾ (out (cop θ φ) ⨾ ψ) ≡ φ ⨾ ψ
  Fac-R⨾ θ φ ψ = cong (_⨾ ψ) (Fac-R θ φ)
{-# REWRITE Fac-L Fac-R Fac-L⨾ Fac-R⨾ #-}
