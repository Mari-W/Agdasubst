{-# OPTIONS --rewriting --local-confluence-check #-}
-- Does the co-de-Bruijn RESIDUAL obstruction (restriction-composition ↾-⨾) reappear
-- IDENTICALLY in the MULTI-SORTED setting?  Test: a sorted substitution-vector `Sub`
-- (one entry per SORTED position), its restriction `↾`, and the composition law `↾-⨾`.
-- Register ↾-⨾ ⇒ if we get the SAME 3 critical pairs as single-sorted FOp, the
-- obstruction is sort-agnostic (lives purely in the thinning/vector algebra).
module FOpMS.ObsTest where
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite
open import FOpMS.ThinRw

private variable
  s : Sort
  Δ Θ sup Γ : Scope

-- a sorted substitution-vector: one entry per SORTED position (payload = Pos, i.e. a renaming)
data Sub (Δ : Scope) : Scope → Set where
  ε   : Sub Δ []
  _∙_ : Pos Δ s → Sub Δ Θ → Sub Δ (s ∷ Θ)

_↾_ : Sub Δ Θ → sup ⊑ Θ → Sub Δ sup
ε       ↾ oz   = ε
(t ∙ σ) ↾ os θ = t ∙ (σ ↾ θ)
(t ∙ σ) ↾ o' θ = σ ↾ θ

↾-⨾ : (σ : Sub Δ Θ)(θ : sup ⊑ Θ)(φ : Γ ⊑ sup) → (σ ↾ θ) ↾ φ ≡ σ ↾ (φ ⨾ θ)
↾-⨾ ε       oz     oz     = refl
↾-⨾ (t ∙ σ) (os θ) (os φ) = cong (t ∙_) (↾-⨾ σ θ φ)
↾-⨾ (t ∙ σ) (os θ) (o' φ) = ↾-⨾ σ θ φ
↾-⨾ (t ∙ σ) (o' θ) φ      = ↾-⨾ σ θ φ

-- RESULT: registering  {-# REWRITE ↾-⨾ #-}  fails --local-confluence-check with the
-- IDENTICAL 3 critical pairs as single-sorted FOp (verified) — the residual co-de-Bruijn
-- obstruction is SORT-AGNOSTIC (↾-elimination vs ↾-composition):
--   ((t ∙ σ) ↾ os θ) ↾ φ   -- ↾-⨾ vs the os elimination clause
--   ((σ ↾ θ) ↾ θ₁) ↾ φ     -- ↾-⨾ with itself (triple-restriction associativity)
--   (ε ↾ oz) ↾ φ           -- ↾-⨾ vs the oz elimination clause
-- ⇒ multi-sortedness is orthogonal to the confluent ⊻ subst-free question.
-- (Uncomment the pragma to reproduce.)
-- {-# REWRITE ↾-⨾ #-}
