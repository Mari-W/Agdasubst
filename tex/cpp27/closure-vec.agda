{-# OPTIONS --rewriting #-}

-- Why the vector rule set has exactly the rules it has: the absences,
-- checked.  Same claims as closure.agda, over maps modeled as vectors.
--
-- TRS.md derives the 73 rules as a small base closed under four completion
-- operators (C1 two worlds, C2 continuations, C3 mode V, C4 coercion).  Each
-- operator comes with a side condition saying when an image is not needed.
-- Those side conditions are the interesting part of the account -- they are
-- what makes the rule set a derivation rather than a list -- and they are what
-- this module checks.  Every proof is `refl`, so each one says: the redex the
-- missing rule would have handled already reduces without it.
--
-- Checked from outside systemf's `opaque` block, on purpose: inside it the
-- definitions unfold and the rules no longer match, so a `refl` there would
-- prove something else.

module closure-vec where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import systemf-vec

private variable
  S₄ S₅ : Scope

-- ══ C2: `assoc` right-nests `⨟`, so a rule matching a non-variable right
--    operand can no longer see it inside a chain and needs a `-⨟` image.
--    five rules match a non-variable right operand and have no such image.
--    The claim is that each continued redex escapes by an inner step.

-- comp-idᵣᴿ escapes because idᴿ is also a left unit
c2-comp-idᵣᴿ : ∀ {ξ : S₁ →ᴿ S₂} {ξ′ : S₂ →ᴿ S₃} → ξ ⨟ᴿ (idᴿ ⨟ᴿ ξ′) ≡ ξ ⨟ᴿ ξ′
c2-comp-idᵣᴿ = refl

-- comp-idᵣ, likewise, in the substitution world
c2-comp-idᵣ : ∀ {σ : S₁ →ˢ S₂} {τ : S₂ →ˢ S₃} → σ ⨟ (⟨ idᴿ ⟩ ⨟ τ) ≡ σ ⨟ τ
c2-comp-idᵣ = refl

-- interact escapes because (t ∙ˢ τ) ⨟ ρ fires `dist` and lands cons-shaped again
c2-interact : ∀ {τ : S₂ →ˢ S₃} {t : S₃ ⊢ s} {ρ : S₃ →ˢ S₄} →
  ⟨ wkᴿ s ⟩ ⨟ ((t ∙ˢ τ) ⨟ ρ) ≡ τ ⨟ ρ
c2-interact = refl

-- lift-cons: same escape
c2-lift-cons : ∀ {σ : S₁ →ˢ S₂} {τ : S₂ →ˢ S₃} {t : S₃ ⊢ s} {ρ : S₃ →ˢ S₄} →
  (σ ↑ˢ s) ⨟ ((t ∙ˢ τ) ⨟ ρ) ≡ (t [ ρ ]ˢ) ∙ˢ (σ ⨟ (τ ⨟ ρ))
c2-lift-cons = refl

-- ⟨⟩-lift-cons: same escape, one level up
c2-⟨⟩-cons : ∀ {ξ : S₁ →ᴿ S₂} {τ : S₂ →ˢ S₃} {t : S₃ ⊢ s} {ρ : S₃ →ˢ S₄} →
  ⟨ ξ ↑ᴿ s ⟩ ⨟ ((t ∙ˢ τ) ⨟ ρ) ≡ (t [ ρ ]ˢ) ∙ˢ (⟨ ξ ⟩ ⨟ (τ ⨟ ρ))
c2-⟨⟩-cons = refl

-- ══ C4: ⟨⟩-split-tail is the tail companion of ⟨⟩-split-⨟, and is needed
--    only in tail position.  With a continuation present, ⟨⟩-split-⨟ followed
--    by lift-dist-compˢᴿ-⨟ already does the job, which is why there is no
--    `⟨⟩-split-tail-⨟`.
c4-tail : ∀ {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} {ξ′ : (s ∷ S₃) →ᴿ S₄} {τ : S₄ →ˢ S₅} →
  (σ ↑ˢ s) ⨟ (⟨ (ξ ↑ᴿ s) ⨟ᴿ ξ′ ⟩ ⨟ τ) ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s) ⨟ (⟨ ξ′ ⟩ ⨟ τ)
c4-tail = refl

-- ══ lift-id (σ⇑'s LiftId) is subsumed, not excluded: its left-hand side is a
--    strict instance of ⟨⟩-lift's, which sends it to ⟨ idᴿ ↑ᴿ s ⟩, where
--    lift-idᴿ finishes under the coercion.  Deregistering it therefore costs
--    no definitional equality -- this is that claim, stated as user code.
lift-id-is-subsumed : ∀ {S} → (⟨ idᴿ {S} ⟩ ↑ˢ s) ≡ ⟨ idᴿ ⟩
lift-id-is-subsumed = refl

-- and the step that makes it work: lift-idᴿ does fire under the coercion
lift-idᴿ-under-⟨⟩ : ∀ {S} → ⟨ idᴿ {S} ↑ᴿ s ⟩ ≡ ⟨ idᴿ ⟩
lift-idᴿ-under-⟨⟩ = refl
