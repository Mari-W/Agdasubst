{-# OPTIONS --rewriting #-}

-- Why the rule set has exactly the rules it has: the ABSENCES, checked.
--
-- TRS.md derives the 72 rules as a small base closed under four completion
-- operators (C1 two worlds, C2 continuations, C3 mode V, C4 coercion).  Each
-- operator comes with a side condition saying when an image is NOT needed.
-- Those side conditions are the interesting part of the account -- they are
-- what makes the rule set a derivation rather than a list -- and they are what
-- this module checks.  Every proof is `refl`, so each one says: the redex the
-- missing rule would have handled already reduces without it.
--
-- Checked from OUTSIDE systemf's `opaque` block, on purpose: inside it the
-- definitions unfold and the rules no longer match, so a `refl` there would
-- prove something else.

module closure where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import systemf

private variable
  S₄ S₅ : Scope

-- ══ C2: `assoc` right-nests `⨟`, so a rule matching a non-variable RIGHT
--    operand can no longer see it inside a chain and needs a `-⨟` image.
--    FIVE rules match a non-variable right operand and have NO such image.
--    The claim is that each continued redex escapes by an inner step.

-- comp-idᵣᴿ escapes because idᴿ is also a LEFT unit
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

-- ══ C4: ⟨⟩-split-tail is the TAIL companion of ⟨⟩-split-⨟, and is needed
--    only in tail position.  With a continuation present, ⟨⟩-split-⨟ followed
--    by lift-dist-compˢᴿ-⨟ already does the job, which is why there is no
--    `⟨⟩-split-tail-⨟`.
c4-tail : ∀ {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} {ξ′ : (s ∷ S₃) →ᴿ S₄} {τ : S₄ →ˢ S₅} →
  (σ ↑ˢ s) ⨟ (⟨ (ξ ↑ᴿ s) ⨟ᴿ ξ′ ⟩ ⨟ τ) ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s) ⨟ (⟨ ξ′ ⟩ ⨟ τ)
c4-tail = refl

-- ══ THE DISPLAYED NORMALIZATION (paper, §3.3) ═══════════════════════
--    Every intermediate term of the two branches shown in the paper is the
--    same normal form, so each step below holds by `refl`.  This is what
--    licenses the claim that the displayed trace is the one Agda takes.

module Trace {S₁ S₂ : Scope} {s s′ : Sort}
  (t : (s′ ∷ S₁) ⊢ s) (t′ : S₁ ⊢ s′) (σ : S₁ →ˢ S₂) where

  nf : S₂ ⊢ s                                            -- the shared normal form
  nf = t [ ((t′ [ σ ]ˢ) ∙ˢ σ) ]ˢ

  -- left branch:  (t [ ⇑σ ]) [ t′[σ] ]₀  ↠  nf
  l0 : (t [ (σ ↑ˢ s′) ]ˢ) [ t′ [ σ ]ˢ ]₀                              ≡ nf
  l0 = refl
  l1 : (t [ (σ ↑ˢ s′) ]ˢ) [ ((t′ [ σ ]ˢ) ∙ˢ idˢ) ]ˢ                   ≡ nf
  l1 = refl
  l2 : t [ ((σ ↑ˢ s′) ⨟ ((t′ [ σ ]ˢ) ∙ˢ idˢ)) ]ˢ                      ≡ nf
  l2 = refl
  l3 : t [ ((t′ [ σ ]ˢ) ∙ˢ (σ ⨟ idˢ)) ]ˢ                              ≡ nf
  l3 = refl

  -- right branch:  (t [ t′ ]₀) [ σ ]  ↠  nf
  r0 : (t [ t′ ]₀) [ σ ]ˢ                                             ≡ nf
  r0 = refl
  r1 : (t [ (t′ ∙ˢ idˢ) ]ˢ) [ σ ]ˢ                                    ≡ nf
  r1 = refl
  r2 : t [ ((t′ ∙ˢ idˢ) ⨟ σ) ]ˢ                                       ≡ nf
  r2 = refl
  r3 : t [ ((t′ [ σ ]ˢ) ∙ˢ (idˢ ⨟ σ)) ]ˢ                              ≡ nf
  r3 = refl

-- ══ lift-id (σ⇑'s LiftId) is SUBSUMED, not excluded: its left-hand side is a
--    strict instance of ⟨⟩-lift's, which sends it to ⟨ idᴿ ↑ᴿ s ⟩, where
--    lift-idᴿ finishes under the coercion.  Deregistering it therefore costs
--    no definitional equality -- this is that claim, stated as user code.
lift-id-is-subsumed : ∀ {S} → (⟨ idᴿ {S} ⟩ ↑ˢ s) ≡ ⟨ idᴿ ⟩
lift-id-is-subsumed = refl

-- and the step that makes it work: lift-idᴿ does fire under the coercion
lift-idᴿ-under-⟨⟩ : ∀ {S} → ⟨ idᴿ {S} ↑ᴿ s ⟩ ≡ ⟨ idᴿ ⟩
lift-idᴿ-under-⟨⟩ = refl
