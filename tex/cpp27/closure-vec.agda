{-# OPTIONS --rewriting #-}

-- Does the vector rule set still DECIDE the rules it does not register?
--
-- systemf-vec.agda registers 53 rules where systemf.agda registers 72.
-- The 19 it drops are the completion families: the `-⨟` continuation
-- companions, the mode-V `-var` companions, and the coercion family.
-- Dropping a rule from the REGISTERED set is only sound if the equation
-- it stated still holds, so this module states every one of them and
-- asks for `refl`.  A `refl` here says: the rule set reduces both sides
-- to the same normal form without that rule being registered.
--
-- Checked from OUTSIDE systemf-vec's `opaque` blocks, on purpose: inside
-- them the definitions unfold and the rules no longer match, so a `refl`
-- there would prove something else.

module closure-vec where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import systemf-vec

private variable
  S₄ S₅ : Scope

-- ══ the seven `-⨟` continuation companions ═════════════════════════

c-def-↑ˢ-zero-⨟ : ∀ {σ : S₁ →ˢ S₂} {τ : (s ∷ S₂) →ˢ S₃} →
  zero [ ((σ ↑ˢ s) ⨟ˢ τ) ]ˢ ≡ zero [ τ ]ˢ
c-def-↑ˢ-zero-⨟ = refl

c-def-↑ˢ-suc-⨟ : ∀ {x : S₁ ∋ s′} {σ : S₁ →ˢ S₂} {τ : (s ∷ S₂) →ˢ S₃} →
  (suc x) [ ((σ ↑ˢ s) ⨟ˢ τ) ]ˢ ≡ x [ (σ ⨟ˢ (⟨ wkᴿ s ⟩ ⨟ˢ τ)) ]ˢ
c-def-↑ˢ-suc-⨟ = refl

c-lift-wk-⨟ : ∀ {σ : S₁ →ˢ S₂} {τ : (s ∷ S₂) →ˢ S₃} →
  ⟨ wkᴿ s ⟩ ⨟ˢ ((σ ↑ˢ s) ⨟ˢ τ) ≡ σ ⨟ˢ (⟨ wkᴿ s ⟩ ⨟ˢ τ)
c-lift-wk-⨟ = refl

c-lift-dist-compˢˢ-⨟ : ∀ {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
  (σ₁ ↑ˢ s) ⨟ˢ ((σ₂ ↑ˢ s) ⨟ˢ τ) ≡ ((σ₁ ⨟ˢ σ₂) ↑ˢ s) ⨟ˢ τ
c-lift-dist-compˢˢ-⨟ = refl

c-interactᴿ-⨟ᴿ : ∀ {x : S₂ ∋ s} {ξ : S₁ →ᴿ S₂} {ξ′ : S₂ →ᴿ S₃} →
  wkᴿ s ⨟ᴿ ((x ∙ᴿ ξ) ⨟ᴿ ξ′) ≡ ξ ⨟ᴿ ξ′
c-interactᴿ-⨟ᴿ = refl

c-lift-wkᴿ-⨟ᴿ : ∀ {ξ : S₁ →ᴿ S₂} {ξ′ : (s ∷ S₂) →ᴿ S₃} →
  wkᴿ s ⨟ᴿ ((ξ ↑ᴿ s) ⨟ᴿ ξ′) ≡ ξ ⨟ᴿ (wkᴿ s ⨟ᴿ ξ′)
c-lift-wkᴿ-⨟ᴿ = refl

c-lift-dist-compᴿᴿ-⨟ᴿ : ∀ {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} {ξ′ : (s ∷ S₃) →ᴿ S₄} →
  (ξ₁ ↑ᴿ s) ⨟ᴿ ((ξ₂ ↑ᴿ s) ⨟ᴿ ξ′) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ⨟ᴿ ξ′
c-lift-dist-compᴿᴿ-⨟ᴿ = refl

-- ══ the mode-V `-var` companions ═══════════════════════════════════

c-compositionalityᴿˢ-⨟-var : ∀ {x : S₁ ∋ s} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
  x [ (⟨ ξ ⟩ ⨟ˢ σ) ]ˢ ≡ (x [ ξ ]ᴿ) [ σ ]ˢ
c-compositionalityᴿˢ-⨟-var = refl

c-lift-dist-compᴿᴿ-var : ∀ {x : (s ∷ S₁) ∋ s′} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
  (x [ (ξ₁ ↑ᴿ s) ]ᴿ) [ (ξ₂ ↑ᴿ s) ]ᴿ ≡ x [ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ]ᴿ
c-lift-dist-compᴿᴿ-var = refl

c-lift-dist-compᴿˢ-var : ∀ {x : (s ∷ S₁) ∋ s′} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
  (x [ (ξ ↑ᴿ s) ]ᴿ) [ (σ ↑ˢ s) ]ˢ ≡ x [ ((⟨ ξ ⟩ ⨟ˢ σ) ↑ˢ s) ]ˢ
c-lift-dist-compᴿˢ-var = refl

c-lift-dist-compᴿˢ-⨟-var : ∀ {x : (s ∷ S₁) ∋ s′}
  {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
  (x [ (ξ ↑ᴿ s) ]ᴿ) [ ((σ ↑ˢ s) ⨟ˢ τ) ]ˢ ≡ x [ (((⟨ ξ ⟩ ⨟ˢ σ) ↑ˢ s) ⨟ˢ τ) ]ˢ
c-lift-dist-compᴿˢ-⨟-var = refl

c-⟨⟩-lift-cons-var : ∀ {x : (s ∷ S₁) ∋ s′} {ξ : S₁ →ᴿ S₂} {t : S₃ ⊢ s} {σ : S₂ →ˢ S₃} →
  (x [ (ξ ↑ᴿ s) ]ᴿ) [ (t ∙ˢ σ) ]ˢ ≡ x [ (t ∙ˢ (⟨ ξ ⟩ ⨟ˢ σ)) ]ˢ
c-⟨⟩-lift-cons-var = refl

-- ══ the coercion family ════════════════════════════════════════════

c-lift-dist-compˢᴿ : ∀ {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
  ((σ ↑ˢ s) ⨟ˢ ⟨ ξ ↑ᴿ s ⟩) ≡ ((σ ⨟ˢ ⟨ ξ ⟩) ↑ˢ s)
c-lift-dist-compˢᴿ = refl

c-lift-dist-compᴿˢ-⨟ : ∀ {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
  ⟨ ξ ↑ᴿ s ⟩ ⨟ˢ ((σ ↑ˢ s) ⨟ˢ τ) ≡ ((⟨ ξ ⟩ ⨟ˢ σ) ↑ˢ s) ⨟ˢ τ
c-lift-dist-compᴿˢ-⨟ = refl

c-lift-dist-compˢᴿ-⨟ : ∀ {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
  (σ ↑ˢ s) ⨟ˢ (⟨ ξ ↑ᴿ s ⟩ ⨟ˢ τ) ≡ ((σ ⨟ˢ ⟨ ξ ⟩) ↑ˢ s) ⨟ˢ τ
c-lift-dist-compˢᴿ-⨟ = refl

c-⟨⟩-comp-⨟-lift-wkᴿ : ∀ {ξ : S₁ →ᴿ S₂} {τ : (s ∷ S₂) →ˢ S₄} →
  ⟨ wkᴿ s ⟩ ⨟ˢ (⟨ ξ ↑ᴿ s ⟩ ⨟ˢ τ) ≡ ⟨ ξ ⟩ ⨟ˢ (⟨ wkᴿ s ⟩ ⨟ˢ τ)
c-⟨⟩-comp-⨟-lift-wkᴿ = refl

c-⟨⟩-comp-⨟-interactᴿ : ∀ {ξ : S₁ →ᴿ S₂} {x : S₂ ∋ s} {τ : S₂ →ˢ S₃} →
  ⟨ wkᴿ s ⟩ ⨟ˢ (⟨ x ∙ᴿ ξ ⟩ ⨟ˢ τ) ≡ ⟨ ξ ⟩ ⨟ˢ τ
c-⟨⟩-comp-⨟-interactᴿ = refl

c-⟨⟩-comp-⨟-lift-dist-compᴿᴿ : ∀ {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
  ⟨ ξ₁ ↑ᴿ s ⟩ ⨟ˢ (⟨ ξ₂ ↑ᴿ s ⟩ ⨟ˢ τ) ≡ ⟨ (ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s ⟩ ⨟ˢ τ
c-⟨⟩-comp-⨟-lift-dist-compᴿᴿ = refl

c-⟨⟩-split-tail : ∀ {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} {ξ′ : (s ∷ S₃) →ᴿ S₄} →
  (σ ↑ˢ s) ⨟ˢ ⟨ (ξ ↑ᴿ s) ⨟ᴿ ξ′ ⟩ ≡ ((σ ⨟ˢ ⟨ ξ ⟩) ↑ˢ s) ⨟ˢ ⟨ ξ′ ⟩
c-⟨⟩-split-tail = refl

-- ══ the two systemf.agda proves but never registers ════════════════

c-distᴿ : ∀ {x : S₂ ∋ s} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
  (x ∙ᴿ ξ₁) ⨟ᴿ ξ₂ ≡ (x [ ξ₂ ]ᴿ) ∙ᴿ (ξ₁ ⨟ᴿ ξ₂)
c-distᴿ = refl

c-lift-consᴿ : ∀ {ξ : S₁ →ᴿ S₂} {x : S₃ ∋ s} {ξ′ : S₂ →ᴿ S₃} →
  (ξ ↑ᴿ s) ⨟ᴿ (x ∙ᴿ ξ′) ≡ x ∙ᴿ (ξ ⨟ᴿ ξ′)
c-lift-consᴿ = refl
