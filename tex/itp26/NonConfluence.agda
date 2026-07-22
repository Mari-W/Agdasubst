{-# OPTIONS --rewriting #-}
-- ════════════════════════════════════════════════════════════════════════════
-- A WITNESS that systemfLift's rewrite system is not confluent.
--
-- The critical pair is def-wk against def-compᴿˢ.  Common ancestor:
--
--     (x ⋯ᴿ wkᴿ s′) ⋯ˢ σ
--
--   ── def-wk ─────►  suc x ⋯ˢ σ                  (rewrites the subterm)
--   ── def-compᴿˢ ─►  x ⋯ˢ (⟨ wkᴿ s′ ⟩ ⨟ σ)       (rewrites at the root)
--
-- Both reducts are normal forms: for an abstract σ nothing further applies
-- (def-∙ˢ-suc and ↑ˢ-suc need σ to be a cons resp. a lift; interact needs the
-- right factor of ⨟ to be a cons).  They are provably equal — see joined-prop —
-- but NOT definitionally equal, see joined-def.  That is the non-confluence.
--
-- Note the shape of the rejection: "S₁ != s′ ∷ S₁".  The two normal forms apply
-- _⋯ˢ_ at DIFFERENT source scopes (s′ ∷ S₁ for `suc x`, S₁ for `x`), so the
-- mismatch surfaces on an implicit index rather than on the visible term.  Not
-- every such message from the confluence checker is a unification artifact.
-- ════════════════════════════════════════════════════════════════════════════
module NonConfluence where

open import systemfLift
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

module _ {S₁ S₂ : List Sort} {s s′ : Sort}
         (x : S₁ ∋ s) (σ : (s′ ∷ S₁) →ˢ S₂) where

  src redA redB : S₂ ⊢ s
  src  = (x ⋯ᴿ wkᴿ s′) ⋯ˢ σ          -- the peak
  redA = suc x ⋯ˢ σ                  -- reduct via def-wk
  redB = x ⋯ˢ (⟨ wkᴿ s′ ⟩ ⨟ σ)       -- reduct via def-compᴿˢ

  -- Agda's strategy normalises the subterm first, so it lands on redA:
  srcA : src ≡ redA
  srcA = refl

  -- but redB is a genuine reduct of the same term, by the other rule:
  srcB : src ≡ redB
  srcB = def-compᴿˢ {x = x} {ρ₁ = wkᴿ s′} {σ₂ = σ}

  -- hence the two reducts are PROPOSITIONALLY equal …
  joined-prop : redB ≡ redA
  joined-prop = trans (sym srcB) srcA

  -- … but NOT definitionally.  Uncommenting the next line gives
  --   error: [UnequalTerms]  S₁ != s′ ∷ S₁ of type List Sort
  --   when checking that the expression refl has type redB ≡ redA
  --
  -- joined-def : redB ≡ redA
  -- joined-def = refl
