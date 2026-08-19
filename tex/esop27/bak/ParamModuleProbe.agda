{-# OPTIONS --rewriting --local-confluence-check #-}
-- ⚠ MEASUREMENT PROBE for REPORT-options.md §9 ⚠  Nothing imports this file.
--
-- THE IDEA UNDER TEST (option 10).  Agda checks confluence at the point
-- of RULE DECLARATION.  So: declare the semantic rewrite rules inside a
-- module PARAMETRISED over an abstract type-substitution structure.
-- Inside that module the type operations are module parameters, hence
-- rigid variables, hence there is nothing for the semantic rules to
-- overlap — R_type does not exist there.  Then instantiate the module
-- with the concrete SystemF-strat layer.
--
-- MEASURED OUTCOME: none of the three anticipated branches.  The rules
-- are REJECTED AT DECLARATION, inside the parametrised module, before
-- instantiation is ever reached:
--
--   warning: -W[no]RewriteVariablesNotBoundByLHS
--   ⟦⟧-sub is not a legal rewrite rule, since the following variables
--   are not bound by the left hand side:  σ, T, Δ₁
--   ⊙-assoc … not bound by the left hand side:  τ, σ, Δ₂
--
-- and the in-module probe then fails, because the rule never fired.
--
-- WHY.  A rewrite rule's LHS must determine all its variables by
-- FIRST-ORDER matching.  Here the LHS is `⟦ app T σ ⟧ η` where `app` is
-- a module parameter — a variable.  Matching against a variable-headed
-- application determines nothing, so `T`, `σ` and `Δ₁` are unbound.
--
-- The property that makes the parametrised module attractive (the type
-- operations are abstract, so nothing can overlap them) is the SAME
-- property that makes them non-matchable.  See REPORT-options.md §9.
--
-- POSTULATES USED (named, as required): `SEnv`, `⟦_⟧`, `⊙`, `⟦⟧-sub`.
-- They stand in for the semantic layer.  The question here is purely
-- about rule registration and firing across module instantiation, and
-- postulating the semantic side makes that question sharper, not weaker:
-- if the technique cannot even work for an abstract semantics it cannot
-- work for a real one.
module ParamModuleProbe where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- imported QUALIFIED so that no name of ours clashes with strat.
-- strat's ~40 rewrite rules are registered globally regardless of
-- qualification, which is exactly the situation under test.
import SystemF-strat as S

-- ══════════════════════════════════════════════════════════════════
-- The abstract type layer.  `Ty`, `Sb`, `_⟦[_]⟧_` and `_⟦⨟⟧_` are module
-- PARAMETERS.  No rewrite rules exist for them; the σ-laws are not even
-- mentioned, so a fortiori nothing can overlap.
-- ══════════════════════════════════════════════════════════════════
module AbstractSem
  (Ty  : S.LCtx → Level → Set)
  (Sb  : S.LCtx → S.LCtx → Set)
  (app : ∀ {Δ₁ Δ₂ l} → Ty Δ₁ l → Sb Δ₁ Δ₂ → Ty Δ₂ l)
  (cmp : ∀ {Δ₁ Δ₂ Δ₃} → Sb Δ₁ Δ₂ → Sb Δ₂ Δ₃ → Sb Δ₁ Δ₃)
  where

  postulate
    SEnv    : S.LCtx → Set
    ⟦_⟧    : ∀ {Δ l} → Ty Δ l → SEnv Δ → Set l
    ⊙      : ∀ {Δ₁ Δ₂} → Sb Δ₁ Δ₂ → SEnv Δ₂ → SEnv Δ₁
    -- the headline semantic law.  Its LHS mentions `app`, which here is
    -- a module parameter (a rigid variable), not a defined symbol.
    ⟦⟧-sub : ∀ {Δ₁ Δ₂ l} (T : Ty Δ₁ l) (σ : Sb Δ₁ Δ₂) (η : SEnv Δ₂) →
             ⟦ app T σ ⟧ η ≡ ⟦ T ⟧ (⊙ σ η)
    -- the closer that the concrete setting needs (layer-(ii) P3/P9)
    ⊙-assoc : ∀ {Δ₁ Δ₂ Δ₃} (σ : Sb Δ₁ Δ₂) (τ : Sb Δ₂ Δ₃) (η : SEnv Δ₃) →
              ⊙ (cmp σ τ) η ≡ ⊙ σ (⊙ τ η)

  {-# REWRITE ⟦⟧-sub ⊙-assoc #-}

  -- probe INSIDE the abstract module: does the rule fire where the type
  -- operations are parameters?  Expected: yes, trivially.
  probe-abstract : ∀ {Δ₁ Δ₂ l} (T : Ty Δ₁ l) (σ : Sb Δ₁ Δ₂) (η : SEnv Δ₂) →
                   ⟦ app T σ ⟧ η ≡ ⟦ T ⟧ (⊙ σ η)
  probe-abstract T σ η = refl

-- ══════════════════════════════════════════════════════════════════
-- INSTANTIATION with the concrete SystemF-strat layer, where `_[_]ˢ`
-- and `_⨟ˢ_` ARE defined symbols carrying ~40 registered rewrite rules.
-- ══════════════════════════════════════════════════════════════════
module C = AbstractSem S.Type S.Sub (λ T σ → S._[_]ˢ T σ) (λ σ τ → S._⨟ˢ_ σ τ)

-- ── the three questions ──

-- (a) does the rule still fire at the instantiated operations?
probe-fires : ∀ {Δ₁ Δ₂ l} (T : S.Type Δ₁ l) (σ : S.Sub Δ₁ Δ₂) (η : C.SEnv Δ₂) →
              C.⟦ S._[_]ˢ T σ ⟧ η ≡ C.⟦ T ⟧ (C.⊙ σ η)
probe-fires T σ η = refl

-- (b) does it fire at a COMPOSED substitution — the shape that generated
--     the critical pairs (`compositionalityˢˢ` rewrites `(T[σ]ˢ)[τ]ˢ`)?
probe-composed : ∀ {Δ₁ Δ₂ Δ₃ l} (T : S.Type Δ₁ l) (σ : S.Sub Δ₁ Δ₂) (τ : S.Sub Δ₂ Δ₃)
                 (η : C.SEnv Δ₃) →
                 C.⟦ S._[_]ˢ (S._[_]ˢ T σ) τ ⟧ η ≡ C.⟦ T ⟧ (C.⊙ σ (C.⊙ τ η))
probe-composed T σ τ η = refl

-- (c) does it fire at a RIGID type former — the case the matching limit
--     is known to permit?
probe-rigid : ∀ {Δ₁ Δ₂ l₁ l₂} (T₁ : S.Type Δ₁ l₁) (T₂ : S.Type Δ₁ l₂)
              (σ : S.Sub Δ₁ Δ₂) (η : C.SEnv Δ₂) →
              C.⟦ S._[_]ˢ (S._⇒_ T₁ T₂) σ ⟧ η ≡ C.⟦ S._⇒_ T₁ T₂ ⟧ (C.⊙ σ η)
probe-rigid T₁ T₂ σ η = refl
