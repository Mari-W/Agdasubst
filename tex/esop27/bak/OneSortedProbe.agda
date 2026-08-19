{-# OPTIONS --rewriting --local-confluence-check #-}
-- ⚠ MEASUREMENT PROBE for REPORT-options.md ⚠
-- Nothing imports this file.  Expected outcome is stated in the report;
-- whichever way it goes, the exit status is the measurement.
--
-- THE QUESTION.  The semantic laws (`⟦ T [ σ ] ⟧ η ≡ ⟦ T ⟧ (⊙ σ η)` and
-- friends) failed to close against SystemF-strat's type-level σ-calculus.
-- Two candidate causes:
--
--   (H1) SHAPE.  A law whose LHS carries a computed type argument can
--        never be closed, because the type layer rewrites that argument.
--        Then no σ-calculus admits a confluent semantic extension.
--
--   (H2) SIZE.  strat's σ-calculus is TWO-SORTED — renamings AND
--        substitutions, joined by `coincidence` — which generates the
--        mixed `⟨⟩-lift-RS/SR/…` family (≈10 rules).  Rounds 6–7 of the
--        layer-(ii) campaign died against exactly that family.  A
--        SINGLE-SORTED λσ⇑ calculus does not have it.
--
-- MEASURED OUTCOME: neither.  The file does not reach the confluence
-- check at all.  It fails at the DESIGN stage:
--
--   Syntax.DisallowedInterleavedMutual: _[_] declared but not defined.
--   Since `opaque` blocks can not participate in mutual recursion,
--   their definition must be given before this point.
--
-- A single-sorted λσ⇑ must define lifting as
--     (σ ↑) (suc α) = (σ α) [ wkₛ ]
-- i.e. via THE TRAVERSAL, so `_↑` and `_[_]` are mutually recursive.
-- `opaque` cannot participate in mutual recursion, so `_↑` cannot be
-- opaque, so `σ ↑` is not rigid, so no rule may match on it.
--
-- SystemF-strat escapes this by being TWO-SORTED: `_↑ˢ` is defined via
-- the RENAMING traversal `_[_]ᴿ`, which is already complete when `_↑ˢ`
-- is declared, so `_↑ˢ` can be opaque and `_[_]ˢ` comes afterwards.
--
-- CONSEQUENCE FOR H2: the two-sorted structure is FORCED, not a curation
-- choice.  The mixed `⟨⟩-lift-RS/SR/…` family that the layer-(ii)
-- campaign died against is a consequence of the very device that makes
-- the map formers opaque-able in the first place.  "Drop to one sort" is
-- not an available move.  H2 is downgraded accordingly; see
-- REPORT-options.md §3.
--
-- Everything below is self-contained; it deliberately does NOT import
-- SystemF-strat, so that the measurement is about the design and not
-- about strat's particular curation.
module OneSortedProbe where

open import Agda.Builtin.Equality.Rewrite public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Axiom.Extensionality.Propositional using (Extensionality)

postulate fun-ext : ∀ {a b} → Extensionality a b

variable n m k : Nat

-- ══════════════ a three-constructor type language ══════════════
data Ty : Nat → Set where
  var : Fin n → Ty n
  arr : Ty n → Ty n → Ty n
  all : Ty (suc n) → Ty n

variable T T₁ T₂ : Ty n

-- ══════════════ single-sorted λσ⇑ substitutions ══════════════
-- All map formers are `opaque`, exactly as SystemF-strat wraps its maps:
-- that is what keeps their applications rigid so the rules below have
-- stable left-hand sides.
opaque
  Sub : Nat → Nat → Set
  Sub n m = Fin n → Ty m

  _&_ : Fin n → Sub n m → Ty m
  α & σ = σ α

  idₛ : Sub n n
  idₛ = var

  _∙_ : Ty m → Sub n m → Sub (suc n) m
  (T ∙ σ) zero    = T
  (T ∙ σ) (suc α) = σ α

infixl 6 _&_
infixr 5 _∙_

-- the traversal
_[_] : Ty n → Sub n m → Ty m

opaque
  unfolding Sub _&_ idₛ _∙_
  wkₛ : Sub n (suc n)
  wkₛ α = var (suc α)

  _⨟_ : Sub n m → Sub m k → Sub n k
  (σ ⨟ τ) α = (σ α) [ τ ]

  _↑ : Sub n m → Sub (suc n) (suc m)
  (σ ↑) zero    = var zero
  (σ ↑) (suc α) = (σ α) [ wkₛ ]

var _ [ σ ] = _ & σ
arr T₁ T₂ [ σ ] = arr (T₁ [ σ ]) (T₂ [ σ ])
all T [ σ ] = all (T [ σ ↑ ])

variable σ τ υ : Sub n m
variable α : Fin n

-- ══════════════ the λσ⇑ rules ══════════════
opaque
  unfolding Sub _&_ idₛ _∙_ wkₛ _⨟_ _↑

  beta-id     : α & idₛ ≡ var α
  beta-id     = refl
  beta-wk     : α & (wkₛ {n = n}) ≡ var (suc α)
  beta-wk     = refl
  beta-cons-z : zero & (T ∙ σ) ≡ T
  beta-cons-z = refl
  beta-cons-s : (suc α) & (T ∙ σ) ≡ α & σ
  beta-cons-s = refl
  beta-lift-z : zero & (σ ↑) ≡ var zero
  beta-lift-z = refl
  beta-lift-s : (suc α) & (σ ↑) ≡ (α & σ) [ wkₛ ]
  beta-lift-s = refl
  beta-comp   : α & (σ ⨟ τ) ≡ (α & σ) [ τ ]
  beta-comp   = refl

{-# REWRITE beta-id beta-wk beta-cons-z beta-cons-s beta-lift-z beta-lift-s beta-comp #-}

-- traversal laws (these need induction, hence separate)
identity : (T : Ty n) → T [ idₛ ] ≡ T
lift-id  : (idₛ {n = n}) ↑ ≡ idₛ

opaque
  unfolding Sub _&_ idₛ _∙_ wkₛ _⨟_ _↑
  lift-id = fun-ext λ { zero → refl ; (suc α) → refl }

identity (var α)     = refl
identity (arr T₁ T₂) = cong₂ arr (identity T₁) (identity T₂)
identity (all T)     = cong all (trans (cong (T [_]) lift-id) (identity T))

{-# REWRITE lift-id identity #-}

-- the map laws
opaque
  unfolding Sub _&_ idₛ _∙_ wkₛ _⨟_ _↑
  comp-idₗ : (idₛ {n = n}) ⨟ σ ≡ σ
  comp-idₗ = fun-ext λ α → refl
  interact : (wkₛ {n = n}) ⨟ (T ∙ σ) ≡ σ
  interact = fun-ext λ α → refl
  lift-cons : (σ ↑) ⨟ (T ∙ τ) ≡ T ∙ (σ ⨟ τ)
  lift-cons {σ = σ} = fun-ext λ { zero → refl ; (suc α) → refl }

{-# REWRITE comp-idₗ interact lift-cons #-}

compositionality : (T : Ty n) (σ : Sub n m) (τ : Sub m k) →
                   (T [ σ ]) [ τ ] ≡ T [ σ ⨟ τ ]
lift-fusion : (σ : Sub n m) (τ : Sub m k) → (σ ↑) ⨟ (τ ↑) ≡ (σ ⨟ τ) ↑

opaque
  unfolding Sub _&_ idₛ _∙_ wkₛ _⨟_ _↑
  lift-fusion σ τ = fun-ext λ { zero → refl
                             ; (suc α) → trans (compositionality (σ α) wkₛ (τ ↑))
                                               (sym (compositionality (σ α) τ wkₛ)) }

compositionality (var α)     σ τ = refl
compositionality (arr T₁ T₂) σ τ = cong₂ arr (compositionality T₁ σ τ) (compositionality T₂ σ τ)
compositionality (all T)     σ τ =
  cong all (trans (compositionality T (σ ↑) (τ ↑)) (cong (T [_]) (lift-fusion σ τ)))

{-# REWRITE lift-fusion compositionality #-}

-- ══════════════ the SEMANTIC layer ══════════════
-- Carrier and operations `opaque`, so family (A) — a rule competing with
-- a projection — cannot confound the family (B) measurement.
opaque
  Env : Nat → Set₁
  Env n = Fin n → Set

  lkp : Fin n → Env n → Set
  lkp α η = η α

  ext : Set → Env n → Env (suc n)
  ext A η zero    = A
  ext A η (suc α) = η α

⟦_⟧ : Ty n → Env n → Set
⟦ var α ⟧    η = lkp α η
⟦ arr T₁ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
⟦ all T ⟧    η = (A : Set) → ⟦ T ⟧ (ext A η)

opaque
  unfolding Env lkp ext Sub _&_ idₛ _∙_ wkₛ _⨟_ _↑
  ⊙ : Sub n m → Env m → Env n
  ⊙ σ η α = ⟦ α & σ ⟧ η

  lkp-⊙ : (α : Fin n) (σ : Sub n m) (η : Env m) → lkp α (⊙ σ η) ≡ ⟦ α & σ ⟧ η
  lkp-⊙ α σ η = refl

  ⊙-id : (η : Env n) → ⊙ idₛ η ≡ η
  ⊙-id η = fun-ext λ α → refl

  ⊙-cons : (T : Ty m) (σ : Sub n m) (η : Env m) → ⊙ (T ∙ σ) η ≡ ext (⟦ T ⟧ η) (⊙ σ η)
  ⊙-cons T σ η = fun-ext λ { zero → refl ; (suc α) → refl }

  ⊙-wk : (A : Set) (η : Env n) → ⊙ wkₛ (ext A η) ≡ η
  ⊙-wk A η = fun-ext λ α → refl

{-# REWRITE lkp-⊙ ⊙-id ⊙-cons ⊙-wk #-}

-- the two headline semantic laws
⟦⟧-sub : (T : Ty n) (σ : Sub n m) (η : Env m) → ⟦ T [ σ ] ⟧ η ≡ ⟦ T ⟧ (⊙ σ η)
⊙-lift : (σ : Sub n m) (A : Set) (η : Env m) → ⊙ (σ ↑) (ext A η) ≡ ext A (⊙ σ η)

opaque
  unfolding Env lkp ext ⊙ Sub _&_ idₛ _∙_ wkₛ _⨟_ _↑
  ⊙-lift σ A η = fun-ext λ { zero → refl
                           ; (suc α) → ⟦⟧-sub (α & σ) wkₛ (ext A η) }

⟦⟧-sub (var α)     σ η = refl
⟦⟧-sub (arr T₁ T₂) σ η = cong₂ (λ X Y → X → Y) (⟦⟧-sub T₁ σ η) (⟦⟧-sub T₂ σ η)
⟦⟧-sub (all T)     σ η =
  cong (λ f → (A : Set) → f A)
       (fun-ext λ A → trans (⟦⟧-sub T (σ ↑) (ext A η)) (cong ⟦ T ⟧ (⊙-lift σ A η)))

-- ★ THE MEASUREMENT ★
-- ⊙-assoc is the closer identified for the layer-(ii) pairs P3/P9.
opaque
  unfolding Env lkp ext ⊙ Sub _&_ idₛ _∙_ wkₛ _⨟_ _↑
  ⊙-assoc : (σ : Sub n m) (τ : Sub m k) (η : Env k) → ⊙ (σ ⨟ τ) η ≡ ⊙ σ (⊙ τ η)
  ⊙-assoc σ τ η = fun-ext λ α → ⟦⟧-sub (α & σ) τ η

{-# REWRITE ⟦⟧-sub ⊙-lift ⊙-assoc #-}

-- firing probes: the three equations the real development needs
probe-sub : (T : Ty n) (σ : Sub n m) (η : Env m) → ⟦ T [ σ ] ⟧ η ≡ ⟦ T ⟧ (⊙ σ η)
probe-sub T σ η = refl

probe-weaken : (T : Ty n) (A : Set) (η : Env n) → ⟦ T [ wkₛ ] ⟧ (ext A η) ≡ ⟦ T ⟧ η
probe-weaken T A η = refl

probe-single : (T : Ty (suc n)) (T′ : Ty n) (η : Env n) →
               ⟦ T [ T′ ∙ idₛ ] ⟧ η ≡ ⟦ T ⟧ (ext (⟦ T′ ⟧ η) η)
probe-single T T′ η = refl
