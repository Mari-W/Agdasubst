-- ════════════════════════════════════════════════════════════════════
-- THE OTHER HORN.  Companion to SystemF-explicit-type.agda.
--
-- Same three datatypes, same explicit weakening, same `_⇈` constructor
-- on `Type`.  ONE definition differs: `_[_]ˢ` recurses on the TYPE and
-- consumes the substitution at the two variable-shaped constructors,
-- through `headˢ` / `tailˢ`.  Composition follows and analyses its LEFT
-- argument.  Neither needs a renaming sort and neither needs a
-- {-# TERMINATING #-} pragma, so the prize of explicit weakening is
-- kept on both horns.
--
-- WHY THIS FILE EXISTS.  SystemF-explicit-type.agda records that the
-- expression-level traversal cannot be kept, because
--   (T₁ ⇒ T₂) [ η ]ˢ ≡ (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)
-- fails for an abstract η.  That is TRUE OF THAT DEFINITION.  Here the
-- same equation is `refl` (see `push-⇒`), and so is its ∀ companion.
-- The obstruction is therefore a TRADE, not a barrier, and the paper
-- should say so.  What this definition loses instead is
--   (a) the IDENTITY law  `T [ idˢ ]ˢ ≡ T`   — REFUTED (`no-id`)
--   (b) the MONAD law     `(T [ η₁ ]ˢ) [ η₂ ]ˢ ≡ T [ η₁ ⨟ˢ η₂ ]ˢ`
--                                            — not available; see the
--       measured failure at the bottom of this file.
--
-- CURRENT STATUS:
--
--   $ agda --library=standard-library -i. SystemF-explicit.agda
--   EXIT=0  —  ZERO non-joinable critical pairs.
--
--   15 rules, --rewriting --local-confluence-check, Agda 2.8.0.  So
--   BOTH horns admit a locally confluent rewrite system; they differ in
--   WHICH LAWS the system can contain.  Side by side:
--
--                                    subst-first        type-first
--                                    (…-type.agda)      (this file)
--     locally confluent rule set     YES, 15, 0 pairs   YES, 15, 0 pairs
--     T [ idˢ ]ˢ ≡ T                 refl               REFUTED
--     monad law (compositionality)   refl (via push)    NOT AVAILABLE
--     ⇒ / ∀ push, abstract η         REFUTED            refl
--     expression traversal           blocked            unblocked
--     η ⨟ˢ idˢ ≡ η                   refl               REFUTED
--     idˢ ⨟ˢ η ≡ η                   registered law     refl
--
--   Every cell of that table is machine-checked, in this file or in
--   SystemF-explicit-type.agda.  Both losses are `Type`- resp.
--   `Sub`-CONSTRUCTOR CLASHES, and both trace to the same decision:
--   `_⇈` applies to ANY type, not only to a variable.  Restricting it
--   to variables collapses the dilemma — and is exactly the design of
--   tex/cpp27/systemf.agda.
--
--   See report.md milestone 7.
-- ════════════════════════════════════════════════════════════════════
{-# OPTIONS --rewriting --local-confluence-check #-}
module SystemF-explicit where
open import Agda.Builtin.Equality.Rewrite public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans)
open import Relation.Nullary using (¬_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 5 _⇒_
infixr 6 _∙ˢ_
infix 8 _⇈

data Type : Nat → Set where
  •    : ∀ {n} → Type (1 + n)
  _⇈   : ∀ {n} → Type n → Type (1 + n)
  ∀α   : ∀ {n} → Type (1 + n) → Type n
  _⇒_  : ∀ {n} → Type n → Type n → Type n

variable
  n n′ n₁ n₂ n₃ : Nat
  T T′ T″ T₁ T₂ T₃ : Type n

data Sub : Nat → Nat → Set where
  idˢ   : ∀ {n} → Sub n n
  _⇈ˢ   : ∀ {n₁ n₂} → Sub n₁ n₂ → Sub n₁ (1 + n₂)
  _∙ˢ_  : ∀ {n₁ n₂} → Type n₂ → Sub n₁ n₂ → Sub (1 + n₁) n₂

variable
  η η′ η₁ η₂ η₃ : Sub n₁ n₂

opaque
  headˢ : Sub (1 + n₁) n₂ → Type n₂
  headˢ idˢ       = •
  headˢ (η ⇈ˢ)    = (headˢ η) ⇈
  headˢ (T ∙ˢ η)  = T

  tailˢ : Sub (1 + n₁) n₂ → Sub n₁ n₂
  tailˢ idˢ       = idˢ ⇈ˢ
  tailˢ (η ⇈ˢ)    = (tailˢ η) ⇈ˢ
  tailˢ (T ∙ˢ η)  = η

  _[_]ˢ : Type n₁ → Sub n₁ n₂ → Type n₂
  •          [ η ]ˢ = headˢ η
  (T ⇈)      [ η ]ˢ = T [ tailˢ η ]ˢ
  (∀α T)     [ η ]ˢ = ∀α (T [ • ∙ˢ (η ⇈ˢ) ]ˢ)
  (T₁ ⇒ T₂)  [ η ]ˢ = (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)

  -- composition must now analyse its LEFT argument, to match
  _⨟ˢ_ : Sub n₁ n₂ → Sub n₂ n₃ → Sub n₁ n₃
  idˢ       ⨟ˢ η₂ = η₂
  (η ⇈ˢ)    ⨟ˢ η₂ = η ⨟ˢ (tailˢ η₂)
  (T ∙ˢ η)  ⨟ˢ η₂ = (T [ η₂ ]ˢ) ∙ˢ (η ⨟ˢ η₂)

_↑ˢ : Sub n₁ n₂ → Sub (1 + n₁) (1 + n₂)
η ↑ˢ = • ∙ˢ (η ⇈ˢ)

opaque
  unfolding headˢ tailˢ _[_]ˢ _⨟ˢ_
  head-id : headˢ (idˢ {1 + n}) ≡ •
  head-wk : headˢ (η ⇈ˢ) ≡ (headˢ η) ⇈
  head-∙  : ∀ {n₁ n₂} (T : Type n₂) (η : Sub n₁ n₂) → headˢ (T ∙ˢ η) ≡ T
  tail-id : tailˢ (idˢ {1 + n}) ≡ idˢ ⇈ˢ
  tail-wk : tailˢ (η ⇈ˢ) ≡ (tailˢ η) ⇈ˢ
  tail-∙  : ∀ {n₁ n₂} (T : Type n₂) (η : Sub n₁ n₂) → tailˢ (T ∙ˢ η) ≡ η
  inst-•  : ∀ {n₁ n₂} (η : Sub (1 + n₁) n₂) → • [ η ]ˢ ≡ headˢ η
  inst-⇈  : (T ⇈) [ η ]ˢ ≡ T [ tailˢ η ]ˢ
  inst-∀  : (∀α T) [ η ]ˢ ≡ ∀α (T [ η ↑ˢ ]ˢ)
  inst-⇒  : (T₁ ⇒ T₂) [ η ]ˢ ≡ (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)
  comp-id : ∀ {n₁ n₂} (η : Sub n₁ n₂) → idˢ ⨟ˢ η ≡ η
  comp-wk : ∀ {n₁ n m} (η : Sub n₁ n) (η₂ : Sub (1 + n) m) → (η ⇈ˢ) ⨟ˢ η₂ ≡ η ⨟ˢ (tailˢ η₂)
  comp-∙  : ∀ {n₁ n₂ n₃} (T : Type n₂) (η : Sub n₁ n₂) (η₂ : Sub n₂ n₃) →
            (T ∙ˢ η) ⨟ˢ η₂ ≡ (T [ η₂ ]ˢ) ∙ˢ (η ⨟ˢ η₂)
  -- the two laws a σ-calculus for this design needs, both PROVABLE by
  -- induction on the LEFT factor
  head-⨟ : ∀ {n₁ n₂ n₃} (η₁ : Sub (1 + n₁) n₂) (η₂ : Sub n₂ n₃) →
           headˢ (η₁ ⨟ˢ η₂) ≡ (headˢ η₁) [ η₂ ]ˢ
  tail-⨟ : ∀ {n₁ n₂ n₃} (η₁ : Sub (1 + n₁) n₂) (η₂ : Sub n₂ n₃) →
           tailˢ (η₁ ⨟ˢ η₂) ≡ (tailˢ η₁) ⨟ˢ η₂
  head-id = refl
  head-wk = refl
  head-∙ T η = refl
  tail-id = refl
  tail-wk = refl
  tail-∙ T η = refl
  inst-• η = refl
  inst-⇈ = refl
  inst-∀ = refl
  inst-⇒ = refl
  comp-id η = refl
  comp-wk η η₂ = refl
  comp-∙ T η η₂ = refl
  head-⨟ idˢ       η₂ = refl
  head-⨟ (η ⇈ˢ)    η₂ = head-⨟ η (tailˢ η₂)
  head-⨟ (T ∙ˢ η)  η₂ = refl
  tail-⨟ idˢ       η₂ = refl
  tail-⨟ (η ⇈ˢ)    η₂ = tail-⨟ η (tailˢ η₂)
  tail-⨟ (T ∙ˢ η)  η₂ = refl

{-# REWRITE head-id head-wk head-∙ tail-id tail-wk tail-∙ #-}
{-# REWRITE inst-• inst-⇈ inst-∀ inst-⇒ #-}
{-# REWRITE comp-id comp-wk comp-∙ #-}
{-# REWRITE head-⨟ tail-⨟ #-}

-- ══════════════ probes ═════════════════════════════════════════════
-- The equations that the substitution-first file REFUTES, here by refl,
-- at an ABSTRACT substitution.  These are the λx and Λα clauses of the
-- expression-level traversal.
push-⇒ : (T₁ T₂ : Type n₁) (η : Sub n₁ n₂) →
         (T₁ ⇒ T₂) [ η ]ˢ ≡ (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)
push-⇒ T₁ T₂ η = refl

push-∀ : (T : Type (1 + n₁)) (η : Sub n₁ n₂) → (∀α T) [ η ]ˢ ≡ ∀α (T [ η ↑ˢ ]ˢ)
push-∀ T η = refl

push-⇈ : (T : Type n₁) (η : Sub (1 + n₁) n₂) → (T ⇈) [ η ]ˢ ≡ T [ tailˢ η ]ˢ
push-⇈ T η = refl

-- … and the price: the IDENTITY law, refuted.
no-wk : (T₁ T₂ : Type n) → ¬ ((T₁ ⇒ T₂) [ (idˢ {n}) ⇈ˢ ]ˢ ≡ (T₁ ⇒ T₂) ⇈)
no-wk T₁ T₂ ()

no-id : (T₁ T₂ : Type n) → ¬ (((T₁ ⇒ T₂) ⇈) [ idˢ ]ˢ ≡ (T₁ ⇒ T₂) ⇈)
no-id T₁ T₂ ()

-- what `_[_]ˢ` is really doing: pushing ⇈ inward, i.e. Wadler's §4
-- "normalisation", performed eagerly by the traversal
norm : (T₁ T₂ : Type n) →
       ((T₁ ⇒ T₂) ⇈) [ idˢ ]ˢ ≡ (T₁ [ (idˢ {n}) ⇈ˢ ]ˢ) ⇒ (T₂ [ (idˢ {n}) ⇈ˢ ]ˢ)
norm T₁ T₂ = refl

-- it IS the identity on the ⇈-NORMAL fragment, i.e. where `_⇈` is
-- applied only to variables
id-var  : ∀ {n} → (• {n}) [ idˢ ]ˢ ≡ •
id-var  = refl
id-var₁ : ∀ {n} → ((• {n}) ⇈) [ idˢ ]ˢ ≡ (• ⇈)
id-var₁ = refl
id-var₂ : ∀ {n} → (((• {n}) ⇈) ⇈) [ idˢ ]ˢ ≡ ((• ⇈) ⇈)
id-var₂ = refl

-- ── WHERE A σ-CALCULUS FOR THIS DESIGN RUNS INTO TROUBLE ───────────
-- Composition now analyses its LEFT argument (it must: `_[_]ˢ` no
-- longer analyses the substitution, so `η ⨟ˢ idˢ ≡ η` cannot be a
-- clause).  The `_⇈ˢ` law of the OTHER design is therefore refuted
-- here, by the mirror-image constructor clash on `Sub`:
no-comp-⇈ᵣ : ∀ {n₁ n₂ n₃} (T : Type n₂) (η : Sub n₁ n₂) (η₂ : Sub n₂ n₃) →
             ¬ ((T ∙ˢ η) ⨟ˢ (η₂ ⇈ˢ) ≡ ((T ∙ˢ η) ⨟ˢ η₂) ⇈ˢ)
no-comp-⇈ᵣ T η η₂ ()

-- and so is the right identity, exactly as in x/D1.agda
no-comp-idᵣ : ∀ {n₁ n₂} (T : Type n₂) (η : Sub n₁ n₂) →
              ¬ (((T ∙ˢ η) ⇈ˢ) ⨟ˢ idˢ ≡ (T ∙ˢ η) ⇈ˢ)
no-comp-idᵣ T η ()

-- the left identity, on the other hand, is a defining clause here
comp-idₗ-def : ∀ {n₁ n₂} (η : Sub n₁ n₂) → idˢ ⨟ˢ η ≡ η
comp-idₗ-def η = refl

-- ══════════════ where the monad law stops (MEASURED) ═══════════════
-- The compositionality law is provable at •, at _⇈ and at _⇒_ — the
-- registered `head-⨟` and `tail-⨟` close the first two — and it stops
-- at ∀α:
--
--   attempt-fold : (T : Type n₁) (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) →
--                  (T [ η₁ ]ˢ) [ η₂ ]ˢ ≡ T [ η₁ ⨟ˢ η₂ ]ˢ
--   attempt-fold •         η₁ η₂ = refl                                   -- ✔ head-⨟
--   attempt-fold (T ⇈)     η₁ η₂ = attempt-fold T (tailˢ η₁) η₂           -- ✔ tail-⨟
--   attempt-fold (T₁ ⇒ T₂) η₁ η₂ = cong₂ _⇒_ (attempt-fold T₁ η₁ η₂)
--                                            (attempt-fold T₂ η₁ η₂)      -- ✔
--   attempt-fold (∀α T)    η₁ η₂ = cong ∀α (attempt-fold T (η₁ ↑ˢ) (η₂ ↑ˢ))
--
--   error: [UnequalTerms]
--     η₁ ⨟ˢ tailˢ (• ∙ˢ (η₂ ⇈ˢ)) != (η₁ ⨟ˢ η₂) ⇈ˢ of type Sub n₁ (suc n₃)
--     when checking that the expression attempt-fold T (η₁ ↑ˢ) (η₂ ↑ˢ)
--     has type ((T [ η₁ ↑ˢ ]ˢ) [ η₂ ↑ˢ ]ˢ) ≡ (T [ (η₁ ⨟ˢ η₂) ↑ˢ ]ˢ)
--
-- The gap is exactly `η₁ ⨟ˢ (η₂ ⇈ˢ) ≡ (η₁ ⨟ˢ η₂) ⇈ˢ`, which
-- `no-comp-⇈ᵣ` above REFUTES.  Closing it needs an
-- ACTION-EXTENSIONALITY lemma — two substitutions with the same
-- headˢ/tailˢ behaviour act alike on every type — which is a second
-- development and is NOT attempted here.  Stated as a limitation, not
-- as an impossibility: no refutation of the monad law itself was found.
