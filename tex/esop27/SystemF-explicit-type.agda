-- ════════════════════════════════════════════════════════════════════
-- STAGE 1 of the EXPLICIT-WEAKENING experiment.
--
-- SystemF.agda, with weakening made EXPLICIT in Wadler's sense
-- ("Explicit Weakening", EPTCS 413 (2024) 15-26) AT THE TYPE LEVEL
-- ONLY.  The expression level is meant to stay verbatim.
--
-- CURRENT STATUS, so that nobody has to guess:
--
--   $ agda --library=standard-library -i. SystemF-explicit-type.agda
--   EXIT=0  —  ZERO non-joinable critical pairs.
--
--   The file carries --rewriting AND --local-confluence-check and
--   PASSES.  15 rules, registered in three blocks (§3).  The answer to
--   "can a locally confluent Agda rewrite system be installed on top of
--   an explicit-weakening type level for System F?" is YES.
--
-- WHAT IS CHANGED, against SystemF.agda:
--   (a) `Type` loses its variable sort and gains a weakening
--       CONSTRUCTOR `_⇈`.  De Bruijn index k is `•` under k ⇈'s, but
--       `_⇈` applies to any type, not only a variable (Wadler §2.5).
--   (b) `Sub` becomes a DATATYPE with Wadler's three primitives
--       idˢ / _⇈ˢ / _∙ˢ_ (id, weaken, cons).  Instantiation `_[_]ˢ`
--       and composition `_⨟ˢ_` become META operations, defined by case
--       analysis on the SUBSTITUTION first (Wadler §§2.7-2.8).
--   (c) THE WHOLE TYPE-LEVEL RENAMING SORT IS DELETED: Ren, wkᴿ, idᴿ,
--       _∙ᴿ_, _&ᴿ_, _⨟ᴿ_, _↑ᴿ, _[_]ᴿ and the coercion ⟨_⟩, together
--       with every law about them.  See report.md for the deletion
--       list, name by name, against the original REWRITE block.
--   (d) `_↑ˢ` (lifting) is DERIVED, `η ↑ˢ = • ∙ˢ (η ⇈ˢ)`, not a
--       first-class opaque symbol.
--   (e) `weaken T` is the constructor application `T ⇈`, not `T [ wkᴿ ]ᴿ`.
--   (f) `_[_]ˢ` and `_⨟ˢ_` are OPAQUE, and their defining clauses are
--       re-registered as rewrite rules.  This is the one change that is
--       ours and not Wadler's, and it is what buys local confluence.
--       See §3 for why, and report.md milestone 4 for the measurements.
--
-- WHAT IT COST, honestly:
--
--   Local confluence is bought at the type level; the STAGE-1 GOAL of
--   keeping the expression level verbatim is still NOT met, and for one
--   reason only.  The traversal's λx clause needs
--     (T₁ ⇒ T₂) [ η ]ˢ ≡ (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)
--   for an ABSTRACT η, and its η = η′ ⇈ˢ case is `push-⇈-⇒`, which
--   `no-push-⇈-⇒` in §6 REFUTES.  That refutation is ABSOLUTE: both
--   sides are constructor applications of `Type`, so no choice of
--   definition can change it.  Everything below the §5 marker therefore
--   still stops at the last definition that typechecks.
--
--   READ THE COMPANION.  SystemF-explicit.agda is the OTHER HORN: the
--   same three datatypes with `_[_]ˢ` recursing on the TYPE instead.
--   There `(T₁ ⇒ T₂) [ η ]ˢ ≡ (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)` holds by
--   `refl` at an abstract η, and the traversal is unblocked — at the
--   price of the IDENTITY law `T [ idˢ ]ˢ ≡ T`, which is refuted there,
--   and of the MONAD law, which is not available there.  Both files
--   report 0 non-joinable pairs.  So the obstruction is a TRADE between
--   two constructor clashes, not a barrier, and both clashes trace to
--   the single decision that `_⇈` applies to ANY type rather than only
--   to a variable.  Restricting it to variables collapses the dilemma,
--   and is exactly the design of tex/cpp27/systemf.agda.
--
--   The `_·*_` clause ALSO still fails, and it too needs an equation
--   this signature does not give — bare `distributivity`.  But that
--   failure is of a WEAKER kind and the previous revision of this
--   header conflated the two.  `no-distributivity` is
--   DEFINITION-RELATIVE: the same three datatypes with `_⨟ˢ_` defined
--   by recursion on its LEFT argument make distributivity hold by
--   `refl`, at the price of refuting the RIGHT IDENTITY.  Measured;
--   see the note above `no-distributivity` in §6, and report.md §4.3,
--   which corrects report.md §3.4.  So stage 1 is blocked by ONE
--   absolute refutation and one contingent one, not by two absolute
--   ones.
--
--   Also honest: this file passes --local-confluence-check, not the
--   much stronger --confluence-check, under which it reports 25
--   ambiguities.  For calibration, SystemF.agda — the project's own
--   passing development — reports 284 under that flag.  Local
--   confluence is the standard here.
--
-- MEASURED, with both flags, all else equal.  The first four rows are
-- one-token perturbations of THIS file (report.md §4.5); the last two
-- are the earlier, transparent rule set (report.md §3.7-§3.9) and
-- Wadler's own development transcribed (report.md §2.2).
--   this file ......................................... 0 pairs, EXIT=0
--   associativity RIGHT-oriented instead of assoc-l .... 4 pairs
--   dist-⨟ dropped .................................... 2 pairs
--   fold-∙-∙ dropped .................................. 4 pairs
--   each of those three, flag removed ................. nothing reported
--   the previous revision: Wadler's three laws, with
--     _[_]ˢ and _⨟ˢ_ TRANSPARENT ...................... 8 pairs
--   Wadler's own λ↑ development (STLC, his own file) .. 12 pairs
-- ════════════════════════════════════════════════════════════════════
{-# OPTIONS --rewriting --local-confluence-check #-}
module SystemF-explicit-type where
open import Agda.Builtin.Equality.Rewrite public

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 5 _⇒_
infixr 6 _∙ˢ_
infix 8 _⇈

-- ══════════════ §1  Types ══════════════════════════════════════════
-- Wadler §2.5: there is no variable sort.  De Bruijn index zero is the
-- constructor `•`, and index (1+k) is `•` under k weakenings.  But `_⇈`
-- applies to ANY type, not just a variable.
data Type : Nat → Set where
  •    : ∀ {n} → Type (1 + n)
  _⇈   : ∀ {n} → Type n → Type (1 + n)
  ∀α   : ∀ {n} → Type (1 + n) → Type n
  _⇒_  : ∀ {n} → Type n → Type n → Type n

_ : Type 0                      -- a closed type:  ∀α. α→α
_ = ∀α (• ⇒ •)
_ : Type 0 -- ∀αβ. α→β→α
_ = ∀α (∀α (• ⇈ ⇒ • ⇒ • ⇈))

variable
  n n′ n₁ n₂ n₃ : Nat
  T T′ T″ T₁ T₂ T₃ : Type n

-- ══════════════ §2  Substitution on types ══════════════════════════
-- DELETED: the whole renaming sort (Ren, wkᴿ, idᴿ, _∙ᴿ_, _&ᴿ_, _⨟ᴿ_,
-- _↑ᴿ, _[_]ᴿ) and the coercion ⟨_⟩.  Explicit weakening is what makes
-- them unnecessary: a substitution is weakened by _⇈ˢ, and instantiating
-- with a weakened substitution weakens the RESULT — no traversal, hence
-- no structural-recursion problem, hence no need for renamings.

--! Substitution
-- substitutions: a DATATYPE, not a function (Wadler §2.6)
data Sub : Nat → Nat → Set where
  idˢ   : ∀ {n} → Sub n n
  _⇈ˢ   : ∀ {n₁ n₂} → Sub n₁ n₂ → Sub n₁ (1 + n₂)
  _∙ˢ_  : ∀ {n₁ n₂} → Type n₂ → Sub n₁ n₂ → Sub (1 + n₁) n₂

variable
  η η′ η₁ η₂ η₃ : Sub n₁ n₂

-- THE OPERATIONS ARE OPAQUE.  Wadler leaves them transparent, so their
-- defining clauses ARE reduction rules and compete with the registered
-- ones; Agda's checker sees both, and the mixture is not locally
-- confluent (8 pairs here, 12 in his own development — report.md §2.2,
-- §3.7).  Blocking them stops the clauses from reducing and hands the
-- ORIENTATION of every law back to us.  §3 is where that is spent.
--
-- Blocking has to be done to BOTH operations at once.  The CPP-side
-- measurement: making composition opaque while instantiation still
-- computed gave 6 non-joinable pairs, all of them compositionality
-- against the clauses of instantiation, failing precisely because
-- composition was stuck while instantiation computed.  The operations
-- that appear on both sides of the monad laws are blocked together.
opaque
  -- apply substitution to a type.  Case analysis is on the SUBSTITUTION
  -- first (Wadler §2.7): if it is idˢ or a weakening we answer without
  -- looking at the type at all.
  _[_]ˢ : Type n₁ → Sub n₁ n₂ → Type n₂
  T          [ idˢ ]ˢ     = T                                     -- (1)
  T          [ η ⇈ˢ ]ˢ    = (T [ η ]ˢ) ⇈                          -- (2)
  •          [ T ∙ˢ η ]ˢ  = T                                     -- (3)
  (T′ ⇈)     [ T ∙ˢ η ]ˢ  = T′ [ η ]ˢ                             -- (4)
  (∀α T′)    [ T ∙ˢ η ]ˢ  = ∀α (T′ [ • ∙ˢ ((T ∙ˢ η) ⇈ˢ) ]ˢ)       -- (5)
  (T₁ ⇒ T₂)  [ T ∙ˢ η ]ˢ  = (T₁ [ T ∙ˢ η ]ˢ) ⇒ (T₂ [ T ∙ˢ η ]ˢ)   -- (6)

  -- left-to-right composition, also a meta operation
  _⨟ˢ_ : Sub n₁ n₂ → Sub n₂ n₃ → Sub n₁ n₃
  η          ⨟ˢ idˢ        = η                                            -- (1)
  η          ⨟ˢ (η′ ⇈ˢ)    = (η ⨟ˢ η′) ⇈ˢ                                 -- (2)
  idˢ        ⨟ˢ (T ∙ˢ η′)  = T ∙ˢ η′                                      -- (3)
  (η ⇈ˢ)     ⨟ˢ (T ∙ˢ η′)  = η ⨟ˢ η′                                      -- (4)
  (T′ ∙ˢ η)  ⨟ˢ (T ∙ˢ η′)  = (T′ [ T ∙ˢ η′ ]ˢ) ∙ˢ (η ⨟ˢ (T ∙ˢ η′))        -- (5)

-- lifting is DERIVED, not primitive (contrast SystemF.agda, where _↑ˢ
-- is an opaque first-class symbol precisely to keep the η-rules out).
-- It needs no unfolding: it is two constructors.
_↑ˢ : Sub n₁ n₂ → Sub (1 + n₁) (1 + n₂)
η ↑ˢ = • ∙ˢ (η ⇈ˢ)

-- ══════════════ §3  The σ-calculus, ORIENTED ═══════════════════════
-- SystemF.agda registers 63 names (72 rules with the per-constructor
-- families).  Every one of them is deleted: 57 cannot even be STATED
-- here, because the symbols they mention (⟨_⟩, _[_]ᴿ, wkᴿ, _↑ᴿ, …) no
-- longer exist.  What is registered instead is 15 rules in three
-- groups, and only the third group is a design decision.
--
--   I.   the six clauses of _[_]ˢ, verbatim              (6 rules)
--   C.   four of the five clauses of _⨟ˢ_, plus the LAW
--        comp-idₗ in place of clause (3), which it subsumes (5 rules)
--   L.   four ORIENTED laws                              (4 rules)
--
-- Groups I and C are not a choice: they are what opacity took away and
-- they are put back exactly as they were.  Group L is the result.
--
-- OPACITY BY ITSELF BUYS NOTHING, and it is worth saying so plainly.
-- MEASURED (report.md §4.9): this same file, same opaque blocks, same
-- eleven clause rules, with group L replaced by Wadler's two laws in
-- HIS orientation, reports 8 non-joinable pairs — exactly the count of
-- the previous, transparent revision.  The clause rules are the same
-- rewrites either way.  What opacity buys is the ABILITY TO RE-ORIENT,
-- and the re-orientation is what takes 8 to 0.
--
-- ── WHY THE ORIENTATIONS ARE WHAT THEY ARE ─────────────────────────
--
-- `push` is compositionality registered RIGHT-TO-LEFT,
--   T [ η₁ ⨟ˢ η₂ ]ˢ  ⟶  (T [ η₁ ]ˢ) [ η₂ ]ˢ
-- the OPPOSITE of SystemF.agda, which folds.  Folding is what fails
-- here, and the reason is specific to explicit weakening: BOTH `_[_]ˢ`
-- and `_⨟ˢ_` analyse the substitution, and `_⨟ˢ_` analyses its RIGHT
-- argument.  A folded term `T [ η₁ ⨟ˢ η₂ ]ˢ` with η₂ abstract is
-- therefore doubly stuck — the composition cannot fire and the
-- instantiation cannot fire — while the peak's other branch has already
-- entered the type.  That is exactly the family-B residue of the
-- previous rule set (5 of its 8 pairs).  Pushing instead leaves the
-- leftmost instantiation next to a substitution that may be concrete,
-- so it can fire.  MEASURED: with the fold orientation the best subset
-- reaches 8 pairs and its completion cannot be written; with push it
-- reaches 0.
--
-- `fold-∙-∙` restores folding at ONE shape, cons against cons:
--   (T [ T′ ∙ˢ η ]ˢ) [ T″ ∙ˢ η′ ]ˢ  ⟶  T [ (T′ [ T″ ∙ˢ η′ ]ˢ) ∙ˢ (η ⨟ˢ (T″ ∙ˢ η′)) ]ˢ
-- The split is FORCED, not tuned.  `push` cannot close the peak
--   T [ (T′ ∙ˢ η) ⨟ˢ (T″ ∙ˢ η′) ]ˢ
-- against clause (5) of `_⨟ˢ_`, because push's branch lands on
-- `(T [ T′ ∙ˢ η ]ˢ) [ T″ ∙ˢ η′ ]ˢ` with T abstract, which no clause of
-- `_[_]ˢ` can touch.  It is the one place where the two stuck terms are
-- both cons-headed, so folding there is safe: the fold's result is
-- again a cons, on which the I-rules can fire, and no loop with push is
-- created because the RHS is written in `_⨟ˢ_`-reduced form.  Dropping
-- it costs 4 pairs and `probe-transfer`.
--
-- `assoc-l` is associativity LEFT-oriented.  Wadler's orientation is
-- the other one, and it is the bad rule of the control matrix: MEASURED
-- 4 pairs.  Left-nesting is what lets the C-rules keep firing, because
-- `_⨟ˢ_` analyses on the right.
--
-- `dist-⨟` is DISTRIBUTIVITY UNDER A CONTINUATION.  Bare distributivity
--   (T ∙ˢ η₁) ⨟ˢ η₂  ≡  (T [ η₂ ]ˢ) ∙ˢ (η₁ ⨟ˢ η₂)
-- is not available: at η₂ = η₂′ ⇈ˢ the composition must commit to a head
-- constructor of `Sub`, and clause (2) commits to `_⇈ˢ` (see the note
-- on `no-distributivity` in §6 — the commitment is forced, but WHICH
-- WAY is a choice, and report.md §4.3 measures the other choice).  In
-- the continued form the right factor is a CONS, not an abstract η₂,
-- and the clash does not arise.  This one companion closes the
-- `assoc-l` × clause-(5) peak; dropping it costs 2 pairs.
opaque
  unfolding _[_]ˢ _⨟ˢ_

  -- ══ I.  instantiation: the defining clauses, put back ════════════
  inst-id : T [ idˢ ]ˢ ≡ T
  inst-wk : T [ η ⇈ˢ ]ˢ ≡ (T [ η ]ˢ) ⇈
  inst-•  : • [ T ∙ˢ η ]ˢ ≡ T
  inst-⇈  : (T′ ⇈) [ T ∙ˢ η ]ˢ ≡ T′ [ η ]ˢ
  inst-∀  : (∀α T′) [ T ∙ˢ η ]ˢ ≡ ∀α (T′ [ • ∙ˢ ((T ∙ˢ η) ⇈ˢ) ]ˢ)
  inst-⇒  : (T₁ ⇒ T₂) [ T ∙ˢ η ]ˢ ≡ (T₁ [ T ∙ˢ η ]ˢ) ⇒ (T₂ [ T ∙ˢ η ]ˢ)

  -- ══ C.  composition: the defining clauses, put back ══════════════
  -- clause (3), `idˢ ⨟ˢ (T ∙ˢ η′)`, is NOT registered: comp-idₗ below
  -- subsumes it, and registering both would only add a trivial pair.
  comp-idᵣ  : η ⨟ˢ idˢ ≡ η                                     -- clause (1)
  comp-wk   : η ⨟ˢ (η′ ⇈ˢ) ≡ (η ⨟ˢ η′) ⇈ˢ                      -- clause (2)
  comp-wk-∙ : (η ⇈ˢ) ⨟ˢ (T ∙ˢ η′) ≡ η ⨟ˢ η′                    -- clause (4)
  comp-∙-∙  : (T′ ∙ˢ η) ⨟ˢ (T ∙ˢ η′)                           -- clause (5)
            ≡ (T′ [ T ∙ˢ η′ ]ˢ) ∙ˢ (η ⨟ˢ (T ∙ˢ η′))

  -- ══ the two laws, proved once, oriented below ════════════════════
  --! CompIdL
  comp-idₗ : (η : Sub n₁ n₂) → idˢ ⨟ˢ η ≡ η
  comp-idₗ idˢ         = refl
  comp-idₗ (η ⇈ˢ)      = cong _⇈ˢ (comp-idₗ η)
  comp-idₗ (T ∙ˢ η)    = refl

  --! Compositionality
  compositionalityˢˢ : (T : Type n₁) (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) →
                       (T [ η₁ ]ˢ) [ η₂ ]ˢ ≡ T [ η₁ ⨟ˢ η₂ ]ˢ
  compositionalityˢˢ T          η₁         idˢ         = refl
  compositionalityˢˢ T          η₁         (η₂ ⇈ˢ)     = cong _⇈ (compositionalityˢˢ T η₁ η₂)
  compositionalityˢˢ T          idˢ        (T₂ ∙ˢ η₂)  = refl
  compositionalityˢˢ T          (η₁ ⇈ˢ)    (T₂ ∙ˢ η₂)  = compositionalityˢˢ T η₁ η₂
  compositionalityˢˢ •          (T₁ ∙ˢ η₁) (T₂ ∙ˢ η₂)  = refl
  compositionalityˢˢ (T ⇈)      (T₁ ∙ˢ η₁) (T₂ ∙ˢ η₂)  = compositionalityˢˢ T η₁ (T₂ ∙ˢ η₂)
  compositionalityˢˢ (∀α T)     (T₁ ∙ˢ η₁) (T₂ ∙ˢ η₂)  =
    cong ∀α (compositionalityˢˢ T ((T₁ ∙ˢ η₁) ↑ˢ) ((T₂ ∙ˢ η₂) ↑ˢ))
  compositionalityˢˢ (T₁′ ⇒ T₂′) (T₁ ∙ˢ η₁) (T₂ ∙ˢ η₂) =
    cong₂ _⇒_ (compositionalityˢˢ T₁′ (T₁ ∙ˢ η₁) (T₂ ∙ˢ η₂))
              (compositionalityˢˢ T₂′ (T₁ ∙ˢ η₁) (T₂ ∙ˢ η₂))

  --! Associativity
  associativity : (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) (η₃ : Sub n₃ n′) →
                  (η₁ ⨟ˢ η₂) ⨟ˢ η₃ ≡ η₁ ⨟ˢ (η₂ ⨟ˢ η₃)
  associativity η₁          η₂          idˢ          = refl
  associativity η₁          η₂          (η₃ ⇈ˢ)      = cong _⇈ˢ (associativity η₁ η₂ η₃)
  associativity η₁          idˢ         (T₃ ∙ˢ η₃)   = refl
  associativity η₁          (η₂ ⇈ˢ)     (T₃ ∙ˢ η₃)   = associativity η₁ η₂ η₃
  associativity idˢ         (T₂ ∙ˢ η₂)  (T₃ ∙ˢ η₃)   = refl
  associativity (η₁ ⇈ˢ)     (T₂ ∙ˢ η₂)  (T₃ ∙ˢ η₃)   = associativity η₁ η₂ (T₃ ∙ˢ η₃)
  associativity (T₁ ∙ˢ η₁)  (T₂ ∙ˢ η₂)  (T₃ ∙ˢ η₃)   =
    cong₂ _∙ˢ_ (compositionalityˢˢ T₁ (T₂ ∙ˢ η₂) (T₃ ∙ˢ η₃))
               (associativity η₁ (T₂ ∙ˢ η₂) (T₃ ∙ˢ η₃))

  -- ══ L.  the four ORIENTED laws that are actually registered ══════
  --! OrientedLaws {
  -- compositionality, read RIGHT-TO-LEFT
  push : (T : Type n₁) (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) →
         T [ η₁ ⨟ˢ η₂ ]ˢ ≡ (T [ η₁ ]ˢ) [ η₂ ]ˢ

  -- folding, restored at the ONE shape where both sides are stuck
  fold-∙-∙ : ∀ {n₁ m n₃} (T : Type (1 + n₁)) (T′ : Type (1 + m)) (η : Sub n₁ (1 + m))
             (T″ : Type n₃) (η′ : Sub m n₃) →
             (T [ T′ ∙ˢ η ]ˢ) [ T″ ∙ˢ η′ ]ˢ
           ≡ T [ (T′ [ T″ ∙ˢ η′ ]ˢ) ∙ˢ (η ⨟ˢ (T″ ∙ˢ η′)) ]ˢ

  -- associativity, LEFT-oriented
  assoc-l : (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) (η₃ : Sub n₃ n′) →
            η₁ ⨟ˢ (η₂ ⨟ˢ η₃) ≡ (η₁ ⨟ˢ η₂) ⨟ˢ η₃

  -- distributivity, UNDER A COMPOSITION CONTINUATION
  dist-⨟ : ∀ {n₁ m k n′} (η₁ : Sub n₁ (1 + m)) (T′ : Type (1 + k)) (η : Sub m (1 + k))
           (T : Type n′) (η′ : Sub k n′) →
           (η₁ ⨟ˢ (T′ ∙ˢ η)) ⨟ˢ (T ∙ˢ η′)
         ≡ η₁ ⨟ˢ ((T′ [ T ∙ˢ η′ ]ˢ) ∙ˢ (η ⨟ˢ (T ∙ˢ η′)))
  --! }

  -- ── proofs ───────────────────────────────────────────────────────
  -- groups I and C are the clauses themselves, so `refl` inside the
  -- unfolding block; the group-L proofs are the two laws re-oriented,
  -- with `_⨟ˢ_` allowed to compute in the statement.
  inst-id   = refl
  inst-wk   = refl
  inst-•    = refl
  inst-⇈    = refl
  inst-∀    = refl
  inst-⇒    = refl
  comp-idᵣ  = refl
  comp-wk   = refl
  comp-wk-∙ = refl
  comp-∙-∙  = refl

  push T η₁ η₂          = sym (compositionalityˢˢ T η₁ η₂)
  fold-∙-∙ T T′ η T″ η′ = compositionalityˢˢ T (T′ ∙ˢ η) (T″ ∙ˢ η′)
  assoc-l η₁ η₂ η₃      = sym (associativity η₁ η₂ η₃)
  dist-⨟ η₁ T′ η T η′   = associativity η₁ (T′ ∙ˢ η) (T ∙ˢ η′)

-- ORDER IS LOAD-BEARING.  Agda checks each rule against those already
-- registered, so the dependencies must come first: the clause rules
-- before the laws, and within the laws the ⨟-algebra before push.
-- MEASURED with the previous, transparent rule set: three separate
-- pragmas in the wrong order gave 10 pairs, one block gave 8.
{-# REWRITE inst-id inst-wk inst-• inst-⇈ inst-∀ inst-⇒ #-}
{-# REWRITE comp-idᵣ comp-wk comp-idₗ comp-wk-∙ comp-∙-∙ #-}
{-# REWRITE assoc-l dist-⨟ fold-∙-∙ push #-}

-- With the σ-calculus installed, the functor laws for substitution hold
-- definitionally.  The laws marked `*` are σ-calculus laws.
--! SubFunctorialApply {
sub*-id : T [ idˢ ]ˢ ≡ T
sub*-id = refl

sub*-comp : (T [ η ⨟ˢ η′ ]ˢ) ≡ (T [ η ]ˢ) [ η′ ]ˢ
sub*-comp = refl                -- *
--! }

-- ══════════════ §4  Expressions ════════════════════════════════════
-- UNCHANGED from the original, except that `weaken` is now the
-- CONSTRUCTOR application `T ⇈` instead of the traversal `T [ wkᴿ ]ᴿ`.
--! Weaken
weaken : Type n → Type (1 + n)
weaken T = T ⇈

--! Subzero
_[_]* : Type (1 + n) → Type n → Type n
T [ T′ ]* = T [ T′ ∙ˢ idˢ ]ˢ

--! Ctx
data Ctx : Nat → Set where
  ∅    : Ctx zero
  _▷_  : Ctx n → Type n → Ctx n
  _▷*  : Ctx n → Ctx (1 + n)

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx n

--! Var
data _∋_ : Ctx n → Type n → Set where
  zero  : (Γ ▷ T) ∋ T
  suc   : Γ ∋ T → (Γ ▷ T′) ∋ T
  suc*  : Γ ∋ T → (Γ ▷*) ∋ weaken T

variable
  x x′ x₁ x₂ x₃ : Γ ∋ T

--! Expr >
--! Definition
data Expr (Γ : Ctx n) : Type n → Set where
  `_    : Γ ∋ T →
          Expr Γ T
  λx    : Expr (Γ ▷ T₁) T₂ →
          Expr Γ (T₁ ⇒ T₂)
  _·_   : Expr Γ (T₁ ⇒ T₂) →
          Expr Γ T₁ →
          Expr Γ T₂
  Λα    : Expr (Γ ▷*) T →
          Expr Γ (∀α T)
  _·*_  : Expr Γ (∀α T) →
          (T′ : Type n) →
          Expr Γ (T [ T′ ]*)

variable
  e e′ e₁ e₁′ e₂ e₂′ e₃ : Expr Γ T

-- ══════════════ §5  Renaming and substitution on expressions ═══════
-- The expression-level RENAMING LAYER IS KEPT (stage 1 changes the type
-- level only).  It can no longer be indexed by a type-level renaming,
-- because there is no type-level renaming sort any more, so it is
-- indexed by a type-level SUBSTITUTION.  That is the one forced edit.

--! Renaming
_∣_⇒ᴿ_ : Sub n₁ n₂ → Ctx n₁ → Ctx n₂ → Set
η ∣ Γ₁ ⇒ᴿ Γ₂ = ∀ T → (x : Γ₁ ∋ T) → Γ₂ ∋ (T [ η ]ˢ)

variable
  ρ ρ′ ρ₁ ρ₂ ρ₃ : η ∣ Γ₁ ⇒ᴿ Γ₂

--! Ren >
opaque
  --! Idr
  Idᴿ : idˢ ∣ Γ ⇒ᴿ Γ
  Idᴿ _ x = x

  --! Weakening
  Wkᴿ : ∀ T → idˢ ∣ Γ ⇒ᴿ (Γ ▷ T)
  Wkᴿ _ _ = suc

  --! TWeakening
  wkᴿ* : ((idˢ {n}) ⇈ˢ) ∣ Γ ⇒ᴿ (Γ ▷*)
  wkᴿ* _ x = suc* x

  --! Composition
  _,_∣_⨾ᴿ_ : ∀ η₁ η₂ → η₁ ∣ Γ₁ ⇒ᴿ Γ₂ → η₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (η₁ ⨟ˢ η₂) ∣ Γ₁ ⇒ᴿ Γ₃
  (_ , _ ∣ ρ₁ ⨾ᴿ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

  --! Extension
  _∣_∙ᴿ_ : ∀ η → Γ₂ ∋ (T [ η ]ˢ) → η ∣ Γ₁ ⇒ᴿ Γ₂ → η ∣ (Γ₁ ▷ T) ⇒ᴿ Γ₂
  (_ ∣ x ∙ᴿ ρ) _ zero     = x
  (_ ∣ _ ∙ᴿ ρ) _ (suc x)  = ρ _ x

  _∣_∙ᴿ*_ : ∀ η T → η ∣ Γ₁ ⇒ᴿ Γ₂ → (T ∙ˢ η) ∣ (Γ₁ ▷*) ⇒ᴿ Γ₂
  (_ ∣ _ ∙ᴿ* ρ) _ (suc* x) = ρ _ x

  --! Lookup
  _∣_&ᴿ_ : ∀ η → Γ₁ ∋ T → η ∣ Γ₁ ⇒ᴿ Γ₂ → Γ₂ ∋ (T [ η ]ˢ)
  η ∣ x &ᴿ ρ = ρ _ x

_⨾ᴿ_ : η₁ ∣ Γ₁ ⇒ᴿ Γ₂ → η₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (η₁ ⨟ˢ η₂) ∣ Γ₁ ⇒ᴿ Γ₃
_⨾ᴿ_ {η₁ = η₁} {η₂ = η₂} ρ₁ ρ₂ = (η₁ , η₂ ∣ ρ₁ ⨾ᴿ ρ₂)

--! Lifting
opaque
  _∣_⇑ᴿ_ : ∀ η → η ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → η ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ η ]ˢ))
  (η ∣ ρ ⇑ᴿ _) = η ∣ zero ∙ᴿ (η , idˢ ∣ ρ ⨾ᴿ (Wkᴿ _))

  --! TLifting
  -- directly on suc*: the index equation
  --   (weaken T) [ η ↑ˢ ]ˢ ≡ weaken (T [ η ]ˢ)
  -- i.e.  (T ⇈) [ • ∙ˢ (η ⇈ˢ) ]ˢ ≡ (T [ η ]ˢ) ⇈,  which is now two
  -- defining clauses of _[_]ˢ and NO rewrite rule at all.
  _∣_↑ᴿ* : ∀ η → η ∣ Γ₁ ⇒ᴿ Γ₂ → (η ↑ˢ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
  (η ∣ ρ ↑ᴿ*) _ (suc* x) = suc* (ρ _ x)

_⇑ᴿ_ : η ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → η ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ η ]ˢ))
_⇑ᴿ_ {η = η} = η ∣_⇑ᴿ_

↑ᴿ*_ : η ∣ Γ₁ ⇒ᴿ Γ₂ → (η ↑ˢ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
↑ᴿ*_ {η = η} = η ∣_↑ᴿ*


--! Traversal
-- ┌──────────────────────────────────────────────────────────────────┐
-- │ THE OBSTRUCTION.  The expression-level traversal of SystemF.agda  │
-- │ is copied here VERBATIM and does not typecheck.  Uncomment to     │
-- │ reproduce; Agda 2.8.0 reports, on the λx clause,                  │
-- │                                                                   │
-- │   error: [UnequalTerms]                                           │
-- │   _T₁_945 ⇒ _T₂_946 != (T₁ ⇒ T₂) [ η ]ˢ of type Type n₂           │
-- │   when checking that the inferred type of an application          │
-- │     Expr Γ₂ (_T₁_945 ⇒ _T₂_946)                                   │
-- │   matches the expected type                                       │
-- │     Expr Γ₂ ((T₁ ⇒ T₂) [ η ]ˢ)                                    │
-- └──────────────────────────────────────────────────────────────────┘
-- _∣_[_]ᴿ : (η : Sub n₁ n₂) → Expr Γ₁ T → η ∣ Γ₁ ⇒ᴿ Γ₂ → Expr Γ₂ (T [ η ]ˢ)
-- η  ∣ (` x) [ ρ ]ᴿ      = ` (η ∣ x &ᴿ ρ)
-- _  ∣ (λx e) [ ρ ]ᴿ     = λx (_ ∣ e [ ρ ⇑ᴿ _ ]ᴿ)          -- ← fails here
-- _  ∣ (Λα e) [ ρ ]ᴿ     = Λα (_ ∣ e [ ↑ᴿ* ρ ]ᴿ)
-- _  ∣ (e₁ · e₂) [ ρ ]ᴿ  = (_ ∣ e₁ [ ρ ]ᴿ) · (_ ∣ e₂ [ ρ ]ᴿ)
-- η  ∣ (e ·* T′) [ ρ ]ᴿ  = (η ∣ e [ ρ ]ᴿ) ·* (T′ [ η ]ˢ)

-- ══════════════ §6  Probes ═════════════════════════════════════════
-- What the type level still gives the (unchanged) expression level,
-- and what it has stopped giving.  Everything in this section is
-- machine-checked: the file typechecks, so every `refl` below really
-- is a definitional equality and every `no-…` really is a refutation.

open import Relation.Nullary using (¬_)

-- ── WHAT STILL HOLDS ───────────────────────────────────────────────
-- These are the type-level equations the expression level asks for,
-- and here they hold with NO rewrite rule at all — they are defining
-- clauses of `_[_]ˢ`.  In SystemF.agda each needed a named rule.

-- identityᵣ / identityᵣˢ  (was: two registered rules)
probe-id : (T : Type n) → T [ idˢ ]ˢ ≡ T
probe-id T = refl

-- the `_∣_↑ᴿ*` obligation: (weaken T) [ η ↑ˢ ]ˢ ≡ weaken (T [ η ]ˢ)
-- SystemF.agda needed  compositionalityᴿˢ + lift-wk + coincidence.
probe-wk-lift : (T : Type n₁) (η : Sub n₁ n₂) → (T ⇈) [ η ↑ˢ ]ˢ ≡ (T [ η ]ˢ) ⇈
probe-wk-lift T η = refl

-- the `_∣_∙ˢ*_` obligation: (weaken T) [ T′ ∙ˢ η ]ˢ ≡ T [ η ]ˢ
-- SystemF.agda needed  compositionalityᴿˢ + interact.  This is
-- Wadler's headline equation (his `introduction`, one level up).
probe-interact : (T : Type n₁) (T′ : Type n₂) (η : Sub n₁ n₂) →
                 (T ⇈) [ T′ ∙ˢ η ]ˢ ≡ T [ η ]ˢ
probe-interact T T′ η = refl

-- compositionality, in both directions (the one registered rule)
probe-comp : (T : Type n₁) (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) →
             (T [ η₁ ]ˢ) [ η₂ ]ˢ ≡ T [ η₁ ⨟ˢ η₂ ]ˢ
probe-comp T η₁ η₂ = refl

-- lift fusion, definitional here (SystemF.agda: `lift-fusion`, a rule
-- whose proof is a 6-line ≡-Reasoning chain)
probe-lift-fusion : (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) →
                    (η₁ ↑ˢ) ⨟ˢ (η₂ ↑ˢ) ≡ (η₁ ⨟ˢ η₂) ↑ˢ
probe-lift-fusion η₁ η₂ = refl

-- ── WHAT HAS STOPPED HOLDING ───────────────────────────────────────
-- Each of the three below is the equation some clause of the
-- expression level needs.  Each is REFUTED, not merely unproved.

-- (1) the λx clause of the traversal.  Needed:
--       (T₁ ⇒ T₂) [ η ]ˢ ≡ (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)   for all η.
-- It holds for η = idˢ and for η = T ∙ˢ η′ …
probe-⇒-id : (T₁ T₂ : Type n) → (T₁ ⇒ T₂) [ idˢ ]ˢ ≡ (T₁ [ idˢ ]ˢ) ⇒ (T₂ [ idˢ ]ˢ)
probe-⇒-id T₁ T₂ = refl

probe-⇒-cons : (T₁ T₂ : Type (1 + n₁)) (T : Type n₂) (η : Sub n₁ n₂) →
               (T₁ ⇒ T₂) [ T ∙ˢ η ]ˢ ≡ (T₁ [ T ∙ˢ η ]ˢ) ⇒ (T₂ [ T ∙ˢ η ]ˢ)
probe-⇒-cons T₁ T₂ T η = refl

-- … and FAILS for η = η′ ⇈ˢ, where it reduces to `push-⇈-⇒`:
--   probe-⇒-wk : (T₁ T₂ : Type n₁) (η : Sub n₁ n₂) →
--                (T₁ ⇒ T₂) [ η ⇈ˢ ]ˢ ≡ (T₁ [ η ⇈ˢ ]ˢ) ⇒ (T₂ [ η ⇈ˢ ]ˢ)
--   probe-⇒-wk T₁ T₂ η = refl
-- error: [UnequalTerms]
--   ((T₁ ⇒ T₂) [ η ]ˢ) ⇈ != (T₁ [ η ⇈ˢ ]ˢ) ⇒ (T₂ [ η ⇈ˢ ]ˢ)
--   of type Type (suc n₂)

-- (2) the repair rule, REFUTED.  This is the exact statement that
--     tex/cpp27/main.tex calls "lost and unrecoverable".  It is worse
--     than unrecoverable: it is false.
no-push-⇈-⇒ : (T₁ T₂ : Type n) → ¬ ((T₁ ⇒ T₂) ⇈ ≡ (T₁ ⇈) ⇒ (T₂ ⇈))
no-push-⇈-⇒ T₁ T₂ ()

no-push-⇈-∀ : (T : Type (1 + n)) → ¬ ((∀α T) ⇈ ≡ ∀α (T [ • ∙ˢ ((idˢ ⇈ˢ) ⇈ˢ) ]ˢ))
no-push-⇈-∀ T ()

-- (3) the `_·*_` clause of the traversal needs `distributivity`,
--     which SystemF.agda registers.  It fails here — but READ THE NEXT
--     PARAGRAPH before quoting this as a refutation of explicit
--     weakening, because unlike (1) and (2) it is DEFINITION-RELATIVE.
--
--     (1) and (2) are ABSOLUTE.  Both sides of each are pure
--     constructor applications of `Type`; `_⇈` against `_⇒_`, and `_⇈`
--     against `∀α`.  No defined symbol occurs on either side, so no
--     choice of definition can change the verdict.  They follow from
--     the decision to make weakening a constructor, and from nothing
--     else.
--
--     (3) is not like that.  Its left-hand side is an application of
--     the DEFINED symbol `_⨟ˢ_`, and what it reduces to is our choice.
--     What is forced is only a CONSTRUCTOR CLASH: at
--     `(T ∙ˢ η₁) ⨟ˢ (η₂ ⇈ˢ)` the composition must commit to a head
--     constructor of `Sub`, `_∙ˢ_` or `_⇈ˢ_`, and cannot be both,
--     because `Sub` is a DATATYPE and extensionally equal substitutions
--     need not be equal.  Wadler's clause (2) commits to `_⇈ˢ`, so
--     distributivity is refuted, as below.  MEASURED (report.md §4.3,
--     scratchpad `x/D1.agda`, EXIT=0): defining `_⨟ˢ_` by recursion on
--     its LEFT argument instead, with the cons clause distributing
--     unconditionally, makes distributivity hold by `refl` — and
--     REFUTES both Wadler's clause (2) and the RIGHT IDENTITY
--     `η ⨟ˢ idˢ ≡ η`, the law he advertises as holding by definition.
--     That is a trade, not a win: the right identity is a monoid law,
--     the direction of clause (2) is a normal-form choice.  We keep
--     Wadler's, and recover distributivity in the CONTINUED form as
--     `dist-⨟` (§3), where the right factor is a cons rather than an
--     abstract substitution and the clash does not arise.
no-distributivity : (T : Type n₂) (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) →
  ¬ ((T ∙ˢ η₁) ⨟ˢ (η₂ ⇈ˢ) ≡ (T [ η₂ ⇈ˢ ]ˢ) ∙ˢ (η₁ ⨟ˢ (η₂ ⇈ˢ)))
no-distributivity T η₁ η₂ ()

-- ── COUPLING PROBES ────────────────────────────────────────────────
-- The equations SystemF-strat.agda, SystemF-binary.agda and
-- SystemF-adequacy.agda actually depend on, at the type level.
-- Names in brackets are the SystemF.agda rules that used to deliver
-- them.  These are the ones that decide whether the change is viable.

-- [compositionalityˢˢ ∘ lift-cons ∘ comp-idᵣ]  THE transfer lemma:
-- the ∀-elimination step of every logical relation in all three files
-- (strat §⟦∀α⟧, binary ⟦∀α⟧², adequacy 𝓥⟦∀α⟧ — their `lemma1`).
probe-transfer : (T : Type (1 + n₁)) (S : Type n₂) (η : Sub n₁ n₂) →
                 (T [ η ↑ˢ ]ˢ) [ S ]* ≡ T [ S ∙ˢ η ]ˢ
probe-transfer T S η = refl

-- [beta-ext-zero] and [interact]: the Env/𝓖 environment split
probe-ext-zero : (S : Type n₂) (η : Sub n₁ n₂) → • [ S ∙ˢ η ]ˢ ≡ S
probe-ext-zero S η = refl

probe-tail : (S : Type n₂) (η : Sub n₁ n₂) → (idˢ ⇈ˢ) ⨟ˢ (S ∙ˢ η) ≡ η
probe-tail S η = refl

-- [compositionalityᴿˢ]  adequacy's `Cdrop-t`, strat's `Reds` suc*-clause.
-- HOLDS, and it is `push` that delivers it: the right-hand side pushes
-- to `(T [ idˢ ⇈ˢ ]ˢ) [ η ]ˢ`, which inst-wk and inst-id turn into the
-- left-hand side.  Under the FOLD orientation of the previous rule set
-- both sides were stuck and this probe failed.  (The version commented
-- out in the previous revision of this file was ill-typed as written —
-- `(idˢ ⇈ˢ) ⨟ˢ η` needs `η : Sub (1 + n₁) n₂` — so it had never been run.)
probe-Cdrop : ∀ {m₁ m₂} (S : Type m₁) (γ : Sub (1 + m₁) m₂) →
              (S ⇈) [ γ ]ˢ ≡ S [ (idˢ ⇈ˢ) ⨟ˢ γ ]ˢ
probe-Cdrop S γ = refl

-- [compositionalityˢˢ ∘ distributivity ∘ comp-idₗ]  the `_·*_` clause of
-- the expression traversal, and adequacy's `semantic-soundness (e ·* T′)`.
-- STILL FAILS, but not for the reason the previous revision gave.  The
-- right-hand side is fine: it NORMALISES, by fold-∙-∙ and the C-rules, to
--   S [ (S′ [ γ ]ˢ) ∙ˢ γ ]ˢ          -- machine-checked, see below
-- The left-hand side is the stuck one: `(S [ S′ ∙ˢ idˢ ]ˢ) [ γ ]ˢ` with γ
-- abstract, which no rule can touch, and reaching the right-hand side from
-- it is exactly BARE distributivity `(S′ ∙ˢ idˢ) ⨟ˢ γ ≡ (S′ [ γ ]ˢ) ∙ˢ γ`.
--   probe-·* : ∀ {m₁ m₂} (S : Type (1 + m₁)) (S′ : Type m₁) (γ : Sub m₁ m₂) →
--              (S [ S′ ]*) [ γ ]ˢ ≡ (S [ γ ↑ˢ ]ˢ) [ S′ [ γ ]ˢ ]*
--   probe-·* S S′ γ = refl
-- error: [UnequalTerms] m₁ != suc m₁ of type Nat
--   when checking that the expression refl has type
--     ((S [ S′ ]*) [ γ ]ˢ) ≡ ((S [ γ ↑ˢ ]ˢ) [ S′ [ γ ]ˢ ]*)

-- the half of it that DOES hold, and that locates the failure precisely
probe-·*-rhs : ∀ {m₁ m₂} (S : Type (1 + m₁)) (S′ : Type m₁) (γ : Sub m₁ m₂) →
               (S [ γ ↑ˢ ]ˢ) [ S′ [ γ ]ˢ ]* ≡ S [ (S′ [ γ ]ˢ) ∙ˢ γ ]ˢ
probe-·*-rhs S S′ γ = refl
