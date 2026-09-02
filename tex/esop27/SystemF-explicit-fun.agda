-- ════════════════════════════════════════════════════════════════════
-- THE THIRD VARIANT.  Explicit weakening, substitutions as FUNCTIONS,
-- and the σ⇑ calculus of Hardin, Maranget & Pagano (JFP 8(2) 1998,
-- figs. 1-2) registered over it.  Companion to
-- SystemF-explicit-type.agda and SystemF-explicit.agda.
--
-- WHY IT EXISTS.  Those two files vary TWO things against SystemF.agda
-- at once: weakening becomes a constructor of `Type`, AND `Sub` becomes
-- an inductive type (Wadler's design).  This file varies only the
-- first.  `Type` keeps `_⇈`; `Sub n₁ n₂ = Var n₁ → Type n₂`, modelled
-- exactly as SystemF.agda models it, with `fun-ext` the only postulate.
--
-- CURRENT STATUS:
--
--   $ agda --library=standard-library -i. SystemF-explicit-fun.agda
--   EXIT=0  —  ZERO non-joinable critical pairs.
--
--   26 rules, --rewriting --local-confluence-check, Agda 2.8.0.
--
-- WHAT THE ANSWER IS.
--
--   (1) The representation FORCES type-first instantiation.  A function
--       cannot be case-analysed, so Wadler's clause
--       `T [ η ⇈ˢ ]ˢ = (T [ η ]ˢ) ⇈` is not even expressible.  The
--       substitution-first horn of the other two files simply does not
--       exist here.
--
--   (2) The prize of explicit weakening SURVIVES: `_[_]ˢ` is
--       structurally recursive on the type, `_↑ˢ` weakens a
--       substitution with the CONSTRUCTOR `_⇈` pointwise, and there is
--       no renaming sort and no {-# TERMINATING #-}.
--
--   (3) The two ABSOLUTE refutations SURVIVE, as expected and now
--       measured: `no-push-⇈-⇒` and `no-push-⇈-∀` in §6.  They are
--       statements about `Type` constructors alone; no substitution
--       occurs on either side, so the representation of `Sub` cannot
--       reach them.
--
--   (4) The function model does REMOVE two obstructions of the
--       inductive model (§7): the λx and Λα clauses of the expression
--       traversal hold by `refl` at an ABSTRACT substitution, and
--       σ⇑'s LiftId holds, which the inductive model refutes.
--
--   (5) And it ADDS obstructions the inductive model did not have.
--       SEVEN σ⇑ rules are REFUTED here (§5), among them the MONAD LAW:
--         Id, VarShift1, IdR, Clos, AssEnv, Lift1, Lift2.
--       `SystemF-explicit-type.agda` has Clos, Id, IdR and AssEnv all
--       definitional.  So the inductive representation is what RESCUES
--       the σ-calculus laws, at the price of the traversal; the
--       function representation gives up the laws to get the traversal.
--
--   Conclusion for the paper: the obstruction is caused by EXPLICIT
--   WEAKENING itself — by `_⇈` applying to any type rather than only to
--   a variable — and not by Wadler's inductive `Sub`.  Changing the
--   representation moves which laws are lost; it does not recover them.
--
-- MEASURED control matrix (report.md §8.4):
--   this file ......................................... 0 pairs, EXIT=0
--   MapEnv and LiftEnv registered as well ............. 2 pairs
--   Clos-at-V FOLDED instead of pushed ................ 6 pairs
--   each of those, flag removed ....................... nothing reported
-- ════════════════════════════════════════════════════════════════════
{-# OPTIONS --rewriting --local-confluence-check #-}
module SystemF-explicit-fun where
open import Agda.Builtin.Equality.Rewrite public

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans)
open import Relation.Nullary using (¬_)
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin using (zero; suc) renaming (Fin to Var)

infixr 5 _⇒_
infixr 6 _∙ˢ_
infix 8 _⇈

-- ══════════════ §1  Types: explicit weakening, UNCHANGED ═══════════
data Type : Nat → Set where
  •    : ∀ {n} → Type (1 + n)
  _⇈   : ∀ {n} → Type n → Type (1 + n)
  ∀α   : ∀ {n} → Type (1 + n) → Type n
  _⇒_  : ∀ {n} → Type n → Type n → Type n

variable
  n n′ n₁ n₂ n₃ : Nat
  x x′ x₁ x₂ : Var n
  T T′ T″ T₁ T₂ T₃ : Type n

-- de Bruijn index k as `•` under k weakenings
var : Var n → Type n
var zero     = •
var (suc x)  = (var x) ⇈

-- ══════════════ §2  Substitutions as FUNCTIONS ═════════════════════
Sub : Nat → Nat → Set
Sub n₁ n₂ = Var n₁ → Type n₂

variable
  σ σ′ σ₁ σ₂ σ₃ τ τ′ υ : Sub n₁ n₂

opaque
  _&ˢ_ : Var n₁ → Sub n₁ n₂ → Type n₂
  x &ˢ σ = σ x

  idˢ : Sub n n
  idˢ = var

  wkˢ : Sub n (1 + n)
  wkˢ x = (var x) ⇈

  _∙ˢ_ : Type n₂ → Sub n₁ n₂ → Sub (1 + n₁) n₂
  (T ∙ˢ σ) zero     = T
  (T ∙ˢ σ) (suc x)  = σ x

  tailˢ : Sub (1 + n₁) n₂ → Sub n₁ n₂
  tailˢ σ x = σ (suc x)

  _⇈ˢ : Sub n₁ n₂ → Sub n₁ (1 + n₂)
  (σ ⇈ˢ) x = (σ x) ⇈

-- lifting: FIRST-CLASS (σ⇑ decision 1), and it needs NO renaming —
-- weakening a substitution is `_⇈ˢ`, which is `_⇈` pointwise, O(1)
opaque
  _↑ˢ : Sub n₁ n₂ → Sub (1 + n₁) (1 + n₂)
  _↑ˢ σ = • ∙ˢ (σ ⇈ˢ)

-- instantiation MUST recurse on the TYPE: a substitution is a function
-- and cannot be case-analysed.  This is forced by the representation.
opaque
  unfolding _&ˢ_ tailˢ

  _[_]ˢ : Type n₁ → Sub n₁ n₂ → Type n₂
  •          [ σ ]ˢ = zero &ˢ σ
  (T ⇈)      [ σ ]ˢ = T [ tailˢ σ ]ˢ
  (∀α T)     [ σ ]ˢ = ∀α (T [ σ ↑ˢ ]ˢ)
  (T₁ ⇒ T₂)  [ σ ]ˢ = (T₁ [ σ ]ˢ) ⇒ (T₂ [ σ ]ˢ)

opaque
  unfolding _[_]ˢ
  _⨟ˢ_ : Sub n₁ n₂ → Sub n₂ n₃ → Sub n₁ n₃
  (σ ⨟ˢ τ) x = (σ x) [ τ ]ˢ

-- ══════════════ §3  The σ⇑ calculus, rule by rule ══════════════════
opaque
  unfolding _&ˢ_ idˢ wkˢ _∙ˢ_ tailˢ _⇈ˢ _↑ˢ _[_]ˢ _⨟ˢ_

  -- ── lookup (the V level) ────────────────────────────────────────
  &-∙-zero  : zero &ˢ (T ∙ˢ σ) ≡ T                                -- σw FVar
  &-∙-suc   : (suc x) &ˢ (T ∙ˢ σ) ≡ x &ˢ σ                        -- σw RVar
  &-↑-zero  : zero &ˢ (σ ↑ˢ) ≡ •                                  -- σ⇑ FVarLift1
  &-↑-suc   : (suc x) &ˢ (σ ↑ˢ) ≡ (x &ˢ σ) ⇈                      -- σ⇑ RVarLift1, ⇈-form
  &-⇈       : x &ˢ (σ ⇈ˢ) ≡ (x &ˢ σ) ⇈                            -- NEW
  &-tail    : x &ˢ (tailˢ σ) ≡ (suc x) &ˢ σ                       -- NEW
  &-id-zero : zero &ˢ (idˢ {1 + n}) ≡ •                           -- σ⇑ Id at V
  &-id-suc  : (suc x) &ˢ idˢ ≡ (x &ˢ idˢ) ⇈                       -- σ⇑ Id at V
  &-wk      : x &ˢ wkˢ ≡ (x &ˢ idˢ) ⇈                             -- σ⇑ VarShift1, ⇈-form
  &-∙-zero  = refl
  &-∙-suc   = refl
  &-↑-zero  = refl
  &-↑-suc   = refl
  &-⇈       = refl
  &-tail    = refl
  &-id-zero = refl
  &-id-suc  = refl
  &-wk      = refl

  -- ── traversal ────────────────────────────────────────────────────
  inst-• : • [ σ ]ˢ ≡ zero &ˢ σ                                   -- V/T injection
  inst-⇈ : (T ⇈) [ σ ]ˢ ≡ T [ tailˢ σ ]ˢ                          -- NEW: explicit weakening
  inst-∀ : (∀α T) [ σ ]ˢ ≡ ∀α (T [ σ ↑ˢ ]ˢ)                       -- σ⇑ Lambda
  inst-⇒ : (T₁ ⇒ T₂) [ σ ]ˢ ≡ (T₁ [ σ ]ˢ) ⇒ (T₂ [ σ ]ˢ)           -- σw App
  inst-• = refl
  inst-⇈ = refl
  inst-∀ = refl
  inst-⇒ = refl

  -- ── the tail algebra (NEW: no σ⇑ counterpart) ────────────────────
  tail-∙  : tailˢ (T ∙ˢ σ) ≡ σ
  tail-↑  : tailˢ (σ ↑ˢ) ≡ σ ⇈ˢ
  tail-⇈  : tailˢ (σ ⇈ˢ) ≡ (tailˢ σ) ⇈ˢ
  tail-id : tailˢ (idˢ {1 + n}) ≡ wkˢ
  tail-wk : tailˢ (wkˢ {1 + n}) ≡ wkˢ ⇈ˢ
  wk-⇈    : (idˢ {n}) ⇈ˢ ≡ wkˢ
  tail-∙  = fun-ext λ _ → refl
  tail-↑  = fun-ext λ _ → refl
  tail-⇈  = fun-ext λ _ → refl
  tail-id = fun-ext λ _ → refl
  tail-wk = fun-ext λ _ → refl
  wk-⇈    = fun-ext λ _ → refl

  -- ── the lemma every map law goes through ─────────────────────────
  var-lookup : (y : Var n₁) (ρ : Sub n₁ n₂) → (y &ˢ idˢ) [ ρ ]ˢ ≡ y &ˢ ρ
  var-lookup zero    ρ = refl
  var-lookup (suc y) ρ = var-lookup y (tailˢ ρ)

  -- ── FOLD AT V (TRS.md decision 3, mirrored) ──────────────────────
  comp-var  : ∀ {n₁ n₂ n₃} (y : Var n₁) (ρ : Sub n₁ n₂) (τ : Sub n₂ n₃) →
              y &ˢ (ρ ⨟ˢ τ) ≡ (y &ˢ ρ) [ τ ]ˢ                     -- σ⇑ Clos at V, PUSHED
  comp-var y ρ τ = refl

  lookup-id : ∀ {n₁ n₂} (y : Var n₁) (τ : Sub n₁ n₂) →
              (y &ˢ idˢ) [ τ ]ˢ ≡ y &ˢ τ                          -- NEW (var-lookup)
  lookup-id = var-lookup

  comp-tail : ∀ {n₁ n₂ n₃} (ρ : Sub (1 + n₁) n₂) (τ : Sub n₂ n₃) →
              (tailˢ ρ) ⨟ˢ τ ≡ tailˢ (ρ ⨟ˢ τ)                     -- NEW
  comp-tail ρ τ = fun-ext λ _ → refl

  comp-⇈ˢ : ∀ {n₁ n₂ n₃} (ρ : Sub n₁ n₂) (τ : Sub (1 + n₂) n₃) →
            (ρ ⇈ˢ) ⨟ˢ τ ≡ ρ ⨟ˢ (tailˢ τ)                          -- NEW
  comp-⇈ˢ ρ τ = fun-ext λ _ → refl

  tail-↑-⨟ : ∀ {n₁ n₂ n₃} (ρ : Sub n₁ n₂) (τ : Sub (1 + n₂) n₃) →
             tailˢ ((ρ ↑ˢ) ⨟ˢ τ) ≡ ρ ⨟ˢ (tailˢ τ)                 -- σ⇑ ShiftLift2 shape
  tail-↑-⨟ ρ τ = fun-ext λ _ → refl

  -- ── σw fig. 1 / σ⇑ fig. 2 map algebra ────────────────────────────
  IdL       : idˢ ⨟ˢ σ ≡ σ                                        -- σw IdL
  IdL {σ = σ} = fun-ext λ y → var-lookup y σ

  MapEnv    : (T ∙ˢ σ) ⨟ˢ τ ≡ (T [ τ ]ˢ) ∙ˢ (σ ⨟ˢ τ)              -- σw MapEnv
  MapEnv = fun-ext λ { zero → refl ; (suc _) → refl }

  LiftEnv   : (σ ↑ˢ) ⨟ˢ (T ∙ˢ τ) ≡ T ∙ˢ (σ ⨟ˢ τ)                  -- σ⇑ LiftEnv
  LiftEnv = fun-ext λ { zero → refl ; (suc _) → refl }

  LiftId    : (idˢ {n}) ↑ˢ ≡ idˢ                                  -- σ⇑ LiftId
  LiftId = fun-ext λ { zero → refl ; (suc _) → refl }

  VarShift2 : ∀ {n₁ n₂} (ρ : Sub (1 + n₁) n₂) → wkˢ ⨟ˢ ρ ≡ tailˢ ρ  -- σ⇑ VarShift2
  VarShift2 ρ = fun-ext λ y → var-lookup y (tailˢ ρ)

  FVarLift2 : ∀ {n₁ n₂ n₃} (ρ : Sub n₁ n₂) (τ : Sub (1 + n₂) n₃) →
              zero &ˢ ((ρ ↑ˢ) ⨟ˢ τ) ≡ zero &ˢ τ                   -- σ⇑ FVarLift2
  FVarLift2 ρ τ = refl

  RVarLift2 : ∀ {n₁ n₂ n₃} (y : Var n₁) (ρ : Sub n₁ n₂) (τ : Sub (1 + n₂) n₃) →
              (suc y) &ˢ ((ρ ↑ˢ) ⨟ˢ τ) ≡ y &ˢ (ρ ⨟ˢ (tailˢ τ))    -- σ⇑ RVarLift2
  RVarLift2 y ρ τ = refl

  -- ── stated for the record, PROVED, subsumption measured in §4 ────
  ShiftCons  : wkˢ ⨟ˢ (T ∙ˢ σ) ≡ σ                                -- σw ShiftCons
  ShiftCons {T = T} {σ = σ} = fun-ext λ y → var-lookup y σ

  ShiftLift1 : ∀ {n₁ n₂} (ρ : Sub n₁ n₂) → wkˢ ⨟ˢ (ρ ↑ˢ) ≡ ρ ⇈ˢ   -- σ⇑ ShiftLift1, ⇈ˢ-form
  ShiftLift1 ρ = fun-ext λ y → var-lookup y (tailˢ (ρ ↑ˢ))

  ShiftLift2 : ∀ {n₁ n₂ n₃} (ρ : Sub n₁ n₂) (τ : Sub (1 + n₂) n₃) →
               wkˢ ⨟ˢ ((ρ ↑ˢ) ⨟ˢ τ) ≡ ρ ⨟ˢ (tailˢ τ)              -- σ⇑ ShiftLift2
  ShiftLift2 ρ τ = fun-ext λ y → var-lookup y (tailˢ ((ρ ↑ˢ) ⨟ˢ τ))

  def-↑ˢ : ∀ {n₁ n₂} (ρ : Sub n₁ n₂) → ρ ↑ˢ ≡ • ∙ˢ (ρ ⇈ˢ)         -- Abadi/AS2, a lemma
  def-↑ˢ ρ = fun-ext λ { zero → refl ; (suc _) → refl }

-- ── ORDER: lookup, traversal, tail algebra, map algebra ───────────
{-# REWRITE &-∙-zero &-∙-suc &-↑-zero &-↑-suc &-⇈ &-tail #-}
{-# REWRITE &-id-zero &-id-suc &-wk #-}
{-# REWRITE inst-• inst-⇈ inst-∀ inst-⇒ #-}
{-# REWRITE tail-∙ tail-↑ tail-⇈ tail-id tail-wk wk-⇈ #-}
{-# REWRITE IdL LiftId VarShift2 #-}
{-# REWRITE comp-var lookup-id comp-⇈ˢ tail-↑-⨟ #-}

-- ══════════════ §4  SUBSUMED σ⇑ rules (MEASURED by refl) ═══════════
-- Proved in §3 and NOT registered: the rules above already reach the
-- same normal form, so registering them would add nothing.
sub-ShiftCons : ∀ {n₁ n₂} (T : Type n₂) (ρ : Sub n₁ n₂) → wkˢ ⨟ˢ (T ∙ˢ ρ) ≡ ρ
sub-ShiftCons T ρ = refl                                          -- σw ShiftCons

sub-FVarLift1 : ∀ {n₁ n₂} (ρ : Sub n₁ n₂) → zero &ˢ (ρ ↑ˢ) ≡ •
sub-FVarLift1 ρ = refl                                            -- σ⇑ FVarLift1

sub-FVarLift2 : ∀ {n₁ n₂ n₃} (ρ : Sub n₁ n₂) (τ : Sub (1 + n₂) n₃) →
                zero &ˢ ((ρ ↑ˢ) ⨟ˢ τ) ≡ zero &ˢ τ
sub-FVarLift2 ρ τ = refl                                          -- σ⇑ FVarLift2

sub-RVarLift2 : ∀ {n₁ n₂ n₃} (y : Var n₁) (ρ : Sub n₁ n₂) (τ : Sub (1 + n₂) n₃) →
                (suc y) &ˢ ((ρ ↑ˢ) ⨟ˢ τ) ≡ y &ˢ (ρ ⨟ˢ (tailˢ τ))
sub-RVarLift2 y ρ τ = refl                                        -- σ⇑ RVarLift2

sub-ShiftLift1 : ∀ {n₁ n₂} (ρ : Sub n₁ n₂) → wkˢ ⨟ˢ (ρ ↑ˢ) ≡ ρ ⇈ˢ
sub-ShiftLift1 ρ = refl                                           -- σ⇑ ShiftLift1, ⇈ˢ-form

sub-ShiftLift2 : ∀ {n₁ n₂ n₃} (ρ : Sub n₁ n₂) (τ : Sub (1 + n₂) n₃) →
                 wkˢ ⨟ˢ ((ρ ↑ˢ) ⨟ˢ τ) ≡ ρ ⨟ˢ (tailˢ τ)
sub-ShiftLift2 ρ τ = refl                                         -- σ⇑ ShiftLift2

-- MapEnv and LiftEnv are PROVED (§3) but NOT registered: with the fold
-- at V they are registrable and σ⇑'s 2-rules then clash with Clos-at-V;
-- with the push they clash directly.  This is TRS.md §2.1's asymmetry,
-- and here there is no second world to keep the other choice in.
-- They hold POINTWISE at every concrete index:
sub-MapEnv-zero : ∀ {n₁ n₂ n₃} (T : Type n₂) (ρ : Sub n₁ n₂) (τ : Sub n₂ n₃) →
                  zero &ˢ ((T ∙ˢ ρ) ⨟ˢ τ) ≡ zero &ˢ ((T [ τ ]ˢ) ∙ˢ (ρ ⨟ˢ τ))
sub-MapEnv-zero T ρ τ = refl
sub-MapEnv-suc : ∀ {n₁ n₂ n₃} (y : Var n₁) (T : Type n₂) (ρ : Sub n₁ n₂) (τ : Sub n₂ n₃) →
                 (suc y) &ˢ ((T ∙ˢ ρ) ⨟ˢ τ) ≡ (suc y) &ˢ ((T [ τ ]ˢ) ∙ˢ (ρ ⨟ˢ τ))
sub-MapEnv-suc y T ρ τ = refl

-- ══════════════ §5  The σ⇑ rules that are REFUTED ══════════════════
at : ∀ {n₁ n₂} {ρ τ : Sub n₁ n₂} → ρ ≡ τ → (y : Var n₁) → y &ˢ ρ ≡ y &ˢ τ
at eq y = cong (y &ˢ_) eq

-- σ⇑ **Id**   `M[id] → M`
no-Id : ∀ {n} (T₁ T₂ : Type n) → ¬ (((T₁ ⇒ T₂) ⇈) [ idˢ ]ˢ ≡ ((T₁ ⇒ T₂) ⇈))
no-Id T₁ T₂ ()

-- σ⇑ **VarShift1**  `n[↑] → n+1`, off the variables
no-VarShift1 : ∀ {n} (T₁ T₂ : Type n) → ¬ ((T₁ ⇒ T₂) [ wkˢ ]ˢ ≡ (T₁ ⇒ T₂) ⇈)
no-VarShift1 T₁ T₂ ()

-- σ⇑ **IdR**  `s∘id → s`
no-IdR : ∀ {n} (T₁ T₂ : Type n) (ρ : Sub n n) →
         ¬ ((((T₁ ⇒ T₂) ⇈) ∙ˢ (ρ ⇈ˢ)) ⨟ˢ idˢ ≡ (((T₁ ⇒ T₂) ⇈) ∙ˢ (ρ ⇈ˢ)))
no-IdR T₁ T₂ ρ eq with at eq zero
... | ()

-- σ⇑ **Clos**  `M[s][t] → M[s∘t]` — THE MONAD LAW
no-Clos : ∀ {m n₂ n₃} (T₁ T₂ : Type n₂) (ρ : Sub m n₂) (τ : Sub n₂ n₃) →
          ¬ (((∀α (• ⇈)) [ (T₁ ⇒ T₂) ∙ˢ ρ ]ˢ) [ τ ]ˢ
             ≡ (∀α (• ⇈)) [ ((T₁ ⇒ T₂) ∙ˢ ρ) ⨟ˢ τ ]ˢ)
no-Clos T₁ T₂ ρ τ ()

-- σw **AssEnv**  `(s∘t)∘u → s∘(t∘u)`
no-AssEnv : ∀ {m k n₂ n₃} (T₁ T₂ : Type n₂) (ρ : Sub k n₂) (ρ′ : Sub m (1 + k))
            (υ : Sub n₂ n₃) →
            ¬ ((((∀α (• ⇈)) ∙ˢ ρ′) ⨟ˢ ((T₁ ⇒ T₂) ∙ˢ ρ)) ⨟ˢ υ
               ≡ ((∀α (• ⇈)) ∙ˢ ρ′) ⨟ˢ (((T₁ ⇒ T₂) ∙ˢ ρ) ⨟ˢ υ))
no-AssEnv T₁ T₂ ρ ρ′ υ eq with at eq zero
... | ()

-- σ⇑ **Lift1**  `⇑s∘⇑t → ⇑(s∘t)`
no-Lift1 : ∀ {m n₂ n₃} (T₁ T₂ : Type n₂) (ρ : Sub m n₂) (τ : Sub n₂ n₃) →
           ¬ ((((T₁ ⇒ T₂) ∙ˢ ρ) ↑ˢ) ⨟ˢ (τ ↑ˢ) ≡ (((T₁ ⇒ T₂) ∙ˢ ρ) ⨟ˢ τ) ↑ˢ)
no-Lift1 T₁ T₂ ρ τ eq with at eq (suc zero)
... | ()

-- σ⇑ **Lift2**  `⇑s∘(⇑t∘u) → ⇑(s∘t)∘u` — its `suc` component is a
-- Clos instance, so the same counterexample refutes it
no-Lift2 : ∀ {n₁ m n₃ n₄} (T₁ T₂ : Type n₃) (ρ : Sub n₁ (1 + m))
           (ρ′ : Sub m n₃) (υ : Sub (1 + n₃) n₄) →
           ¬ ((((∀α (• ⇈)) ∙ˢ ρ) ↑ˢ) ⨟ˢ ((((T₁ ⇒ T₂) ∙ˢ ρ′) ↑ˢ) ⨟ˢ υ)
              ≡ ((((∀α (• ⇈)) ∙ˢ ρ) ⨟ˢ ((T₁ ⇒ T₂) ∙ˢ ρ′)) ↑ˢ) ⨟ˢ υ)
no-Lift2 T₁ T₂ ρ ρ′ υ eq with at eq (suc zero)
... | ()

-- ══════════════ §6  The two ABSOLUTE refutations, re-measured ══════
-- They are statements about `Type` constructors only.  No substitution
-- occurs on either side, so the representation of `Sub` cannot touch
-- them — and does not.
no-push-⇈-⇒ : ∀ {n} (T₁ T₂ : Type n) → ¬ ((T₁ ⇒ T₂) ⇈ ≡ (T₁ ⇈) ⇒ (T₂ ⇈))
no-push-⇈-⇒ T₁ T₂ ()

no-push-⇈-∀ : ∀ {n} (T : Type (1 + n)) → ¬ ((∀α T) ⇈ ≡ ∀α (T [ (wkˢ {n}) ↑ˢ ]ˢ))
no-push-⇈-∀ T ()

-- ══════════════ §7  What the function model DOES buy ═══════════════
-- the λx and Λα clauses of the expression traversal, at an ABSTRACT
-- substitution — refuted in SystemF-explicit-type.agda
push-⇒ : ∀ {n₁ n₂} (T₁ T₂ : Type n₁) (ρ : Sub n₁ n₂) →
         (T₁ ⇒ T₂) [ ρ ]ˢ ≡ (T₁ [ ρ ]ˢ) ⇒ (T₂ [ ρ ]ˢ)
push-⇒ T₁ T₂ ρ = refl

push-∀ : ∀ {n₁ n₂} (T : Type (1 + n₁)) (ρ : Sub n₁ n₂) →
         (∀α T) [ ρ ]ˢ ≡ ∀α (T [ ρ ↑ˢ ]ˢ)
push-∀ T ρ = refl

-- and LiftId, which the inductive model refutes (report.md §5.1, b12)
push-LiftId : ∀ {n} → (idˢ {n}) ↑ˢ ≡ idˢ
push-LiftId = refl
