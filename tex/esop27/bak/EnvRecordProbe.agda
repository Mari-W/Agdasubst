{-# OPTIONS --rewriting --local-confluence-check #-}
-- ⚠ MEASUREMENT PROBE — *EXPECTED TO FAIL* (exit 42) ⚠
-- Task 2 of REPORT-canonicity-port.md: can the canonicity prototype's
-- bundled-record environment
--     record Env (n : Nat) : Set where
--       field syn : Sub n 0
--             sem : (α : Var n) → Pred (α &ˢ syn)
-- be ported to the STRATIFIED setting, where `Pred` is level-indexed?
--
-- Attempt (a) from the brief: "index the record by the level rather than
-- quantifying inside it, staying in Set (maxL Δ)".
-- Nothing imports this file.
module EnvRecordProbe where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)

open import SystemF-strat hiding (fundamental)

-- ══════════════════════════════════════════════════════════════════
-- ATTEMPT (a): the record with `syn` as a FIELD, as in the prototype.
--
-- `Pred {l} A : Set (lsuc l)`, so the `sem` field must quantify over
-- `l : Level`.  A Π over `Level` lands in `Setω`, so the record cannot
-- be declared at `Set (maxL Δ)`.  Uncommenting the block below is the
-- measurement: Agda rejects it.
--
--   record EnvR (Δ : LCtx) : Set (maxL Δ) where
--     field
--       syn : Sub Δ ∅
--       sem : ∀ {l} (α : Δ ∋ˡ l) → Pred (α &ˢ syn)
--
-- error: The type of the constructor does not fit in the sort of the
-- datatype … Setω is not less or equal than Set (maxL Δ)
--
-- "Indexing the record by the level" does not rescue this: a SINGLE
-- environment for `Δ` must supply a predicate at EVERY level occurring
-- in `Δ`, so the level cannot be moved out to a parameter.  The record
-- would have to be `EnvR : (Δ : LCtx) → Level → Set …`, which no longer
-- types `sem` for a `Δ` mixing levels.
--
-- The live check below is the *uncommented* version, so that this file
-- records a real Agda verdict rather than a claim.
-- ══════════════════════════════════════════════════════════════════

record EnvR (Δ : LCtx) : Set (maxL Δ) where
  field
    syn : Sub Δ ∅
    sem : ∀ {l} (α : Δ ∋ˡ l) → Pred (α &ˢ syn)
