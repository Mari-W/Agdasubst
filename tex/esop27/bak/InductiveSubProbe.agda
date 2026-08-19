{-# OPTIONS --rewriting --local-confluence-check #-}
-- ⚠ MEASUREMENT PROBE for REPORT-options.md ⚠  Nothing imports this file.
--
-- OPTION 2's falsifier.  Family (B) is "a law whose LHS carries a
-- COMPUTED type argument".  The proposed escape is to make the map
-- formers CONSTRUCTORS of an inductive `Sub` rather than opaque defined
-- symbols, so that `σ ⨟ τ` and `σ ↑` are rigid by construction — and,
-- unlike the `opaque` route, constructors have no trouble participating
-- in mutual recursion (see OneSortedProbe.agda, which died on exactly
-- that).
--
-- THE CRUX IS TERMINATION.  With `_⨟_` a constructor, lookup must read
--     α & (σ ⨟ τ)  =  (α & σ) [ τ ]
-- and the traversal must read
--     (var α) [ σ ] = α & σ
-- so `_&_` and `_[_]` are mutually recursive with NEITHER argument
-- structurally decreasing in the ⨟-case: `α & σ` is an arbitrary `Ty`.
-- If Agda's termination checker rejects this, Option 2 costs a
-- well-founded recursion (on the size of the Sub) before any confluence
-- question can even be asked.
--
-- MEASURED OUTCOME: termination FAILS, as anticipated.
--   error: [TerminationIssue] Termination checking failed for: _&_, _[_]
--   Problematic calls: α & σ ; (α & σ) [ τ ] ; α & σ ; T [ σ ↑ ]
-- So Option 2 is not free: the σ-calculus must be rebuilt on
-- well-founded recursion over the size of the `Sub` before any
-- confluence question can be asked.  That is a serious cost, because a
-- well-founded `_&_`/`_[_]` computes only as far as its accessibility
-- proof reduces — and the entire rewriting method depends on these two
-- functions computing definitionally.  See REPORT-options.md §4.
--
-- This file asks ONLY the termination question.  It registers no rules.
module InductiveSubProbe where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; zero; suc)

variable n m k : Nat

data Ty : Nat → Set
data Sub : Nat → Nat → Set

data Ty where
  var : Fin n → Ty n
  arr : Ty n → Ty n → Ty n
  all : Ty (suc n) → Ty n

-- composition and lifting are CONSTRUCTORS, so every map former is rigid
data Sub where
  idₛ : Sub n n
  wkₛ : Sub n (suc n)
  _∙_ : Ty m → Sub n m → Sub (suc n) m
  _⨟_ : Sub n m → Sub m k → Sub n k
  _↑  : Sub n m → Sub (suc n) (suc m)

infixl 6 _&_

_&_  : Fin n → Sub n m → Ty m
_[_] : Ty n → Sub n m → Ty m

α       & idₛ      = var α
α       & wkₛ      = var (suc α)
zero    & (T ∙ σ)  = T
(suc α) & (T ∙ σ)  = α & σ
α       & (σ ⨟ τ)  = (α & σ) [ τ ]      -- ← not structurally decreasing
zero    & (σ ↑)    = var zero
(suc α) & (σ ↑)    = (α & σ) [ wkₛ ]    -- ← not structurally decreasing

var α       [ σ ] = α & σ
arr T₁ T₂   [ σ ] = arr (T₁ [ σ ]) (T₂ [ σ ])
all T       [ σ ] = all (T [ σ ↑ ])
