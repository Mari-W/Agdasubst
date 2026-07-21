{-# OPTIONS --rewriting --local-confluence-check #-}
-- The convergent first-order σ-calculus (σ_SP, à la ACCL / Stark) for the
-- TYPE level of System F.  Passes Agda's confluence checker GENUINELY:
-- --local-confluence-check, NO --double-check.
--
-- The two things that make this work, learned the hard way from the
-- function-based encodings (which only pass under the --double-check bug):
--   (1) substitutions are SYNTAX (id, wk, cons, comp), not functions, so the
--       confluence checker compares them structurally (no funext involved);
--   (2) there is ONE uniform instantiation  _[_]  with no variable-lookup /
--       term-instantiation split, so the closure rule  Clos  fires on
--       variables too — which is exactly what joins the η/dist critical pair
--       that is non-confluent in the split encodings.
-- First-class renamings (the coincidence-pop-* completion) are deliberately
-- absent: they are an optimisation, not part of σ, and they reintroduce the
-- non-joinable critical pairs.
module SigmaTy where
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat using (ℕ; zero; suc)

variable m n k l : ℕ

postulate
  Ty  : ℕ → Set
  Sub : ℕ → ℕ → Set
  -- type syntax  (vz = de Bruijn 0; higher variables are  vz [ wk ⨟ … ])
  vz   : Ty (suc n)
  _⇒_  : Ty n → Ty n → Ty n
  ∀'_  : Ty (suc n) → Ty n
  -- substitution syntax
  id   : Sub n n
  wk   : Sub n (suc n)
  _∙_  : Ty n → Sub m n → Sub (suc m) n
  _⨟_  : Sub m k → Sub k n → Sub m n
  _[_] : Ty m → Sub m n → Ty n

infixr 5 _⇒_
infixl 6 _⨟_
infixr 7 _∙_

variable A B : Ty n
variable s t u : Sub m n

postulate
  -- monad / closure  (the ONE uniform rule — fires on every type, incl. vars)
  Clos      : (A [ s ]) [ t ] ≡ A [ s ⨟ t ]
  IdSubst   : A [ id ] ≡ A
  VarCons   : vz [ A ∙ s ] ≡ A
  -- substitution algebra
  IdL       : id ⨟ s ≡ s
  IdR       : s ⨟ id ≡ s
  ShiftCons : wk ⨟ (A ∙ s) ≡ s
  Map       : (A ∙ s) ⨟ t ≡ (A [ t ]) ∙ (s ⨟ t)
  Ass       : (s ⨟ t) ⨟ u ≡ s ⨟ (t ⨟ u)
  -- η / surjective pairing  (the σ_SP extension)
  IdCons    : (vz {n}) ∙ wk ≡ id
  SCons     : (vz [ s ]) ∙ (wk ⨟ s) ≡ s
  -- traversal: push instantiation through the type structure
  Inst-⇒    : (A ⇒ B) [ s ] ≡ (A [ s ]) ⇒ (B [ s ])
  Inst-∀    : (∀' A) [ s ] ≡ ∀' (A [ vz ∙ (s ⨟ wk) ])

{-# REWRITE Clos IdSubst VarCons IdL IdR ShiftCons Map Ass IdCons SCons Inst-⇒ Inst-∀ #-}
