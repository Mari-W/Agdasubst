{-# OPTIONS --rewriting --local-confluence-check #-}
-- Types are CONCRETE data (you can pattern-match / eliminate them);
-- only the substitution machinery (Sub, _⨟_, _[_]) is abstract, and substitution
-- COMPUTES on concrete types via the confluent rewrite rules.
module SigmaTyData where
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat using (ℕ; zero; suc)

variable m n k l : ℕ

-- ⟶ concrete, eliminable type syntax
data Ty : ℕ → Set where
  vz   : Ty (suc n)
  _⇒_  : Ty n → Ty n → Ty n
  ∀'_  : Ty (suc n) → Ty n

postulate
  Sub  : ℕ → ℕ → Set
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
  Clos      : (A [ s ]) [ t ] ≡ A [ s ⨟ t ]
  IdSubst   : A [ id ] ≡ A
  VarCons   : vz [ A ∙ s ] ≡ A
  IdL       : id ⨟ s ≡ s
  IdR       : s ⨟ id ≡ s
  ShiftCons : wk ⨟ (A ∙ s) ≡ s
  Map       : (A ∙ s) ⨟ t ≡ (A [ t ]) ∙ (s ⨟ t)
  Ass       : (s ⨟ t) ⨟ u ≡ s ⨟ (t ⨟ u)
  IdCons    : (vz {n}) ∙ wk ≡ id
  SCons     : (vz [ s ]) ∙ (wk ⨟ s) ≡ s
  Inst-⇒    : (A ⇒ B) [ s ] ≡ (A [ s ]) ⇒ (B [ s ])
  Inst-∀    : (∀' A) [ s ] ≡ ∀' (A [ vz ∙ (s ⨟ wk) ])
{-# REWRITE Clos IdSubst VarCons IdL IdR ShiftCons Map Ass IdCons SCons Inst-⇒ Inst-∀ #-}

-- and now types are REAL data: you can eliminate them.
open import Data.Bool using (Bool; true; false)
isArrow : Ty n → Bool
isArrow (_ ⇒ _) = true
isArrow _        = false
