{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.Pos — POSITIONS are SINGLETON THINNINGS  `Pos Γ = (tt∷[]) ⊑ Γ`.
--
-- This is the thinning-position rep (cf. the Var rep we had before): a position is
-- a thinning, so positions COMPOSE by the already-registered `_⨾_` — there is NO
-- separate `act`, no `act-⨾`, and the cover coherence is FREE via `Fac-L⨾`.  The
-- only residue is the "position lookup" fact `oe ⨾ θ ≡ oe` (the empty thinning is
-- absorbing), registered below.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.Pos where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Agda.Builtin.Equality.Rewrite
open import Sf.Scaffold ⊤ public  -- Scope, _⊑_ (oz/os/o'), oi, _⨾_, oe, Cover, cop, thinL/thinR, _↑_, _⟨_⟩, pairUp, bindUp, ...
open import Sf.Fac ⊤ public       -- Fac-L/R/Fac-L⨾/Fac-R⨾ + cover-thinning completion

-- a position = a singleton thinning picking one slot of Γ
Pos : Scope → Set
Pos Γ = (tt ∷ []) ⊑ Γ

-- the empty thinning is unique and absorbing — the only "position tax" (replaces the
-- Var rep's act/var⊑ roundtrips).  `oe ⨾ θ → oe` lets head-position lookups compute.
opaque
  unfolding oe
  oe-uniq : ∀ {Γ}(q : [] ⊑ Γ) → q ≡ oe
  oe-uniq oz     = refl
  oe-uniq (o' q) = cong o' (oe-uniq q)
opaque
  unfolding oe _⨾_
  oe-⨾ : ∀ {Γ Δ}(θ : Γ ⊑ Δ) → oe ⨾ θ ≡ oe
  oe-⨾ oz     = refl
  oe-⨾ (os θ) = cong o' (oe-⨾ θ)
  oe-⨾ (o' θ) = cong o' (oe-⨾ θ)
{-# REWRITE oe-⨾ #-}
