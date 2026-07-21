{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.STLCInst — registers the INSTANTIATION laws Inst-· / Inst-ƛ as rewrites,
-- so that `sub` on a constructor reduces to the constructor of subs and the σ_SP
-- law set is COMPLETE definitionally (see Sf.SigmaLaws).
--
-- WHY a separate module: making Inst-· a rewrite spawns a critical pair with
-- IdSubst (`sub (app …) idS` reduces two ways).  Closing it needs the
-- coproduct-algebra completion `cop-thin`/`cop-thin-⨾` as rewrites — whose
-- `cop θ φ` LHS would, in the typing layer, race the context coherence cohL.
-- The SR proof needs NONE of these, so they are quarantined here, imported only
-- by Sf.SigmaLaws — exactly as McBride's reference keeps the typing layer free
-- of the σ-engine's instantiation rewrites.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.STLCInst where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Equality.Rewrite
open import Sf.STLC

-- coproduct-algebra completion (concrete Tm instances) so Inst-· JOINS IdSubst:
-- app↑ (sub l (selL cv idS)) … further reduces to (app …)⇑oi.
selL-idS-Tm   : ∀ {sₗ sᵣ Γ}(cv : Cover sₗ sᵣ Γ) → selL cv idS ≡ idEmb (thinL cv)
selL-idS-Tm   = selL-idS
selR-idS-Tm   : ∀ {sₗ sᵣ Γ}(cv : Cover sₗ sᵣ Γ) → selR cv idS ≡ idEmb (thinR cv)
selR-idS-Tm   = selR-idS
selL-idEmb-Tm : ∀ {sₗ sᵣ sup Δ}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ) → selL cv (idEmb θ) ≡ idEmb (thinL cv ⨾ θ)
selL-idEmb-Tm = selL-idEmb
selR-idEmb-Tm : ∀ {sₗ sᵣ sup Δ}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ) → selR cv (idEmb θ) ≡ idEmb (thinR cv ⨾ θ)
selR-idEmb-Tm = selR-idEmb
{-# REWRITE selL-idS-Tm selR-idS-Tm selL-idEmb-Tm selR-idEmb-Tm sub-idEmb cop-thin cop-thin-⨾ #-}

-- ── REWRITE GROUP: INSTANTIATION (Inst-·) ──
{-# REWRITE Inst-· #-}

-- lift of an identity = identity at the bigger scope (closes Inst-ƛ × IdSubst)
opaque
  unfolding lift idEmb idS
  lift-idEmb : ∀ {s sup Δ}(θ : sup ⊑ Δ) → lift {s} (idEmb θ) ≡ idEmb (os θ)
  lift-idEmb θ = refl
opaque
  unfolding idS idEmb oi
  idS≡idEmb-oi : ∀ {Γ} → idS {Γ} ≡ idEmb (oi {Γ})
  idS≡idEmb-oi {[]}    = refl
  idS≡idEmb-oi {s ∷ Γ} = cong (λ ρ → wkSub ρ ,- var₀) idS≡idEmb-oi
lift-idS : ∀ {s Γ} → lift {s} (idS {Γ}) ≡ idEmb (os (oi {Γ}))
lift-idS = trans (cong lift idS≡idEmb-oi) (lift-idEmb oi)

-- ── REWRITE GROUP: INSTANTIATION (Inst-ƛ) ──
{-# REWRITE lift-idEmb lift-idS Inst-ƛ #-}
