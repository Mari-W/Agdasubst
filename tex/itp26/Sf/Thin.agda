{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.Thin — LANGUAGE-INDEPENDENT thinning/cover/coproduct algebra.
--
-- This is McBride's co-de-Bruijn renaming infrastructure ("Everybody's Got To Be
-- Somewhere", MSFP 2018), generic in the scope element `I`.  It mentions NO
-- object-language constructor: only thinnings `_⊑_`, covers `Cover`, and their
-- coproduct `Cop`/`cop`.
--
-- WHY a confluent rewrite system at all:  in de Bruijn, variable lookup `σ x` is
-- an opaque FUNCTION application — it cannot be a rewrite (it re-enters the
-- function world; the σ-law `Clos` breaks).  In co-de-Bruijn there is no such
-- function: thinnings and coproducts are DATA destructors, so their laws DO close
-- into a confluent rewrite system.
--
-- THE "ONE OPAQUE BLOCK" TRICK:  every operation is `opaque`, so its defining
-- clauses do NOT race the laws we want to register about it (a transparent op
-- would reduce the law's LHS, breaking confluence).  The laws are PROVEN inside
-- the block (where the op unfolds) and REGISTERED after it.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.Thin (I : Set) where
open import Data.List using (List; []; _∷_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite

Scope : Set
Scope = List I
variable s : I
variable Γ Δ Θ Ξ Γ₁ Γ₂ Γₗ Γᵣ : Scope

-- thinnings / order-preserving embeddings (McBride §2)
data _⊑_ : Scope → Scope → Set where
  oz : [] ⊑ []
  os : Γ ⊑ Δ → (s ∷ Γ) ⊑ (s ∷ Δ)
  o' : Γ ⊑ Δ → Γ ⊑ (s ∷ Δ)
infix 4 _⊑_

-- a cover says, for each variable of Γ, whether it is used left, right, or both
data Cover : Scope → Scope → Scope → Set where
  czz : Cover [] [] []
  css : Cover Γₗ Γᵣ Γ → Cover (s ∷ Γₗ) (s ∷ Γᵣ) (s ∷ Γ)
  cs' : Cover Γₗ Γᵣ Γ → Cover (s ∷ Γₗ) Γᵣ       (s ∷ Γ)
  c's : Cover Γₗ Γᵣ Γ → Cover Γₗ       (s ∷ Γᵣ) (s ∷ Γ)

-- the coproduct of two thinnings into Δ (McBride §6): least Ξ⊑Δ containing both
record Cop {Γ₁ Γ₂ Δ}(θ : Γ₁ ⊑ Δ)(φ : Γ₂ ⊑ Δ) : Set where
  constructor mkCop
  field {un} : Scope
        inl  : Γ₁ ⊑ un
        inr  : Γ₂ ⊑ un
        out  : un ⊑ Δ
        cov  : Cover Γ₁ Γ₂ un
open Cop public

opaque
  -- identity + composition: the renaming MONOID (McBride §2/§7)
  oi : Γ ⊑ Γ
  oi {[]}    = oz
  oi {_ ∷ Γ} = os oi
  _⨾_ : Γ ⊑ Δ → Δ ⊑ Θ → Γ ⊑ Θ
  θ      ⨾ oz     = θ
  os θ   ⨾ os φ   = os (θ ⨾ φ)
  o' θ   ⨾ os φ   = o' (θ ⨾ φ)
  θ      ⨾ o' φ   = o' (θ ⨾ φ)
  infixl 6 _⨾_

  -- THINNING MONOID laws.  As rewrites these make renaming functoriality
  -- (ren-id, ren-∘ in Sf.Scaffold) hold by refl.
  oi⨾ : (θ : Γ ⊑ Δ) → oi ⨾ θ ≡ θ
  oi⨾ oz = refl ; oi⨾ (os θ) = cong os (oi⨾ θ) ; oi⨾ (o' θ) = cong o' (oi⨾ θ)
  ⨾oi : (θ : Γ ⊑ Δ) → θ ⨾ oi ≡ θ
  ⨾oi oz = refl ; ⨾oi (os θ) = cong os (⨾oi θ) ; ⨾oi (o' θ) = cong o' (⨾oi θ)
  ⨾⨾ : (θ : Γ ⊑ Δ)(φ : Δ ⊑ Θ)(ψ : Θ ⊑ Ξ) → (θ ⨾ φ) ⨾ ψ ≡ θ ⨾ (φ ⨾ ψ)
  ⨾⨾ θ      φ      (o' ψ) = cong o' (⨾⨾ θ φ ψ)
  ⨾⨾ θ      (o' φ) (os ψ) = cong o' (⨾⨾ θ φ ψ)
  ⨾⨾ (os θ) (os φ) (os ψ) = cong os (⨾⨾ θ φ ψ)
  ⨾⨾ (o' θ) (os φ) (os ψ) = cong o' (⨾⨾ θ φ ψ)
  ⨾⨾ oz     oz     oz     = refl

  -- COPRODUCT of two thinnings into Δ (McBride §6): the least Ξ⊑Δ containing both
  -- images, with a cover.  This is what substitution uses to merge subterm supports.
  cop : (θ : Γ₁ ⊑ Δ)(φ : Γ₂ ⊑ Δ) → Cop θ φ
  cop oz     oz     = mkCop oz oz oz czz
  cop (os θ) (os φ) = let mkCop l r o c = cop θ φ in mkCop (os l) (os r) (os o) (css c)
  cop (os θ) (o' φ) = let mkCop l r o c = cop θ φ in mkCop (os l) (o' r) (os o) (cs' c)
  cop (o' θ) (os φ) = let mkCop l r o c = cop θ φ in mkCop (o' l) (os r) (os o) (c's c)
  cop (o' θ) (o' φ) = let mkCop l r o c = cop θ φ in mkCop l      r      (o' o) c

  -- the three "select a cover side" thinnings + the diagonal cover
  covL : (φ : Γ ⊑ Δ) → Cover Δ Γ Δ
  covL oz = czz ; covL (os φ) = css (covL φ) ; covL (o' φ) = cs' (covL φ)
  covR : (θ : Γ ⊑ Δ) → Cover Γ Δ Δ
  covR oz = czz ; covR (os θ) = css (covR θ) ; covR (o' θ) = c's (covR θ)
  full : Cover Γ Γ Γ
  full {[]} = czz ; full {_ ∷ Γ} = css full

  -- COVER/COPRODUCT unit laws.  `cop oi φ` / `cop θ oi` spawn the critical pair
  -- `cop oi oi → covL oi` vs `covR oi`, closed by covL-oi/covR-oi (both → full).
  covL-oi : covL (oi {Γ}) ≡ full
  covL-oi {[]} = refl ; covL-oi {_ ∷ Γ} = cong css covL-oi
  covR-oi : covR (oi {Γ}) ≡ full
  covR-oi {[]} = refl ; covR-oi {_ ∷ Γ} = cong css covR-oi
  cop-oiL : (φ : Γ ⊑ Δ) → cop oi φ ≡ mkCop oi φ oi (covL φ)
  cop-oiL oz = refl
  cop-oiL (os φ) rewrite cop-oiL φ = refl
  cop-oiL (o' φ) rewrite cop-oiL φ = refl
  cop-oiR : (θ : Γ ⊑ Δ) → cop θ oi ≡ mkCop θ oi oi (covR θ)
  cop-oiR oz = refl
  cop-oiR (os θ) rewrite cop-oiR θ = refl
  cop-oiR (o' θ) rewrite cop-oiR θ = refl

-- ── REWRITE GROUP: THINNING MONOID ──  (oi/⨾ unit + associativity)
{-# REWRITE oi⨾ ⨾oi ⨾⨾ #-}
-- ── REWRITE GROUP: COVER/COPRODUCT algebra ──  (cop units + covL/covR completion)
{-# REWRITE covL-oi covR-oi cop-oiL cop-oiR #-}

-- ── the empty thinning.  OPAQUE on purpose: if it unfolded to `o' oe`, then the
-- context law `rest oe Ψ → ε` (Sf.Typing) would race `rest (o' oe) Ψ` (stuck for
-- abstract Ψ) and break confluence.  Opaque ⇒ no competing redex.
opaque
  oe : ∀ {Δ} → [] ⊑ Δ
  oe {[]}    = oz
  oe {_ ∷ Δ} = o' oe

-- ── cover → its two embedding thinnings.  OPAQUE so cop-thin (Sf.Sigma) has a
-- stable neutral LHS (a transparent thinL/thinR would let cop-thin's LHS reduce
-- and break confluence).
opaque
  thinL : ∀ {sₗ sᵣ Γ} → Cover sₗ sᵣ Γ → sₗ ⊑ Γ
  thinL czz = oz ; thinL (css c) = os (thinL c)
  thinL (cs' c) = os (thinL c) ; thinL (c's c) = o' (thinL c)
  thinR : ∀ {sₗ sᵣ Γ} → Cover sₗ sᵣ Γ → sᵣ ⊑ Γ
  thinR czz = oz ; thinR (css c) = os (thinR c)
  thinR (cs' c) = o' (thinR c) ; thinR (c's c) = os (thinR c)

-- (The COVER-THINNING completion rewrites — thinL-covL etc. — live in Sf.Context,
-- stated for that layer's TRANSPARENT `thL`/`thR`; the opaque `thinL`/`thinR`
-- here carry no completion, they only feed the σ-engine's cop-thin lemma.)

-- cop of a cover's two thinnings reconstructs the cover, out = oi.  Needed for
-- the σ-law IdSubst.  Stable LHS: thinL/thinR opaque (else its LHS would reduce).
opaque
  unfolding cop thinL thinR
  cop-thin : ∀ {sₗ sᵣ Γ}(cv : Cover sₗ sᵣ Γ) → cop (thinL cv) (thinR cv) ≡ mkCop (thinL cv) (thinR cv) oi cv
  cop-thin czz                  = refl
  cop-thin (css c) rewrite cop-thin c = refl
  cop-thin (cs' c) rewrite cop-thin c = refl
  cop-thin (c's c) rewrite cop-thin c = refl
