{-# OPTIONS --rewriting --local-confluence-check #-}
-- ============================================================================
-- Co-de-Bruijn infrastructure as a CONFLUENT REWRITE SYSTEM.
-- Following Conor McBride, "Everybody's Got To Be Somewhere" (MSFP 2018,
--   EPTCS 275; arXiv:1807.04085).  Section map:
--     _⊑_ , oi , _⨾_ , the category laws ......... §2 (OPEs) / §7 (monoidal str.)
--     Cover ...................................... the cover relation of §8
--     Cop / cop .................................. §6 "Coproduct in Slices of ⊑⁺"
--     covL / covR / full ......................... cover ops used by cop's unit laws
--
-- The point of THIS file: in de Bruijn, variable lookup `σ x` is an abstract
-- FUNCTION application — it cannot be a confluent rewrite (it re-enters the
-- function world; breaks `Clos`).  In co-de-Bruijn there is no such function:
-- thinnings and coproducts are DATA destructors, so their laws DO close into a
-- confluent rewrite system.  Verified: --local-confluence-check 0.
-- Method (the "one opaque block" trick): the ops are opaque (so their laws can
-- be rewrites without their clauses racing them); the laws are PROVEN inside the
-- block, where the ops unfold; then registered after the block.
-- ============================================================================
module CDBsig where
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite

Scope : Set
Scope = List ⊤
variable Γ Δ Θ Ξ Γ₁ Γ₂ Γₗ Γᵣ : Scope

-- thinnings / order-preserving embeddings (McBride §2)
data _⊑_ : Scope → Scope → Set where
  oz : [] ⊑ []
  os : Γ ⊑ Δ → (tt ∷ Γ) ⊑ (tt ∷ Δ)
  o' : Γ ⊑ Δ → Γ ⊑ (tt ∷ Δ)
infix 4 _⊑_

-- a cover says, for each variable of Γ, whether it is used left, right, or both
data Cover : Scope → Scope → Scope → Set where
  czz : Cover [] [] []
  css : Cover Γₗ Γᵣ Γ → Cover (tt ∷ Γₗ) (tt ∷ Γᵣ) (tt ∷ Γ)
  cs' : Cover Γₗ Γᵣ Γ → Cover (tt ∷ Γₗ) Γᵣ        (tt ∷ Γ)
  c's : Cover Γₗ Γᵣ Γ → Cover Γₗ        (tt ∷ Γᵣ) (tt ∷ Γ)

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
  -- identity + composition of thinnings (the renaming algebra, McBride §2)
  oi : Γ ⊑ Γ
  oi {[]}    = oz
  oi {_ ∷ Γ} = os oi
  _⨾_ : Γ ⊑ Δ → Δ ⊑ Θ → Γ ⊑ Θ
  θ      ⨾ oz     = θ
  os θ   ⨾ os φ   = os (θ ⨾ φ)
  o' θ   ⨾ os φ   = o' (θ ⨾ φ)
  θ      ⨾ o' φ   = o' (θ ⨾ φ)
  infixl 6 _⨾_

  -- thinning CATEGORY laws (McBride §2/§7); as rewrites these make renaming
  -- functoriality (ren-id, ren-∘ in CDBterm) hold by refl
  oi⨾ : (θ : Γ ⊑ Δ) → oi ⨾ θ ≡ θ
  oi⨾ oz     = refl
  oi⨾ (os θ) = cong os (oi⨾ θ)
  oi⨾ (o' θ) = cong o' (oi⨾ θ)
  ⨾oi : (θ : Γ ⊑ Δ) → θ ⨾ oi ≡ θ
  ⨾oi oz     = refl
  ⨾oi (os θ) = cong os (⨾oi θ)
  ⨾oi (o' θ) = cong o' (⨾oi θ)
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

  covL : (φ : Γ ⊑ Δ) → Cover Δ Γ Δ
  covL oz     = czz
  covL (os φ) = css (covL φ)
  covL (o' φ) = cs' (covL φ)
  covR : (θ : Γ ⊑ Δ) → Cover Γ Δ Δ
  covR oz     = czz
  covR (os θ) = css (covR θ)
  covR (o' θ) = c's (covR θ)
  full : Cover Γ Γ Γ
  full {[]}    = czz
  full {_ ∷ Γ} = css full

  -- cop's UNIT laws.  cop oi φ / cop θ oi spawn the critical pair cop oi oi →
  -- covL oi vs covR oi, closed by the covL-oi/covR-oi laws below (both → full).
  covL-oi : covL (oi {Γ}) ≡ full
  covL-oi {[]}    = refl
  covL-oi {_ ∷ Γ} = cong css covL-oi
  covR-oi : covR (oi {Γ}) ≡ full
  covR-oi {[]}    = refl
  covR-oi {_ ∷ Γ} = cong css covR-oi
  cop-oiL : (φ : Γ ⊑ Δ) → cop oi φ ≡ mkCop oi φ oi (covL φ)
  cop-oiL oz                    = refl
  cop-oiL (os φ) rewrite cop-oiL φ = refl
  cop-oiL (o' φ) rewrite cop-oiL φ = refl
  cop-oiR : (θ : Γ ⊑ Δ) → cop θ oi ≡ mkCop θ oi oi (covR θ)
  cop-oiR oz                    = refl
  cop-oiR (os θ) rewrite cop-oiR θ = refl
  cop-oiR (o' θ) rewrite cop-oiR θ = refl

{-# REWRITE oi⨾ ⨾oi ⨾⨾ covL-oi covR-oi cop-oiL cop-oiR #-}
