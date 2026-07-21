{-# OPTIONS --rewriting --local-confluence-check #-}
-- The co-de-Bruijn thinning/cop/cover infrastructure is GENERIC in the scope
-- element.  Parameterising by (I : Set) gives both the STLC instance (I = ⊤) and
-- the System F instance (I = Sort) for free — McBride's construction is generic.
module CDBsigG (I : Set) where
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Agda.Builtin.Equality.Rewrite

Scope : Set
Scope = List I
variable s : I
variable Γ Δ Θ Ξ Γ₁ Γ₂ Γₗ Γᵣ : Scope

data _⊑_ : Scope → Scope → Set where
  oz : [] ⊑ []
  os : Γ ⊑ Δ → (s ∷ Γ) ⊑ (s ∷ Δ)
  o' : Γ ⊑ Δ → Γ ⊑ (s ∷ Δ)
infix 4 _⊑_

data Cover : Scope → Scope → Scope → Set where
  czz : Cover [] [] []
  css : Cover Γₗ Γᵣ Γ → Cover (s ∷ Γₗ) (s ∷ Γᵣ) (s ∷ Γ)
  cs' : Cover Γₗ Γᵣ Γ → Cover (s ∷ Γₗ) Γᵣ       (s ∷ Γ)
  c's : Cover Γₗ Γᵣ Γ → Cover Γₗ       (s ∷ Γᵣ) (s ∷ Γ)

record Cop {Γ₁ Γ₂ Δ}(θ : Γ₁ ⊑ Δ)(φ : Γ₂ ⊑ Δ) : Set where
  constructor mkCop
  field {un} : Scope
        inl  : Γ₁ ⊑ un
        inr  : Γ₂ ⊑ un
        out  : un ⊑ Δ
        cov  : Cover Γ₁ Γ₂ un
open Cop public

opaque
  oi : Γ ⊑ Γ
  oi {[]}    = oz
  oi {_ ∷ Γ} = os oi
  _⨾_ : Γ ⊑ Δ → Δ ⊑ Θ → Γ ⊑ Θ
  θ      ⨾ oz     = θ
  os θ   ⨾ os φ   = os (θ ⨾ φ)
  o' θ   ⨾ os φ   = o' (θ ⨾ φ)
  θ      ⨾ o' φ   = o' (θ ⨾ φ)
  infixl 6 _⨾_
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
  cop : (θ : Γ₁ ⊑ Δ)(φ : Γ₂ ⊑ Δ) → Cop θ φ
  cop oz     oz     = mkCop oz oz oz czz
  cop (os θ) (os φ) = let mkCop l r o c = cop θ φ in mkCop (os l) (os r) (os o) (css c)
  cop (os θ) (o' φ) = let mkCop l r o c = cop θ φ in mkCop (os l) (o' r) (os o) (cs' c)
  cop (o' θ) (os φ) = let mkCop l r o c = cop θ φ in mkCop (o' l) (os r) (os o) (c's c)
  cop (o' θ) (o' φ) = let mkCop l r o c = cop θ φ in mkCop l      r      (o' o) c
  covL : (φ : Γ ⊑ Δ) → Cover Δ Γ Δ
  covL oz = czz ; covL (os φ) = css (covL φ) ; covL (o' φ) = cs' (covL φ)
  covR : (θ : Γ ⊑ Δ) → Cover Γ Δ Δ
  covR oz = czz ; covR (os θ) = css (covR θ) ; covR (o' θ) = c's (covR θ)
  full : Cover Γ Γ Γ
  full {[]} = czz ; full {_ ∷ Γ} = css full
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
{-# REWRITE oi⨾ ⨾oi ⨾⨾ covL-oi covR-oi cop-oiL cop-oiR #-}
