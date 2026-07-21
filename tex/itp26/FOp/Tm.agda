{-# OPTIONS --rewriting --local-confluence-check #-}
-- RAW (extrinsic) System F terms over the proven-law co-de-Bruijn types (FOp.Ty).
-- Terms carry NO type index ⇒ the substitution operations are plain functions and
-- their laws (compositionality, identity) are CLEAN equations — no transport, no subst.
module FOp.Tm where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Agda.Builtin.Equality.Rewrite
open import FOp.ThinRw
open import FOp.Ty

-- raw terms, indexed only by the TYPE scope Θ (term variables are de Bruijn naturals)
data Tm (Θ : Scope) : Set where
  var : ℕ → Tm Θ
  lam : Ty ↑ Θ → Tm Θ → Tm Θ            -- Church-style: domain type annotation
  app : Tm Θ → Tm Θ → Tm Θ
  Lam : Tm (tt ∷ Θ) → Tm Θ
  App : Tm Θ → Ty ↑ Θ → Tm Θ

-- ════ TYPE substitution acting on a term = a plain OPERATION ════
subTyTm : Tm Θ → Sub Δ Θ → Tm Δ
subTyTm (var n)   σ = var n
subTyTm (lam A t) σ = lam (A ⟪ σ ⟫) (subTyTm t σ)
subTyTm (app t u) σ = app (subTyTm t σ) (subTyTm u σ)
subTyTm (Lam t)   σ = Lam (subTyTm t (lift σ))
subTyTm (App t A) σ = App (subTyTm t σ) (A ⟪ σ ⟫)

-- ★ COMPOSITIONALITY of subTyTm — PROVEN, no transport, no subst (this is the point)
subTyTm-⨟ : (t : Tm Θ)(σ : Sub Δ Θ)(τ : Sub Ξ Δ) → subTyTm (subTyTm t σ) τ ≡ subTyTm t (σ ⨟ τ)
subTyTm-⨟ (var n)   σ τ = refl
subTyTm-⨟ (lam A t) σ τ = cong₂ lam (Clos A σ τ) (subTyTm-⨟ t σ τ)
subTyTm-⨟ (app t u) σ τ = cong₂ app (subTyTm-⨟ t σ τ) (subTyTm-⨟ u σ τ)
subTyTm-⨟ (Lam t)   σ τ = cong Lam (trans (subTyTm-⨟ t (lift σ) (lift τ)) (cong (subTyTm t) (lift-⨟ σ τ)))
subTyTm-⨟ (App t A) σ τ = cong₂ App (subTyTm-⨟ t σ τ) (Clos A σ τ)

-- ★ IDENTITY law for subTyTm — PROVEN, clean
subTyTm-id : (t : Tm Θ) → subTyTm t ids ≡ t
subTyTm-id (var n)   = refl
subTyTm-id (lam A t) = cong₂ lam (⟪⟫-id A) (subTyTm-id t)
subTyTm-id (app t u) = cong₂ app (subTyTm-id t) (subTyTm-id u)
subTyTm-id (Lam t)   = cong Lam (subTyTm-id t)          -- lift ids = ids (definitional)
subTyTm-id (App t A) = cong₂ App (subTyTm-id t) (⟪⟫-id A)

-- ════ TERM substitution (de Bruijn, parallel) — also a plain OPERATION ════
Ren : Set
Ren = ℕ → ℕ
liftR : Ren → Ren
liftR ρ zero    = zero
liftR ρ (suc n) = suc (ρ n)
renTm : Ren → Tm Θ → Tm Θ
renTm ρ (var n)   = var (ρ n)
renTm ρ (lam A t) = lam A (renTm (liftR ρ) t)
renTm ρ (app t u) = app (renTm ρ t) (renTm ρ u)
renTm ρ (Lam t)   = Lam (renTm ρ t)
renTm ρ (App t A) = App (renTm ρ t) A
wkTyTm : Tm Θ → Tm (tt ∷ Θ)          -- type-weaken a term (needed under Lam)
wkTyTm t = subTyTm t (wkSub ids)
liftS : (ℕ → Tm Θ) → (ℕ → Tm Θ)
liftS σ zero    = var zero
liftS σ (suc n) = renTm suc (σ n)
subTm : (ℕ → Tm Θ) → Tm Θ → Tm Θ
subTm σ (var n)   = σ n
subTm σ (lam A t) = lam A (subTm (liftS σ) t)
subTm σ (app t u) = app (subTm σ t) (subTm σ u)
subTm σ (Lam t)   = Lam (subTm (λ n → wkTyTm (σ n)) t)
subTm σ (App t A) = App (subTm σ t) A
-- single substitution (for β): replace var 0 by a
_∷ˢ_ : Tm Θ → (ℕ → Tm Θ) → (ℕ → Tm Θ)
(a ∷ˢ σ) zero    = a
(a ∷ˢ σ) (suc n) = σ n
sub0 : Tm Θ → Tm Θ → Tm Θ
sub0 a t = subTm (a ∷ˢ var) t

-- type-substitution commutes with term-renaming and term-substitution — CLEAN (no subst)
subTy-renTm : (ρ : Ren)(t : Tm Θ)(σ : Sub Δ Θ) → subTyTm (renTm ρ t) σ ≡ renTm ρ (subTyTm t σ)
subTy-renTm ρ (var n)   σ = refl
subTy-renTm ρ (lam A t) σ = cong (lam _) (subTy-renTm (liftR ρ) t σ)
subTy-renTm ρ (app t u) σ = cong₂ app (subTy-renTm ρ t σ) (subTy-renTm ρ u σ)
subTy-renTm ρ (Lam t)   σ = cong Lam (subTy-renTm ρ t (lift σ))
subTy-renTm ρ (App t A) σ = cong (λ z → App z _) (subTy-renTm ρ t σ)

-- term-sub respects pointwise-equal substitutions — WITHOUT funext (pointwise congruence)
subTm-cong : {σ σ′ : ℕ → Tm Θ}(t : Tm Θ) → (∀ n → σ n ≡ σ′ n) → subTm σ t ≡ subTm σ′ t
subTm-cong (var n)   e = e n
subTm-cong (lam A t) e = cong (lam A) (subTm-cong t λ { zero → refl ; (suc n) → cong (renTm suc) (e n) })
subTm-cong (app t u) e = cong₂ app (subTm-cong t e) (subTm-cong u e)
subTm-cong (Lam t)   e = cong Lam (subTm-cong t λ n → cong wkTyTm (e n))
subTm-cong (App t A) e = cong (λ z → App z A) (subTm-cong t e)
