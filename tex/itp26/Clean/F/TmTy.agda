{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.F.TmTy — TYPE-substitution acting on a TERM (the type-β engine).
--
-- The mirror image of `subTm`: here the TYPE scope Θ is what gets substituted (via
-- the type σ-engine `Clean.F.Ty`, imported as TY), and the TERM scope Γ is ambient
-- — `subTyTm` only THREADS a free term-thinning `Γ′ ⊑ Γ`.  Type ANNOTATIONS are
-- TY.sub'd (not just renamed); under Λ the type-sub lifts (TY.lift).
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.TmTy where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
import Clean.F.Ty as TY                 -- the TYPE σ-engine (qualified: TY.Sub, TY.sub, TY.selL, TY.lift, …)
open TY using (Ty)
open import Clean.F.Tm public           -- Tm, Bi, smart constructors, wkΓ-T/wkΘ-T, + Pos/Scaffold

-- subTyTm t ψ στ : substitute the TYPE-vars of `t : Tm Θ Γ′` by στ, embedding t's
-- term-scope into the ambient Γ via ψ.  Annotations are TY.sub'd.
subTyTm : ∀ {Θ Δ Γ′ Γ} → Tm Θ Γ′ → Γ′ ⊑ Γ → TY.Sub Δ Θ → Bi Tm Δ Γ
subTyTm tmvar               ψ στ = tmvar ⇑[ oe , ψ ]
subTyTm (app l r cθ cγ)     ψ στ =
  appᵇ (subTyTm l (thinL cγ ⨾ ψ) (TY.selL cθ στ)) (subTyTm r (thinR cγ ⨾ ψ) (TY.selR cθ στ))
subTyTm (lam a (use t) cθ)  ψ στ =
  lamᵇ (TY.sub a (TY.selL cθ στ)) (subTyTm t (os ψ) (TY.selR cθ στ))
subTyTm (lam a (drop t) cθ) ψ στ =
  lamᵇ (TY.sub a (TY.selL cθ στ)) (wkΓ-T (subTyTm t ψ (TY.selR cθ στ)))
subTyTm (Lam (use t))       ψ στ = Lamᵇ (subTyTm t ψ (TY.lift στ))
subTyTm (Lam (drop t))      ψ στ = Lamᵇ (wkΘ-T (subTyTm t ψ στ))
subTyTm (App e a cθ)        ψ στ =
  Appᵇ (subTyTm e ψ (TY.selL cθ στ)) (TY.sub a (TY.selR cθ στ))

-- apply a type-sub to a bi-scoped term (the term-thinning threads, the type-thinning restricts στ)
opaque
  _⟪_⟫T : ∀ {Θ Δ Γ} → Bi Tm Θ Γ → TY.Sub Δ Θ → Bi Tm Δ Γ
  (t ⇑[ θ , φ ]) ⟪ στ ⟫T = subTyTm t φ (στ TY.↾ θ)
infixl 8 _⟪_⟫T
