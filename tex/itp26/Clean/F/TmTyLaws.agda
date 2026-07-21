{-# OPTIONS --rewriting #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.F.TmTyLaws — the renaming-commute for the TYPE-into-term engine subTyTm.
--
-- `subTyTm-renΘ` : subTyTm commutes with renaming the type-sub's TARGET scope.
-- This is the analog of TmLaws.subTm-renΘ for the OTHER engine; it REUSES all the
-- bi-scoped renaming distributions (TmLaws) + the type σ-laws sub-thin/lift-thinSub
-- (TyLaws).  Specialised to o' oi it gives `subTyTm-wkΘ`, which discharges the two
-- type-weakening postulates in SR (Lamᵈ-case and ⊢-wkΘ).
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.TmTyLaws where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite
open import Clean.Pos
import Clean.F.Ty as TY
open TY using (Ty)
open import Clean.F.TyLaws using (thinSub; sub-thin; lift-thinSub; sub-idEmb; lift-idS↾; ↑ₛ≡wkSubidS; sub-wkSub)
open import Clean.F.TmTy using (subTyTm)
open import Clean.F.TmLaws using (appᵇ-⟨⟩b; Appᵇ-⟨⟩b; lamᵇ-⟨⟩Θ; lamᵇ-drop-⟨⟩Θ; Lamᵇ-⟨⟩b; Lamᵇ-drop-⟨⟩Θ; wkΘ-T≡⟨⟩b)
open import Clean.F.Tm using (Tm; tmvar; app; lam; Lam; App; use; drop; Bi; _⇑[_,_]; _⟨_,_⟩b; lamᵇ; Lamᵇ; Appᵇ; appᵇ; wkΓ-T; wkΘ-T)

-- ── subTyTm-renΘ : subTyTm commutes with renaming the TYPE-sub's target by ξ ──
opaque
  unfolding subTyTm
  subTyTm-renΘ : ∀ {Θ Δ Δ′ Γ′ Γ}(t : Tm Θ Γ′)(ψ : Γ′ ⊑ Γ)(ξ : Δ ⊑ Δ′)(στ : TY.Sub Δ Θ)
               → subTyTm t ψ (thinSub ξ στ) ≡ (subTyTm t ψ στ) ⟨ ξ , oi ⟩b
  subTyTm-renΘ tmvar ψ ξ στ = refl
  subTyTm-renΘ (app l r cθ cγ) ψ ξ στ =
    trans (cong₂ appᵇ (subTyTm-renΘ l (thinL cγ ⨾ ψ) ξ (TY.selL cθ στ))
                      (subTyTm-renΘ r (thinR cγ ⨾ ψ) ξ (TY.selR cθ στ)))
          (sym (appᵇ-⟨⟩b (subTyTm l (thinL cγ ⨾ ψ) (TY.selL cθ στ)) (subTyTm r (thinR cγ ⨾ ψ) (TY.selR cθ στ)) ξ oi))
  subTyTm-renΘ (lam a (use t) cθ) ψ ξ στ =
    trans (cong₂ lamᵇ (sub-thin a ξ (TY.selL cθ στ)) (subTyTm-renΘ t (os ψ) ξ (TY.selR cθ στ)))
          (sym (lamᵇ-⟨⟩Θ (TY.sub a (TY.selL cθ στ)) (subTyTm t (os ψ) (TY.selR cθ στ)) ξ))
  subTyTm-renΘ (lam a (drop t) cθ) ψ ξ στ =
    trans (cong₂ (λ A Z → lamᵇ A (wkΓ-T Z)) (sub-thin a ξ (TY.selL cθ στ)) (subTyTm-renΘ t ψ ξ (TY.selR cθ στ)))
          (sym (lamᵇ-drop-⟨⟩Θ (TY.sub a (TY.selL cθ στ)) (subTyTm t ψ (TY.selR cθ στ)) ξ))
  subTyTm-renΘ (Lam (use t)) ψ ξ στ =
    trans (cong (λ s → Lamᵇ (subTyTm t ψ s)) (lift-thinSub ξ στ))
          (trans (cong Lamᵇ (subTyTm-renΘ t ψ (os ξ) (TY.lift στ)))
                 (sym (Lamᵇ-⟨⟩b (subTyTm t ψ (TY.lift στ)) ξ oi)))
  subTyTm-renΘ (Lam (drop t)) ψ ξ στ =
    trans (cong (λ Z → Lamᵇ (wkΘ-T Z)) (subTyTm-renΘ t ψ ξ στ))
          (sym (Lamᵇ-drop-⟨⟩Θ (subTyTm t ψ στ) ξ))
  subTyTm-renΘ (App e a cθ) ψ ξ στ =
    trans (cong₂ Appᵇ (subTyTm-renΘ e ψ ξ (TY.selL cθ στ)) (sub-thin a ξ (TY.selR cθ στ)))
          (sym (Appᵇ-⟨⟩b (subTyTm e ψ (TY.selL cθ στ)) (TY.sub a (TY.selR cθ στ)) ξ oi))

-- wkSub = thinSub (o' oi); hence subTyTm commutes with type-weakening
opaque
  unfolding TY.wkSub
  wkSub≡thinSub : ∀ {Δ Θ}(στ : TY.Sub Δ Θ) → TY.wkSub στ ≡ thinSub (o' oi) στ
  wkSub≡thinSub στ = refl

subTyTm-wkΘ : ∀ {Θ Δ Γ′ Γ}(t : Tm Θ Γ′)(ψ : Γ′ ⊑ Γ)(στ : TY.Sub Δ Θ)
            → subTyTm t ψ (TY.wkSub στ) ≡ wkΘ-T (subTyTm t ψ στ)
subTyTm-wkΘ t ψ στ =
  trans (cong (subTyTm t ψ) (wkSub≡thinSub στ))
        (trans (subTyTm-renΘ t ψ (o' oi) στ) (sym (wkΘ-T≡⟨⟩b (subTyTm t ψ στ))))

-- the o'-analogue of TyLaws.lift-↾, for the Λ-drop bridge in SR
postulate funext : ∀ {a b}{A : Set a}{B : A → Set b}{f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
opaque
  unfolding TY.lift TY._∙_ TY.wkSub _⨾_
  lift-↾-o' : ∀ {Δ Θ sup}(στ : TY.Sub Δ Θ)(θ : sup ⊑ Θ) → (TY.lift στ) TY.↾ (o' θ) ≡ TY.wkSub (στ TY.↾ θ)
  lift-↾-o' στ θ = funext λ p → refl

-- ── subTyTm-idEmb : subTyTm with the identity type-sub is the embedding ──
opaque
  unfolding subTyTm
  subTyTm-idEmb : ∀ {Θ Δ Γ′ Γ}(t : Tm Θ Γ′)(ψ : Γ′ ⊑ Γ)(θ : Θ ⊑ Δ)
                → subTyTm t ψ (TY.idS TY.↾ θ) ≡ t ⇑[ θ , ψ ]
  subTyTm-idEmb tmvar ψ θ = cong (λ z → tmvar ⇑[ z , ψ ]) (sym (oe-uniq θ))
  subTyTm-idEmb (app l r cθ cγ) ψ θ =
    trans (cong₂ appᵇ (subTyTm-idEmb l (thinL cγ ⨾ ψ) (thinL cθ ⨾ θ))
                      (subTyTm-idEmb r (thinR cγ ⨾ ψ) (thinR cθ ⨾ θ)))
          (cong₂ (λ cΘ cΓ → app l r (cov cΘ) (cov cΓ) ⇑[ out cΘ , out cΓ ])
                 (cop-thin-⨾ cθ θ) (cop-thin-⨾ cγ ψ))
  subTyTm-idEmb (lam a (use t) cθ) ψ θ =
    trans (cong₂ lamᵇ (sub-idEmb a (thinL cθ ⨾ θ)) (subTyTm-idEmb t (os ψ) (thinR cθ ⨾ θ)))
          (cong (λ c → lam a (use t) (cov c) ⇑[ out c , ψ ]) (cop-thin-⨾ cθ θ))
  subTyTm-idEmb (lam a (drop t) cθ) ψ θ =
    trans (cong₂ (λ A Z → lamᵇ A (wkΓ-T Z)) (sub-idEmb a (thinL cθ ⨾ θ)) (subTyTm-idEmb t ψ (thinR cθ ⨾ θ)))
          (cong (λ c → lam a (drop t) (cov c) ⇑[ out c , ψ ]) (cop-thin-⨾ cθ θ))
  subTyTm-idEmb (Lam (use t)) ψ θ =
    trans (cong (λ s → Lamᵇ (subTyTm t ψ s)) (lift-idS↾ θ)) (cong Lamᵇ (subTyTm-idEmb t ψ (os θ)))
  subTyTm-idEmb (Lam (drop t)) ψ θ = cong (λ Z → Lamᵇ (wkΘ-T Z)) (subTyTm-idEmb t ψ θ)
  subTyTm-idEmb (App e a cθ) ψ θ =
    trans (cong₂ Appᵇ (subTyTm-idEmb e ψ (thinL cθ ⨾ θ)) (sub-idEmb a (thinR cθ ⨾ θ)))
          (cong (λ c → App e a (cov c) ⇑[ out c , ψ ]) (cop-thin-⨾ cθ θ))

-- ── the shift bridges, for ⊢-wkΘ in SR ──
opaque
  unfolding TY.↑ₛ TY.wkSub TY.idS _⨾_
  ↑ₛ↾≡wkSub : ∀ {Δ sup}(θ : sup ⊑ Δ) → TY.↑ₛ TY.↾ θ ≡ TY.wkSub (TY.idS TY.↾ θ)
  ↑ₛ↾≡wkSub θ = funext λ p → refl

⟪↑ₛ⟫≡wk↑ : ∀ {Θ}(B : Ty ↑ Θ) → B TY.⟪ TY.↑ₛ ⟫ ≡ wk↑ tt B
⟪↑ₛ⟫≡wk↑ B = trans (cong (B TY.⟪_⟫) ↑ₛ≡wkSubidS) (sub-wkSub B TY.idS)

subTyTm-shift : ∀ {Θ Δ Γ′ Γ}(t : Tm Θ Γ′)(φ : Γ′ ⊑ Γ)(θ : Θ ⊑ Δ)
              → subTyTm t φ (TY.↑ₛ TY.↾ θ) ≡ wkΘ-T (t ⇑[ θ , φ ])
subTyTm-shift t φ θ =
  trans (cong (subTyTm t φ) (↑ₛ↾≡wkSub θ))
        (trans (subTyTm-wkΘ t φ (TY.idS TY.↾ θ)) (cong wkΘ-T (subTyTm-idEmb t φ θ)))
