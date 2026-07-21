{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.F.TmLaws — the σ-calculus laws for System F TERMS (the term-sub engine).
--
-- The same ACCL/σ_SP laws as the type level (Clean.F.TyLaws), but for the
-- BI-SCOPED term-sub `subTm`/`_⟪_⟫`/`_⨟_`: the type scope Θ rides along untouched,
-- only the TERM scope is substituted.  Registered conf-0.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.TmLaws where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Agda.Builtin.Equality.Rewrite
open import Clean.F.Ty using (Ty)
open import Clean.F.TmSub public

-- ── the funext+refl block (VarCons/ShiftCons/Map/IdL/IdCons/SCons) ──
opaque
  unfolding _∙_ ↑ₛ idS
  IdCons : ∀ {Θ Γ} → (var₀ᵇ ∙ ↑ₛ) ≡ idS {Θ} {tt ∷ Γ}
  IdCons = funext go
    where go : ∀ {Θ Γ}(p : Pos (tt ∷ Γ)) → (var₀ᵇ ∙ ↑ₛ {Θ}) p ≡ idS p
          go (os q) = cong (λ z → tmvar ⇑[ oe , os z ]) (sym (oe-uniq q))
          go (o' q) = refl

opaque
  unfolding _⟪_⟫ subTm _∙_
  VarCons : ∀ {Θ Δ Γ}(u : Bi Tm Θ Δ)(σ : TmSub Θ Δ Γ) → var₀ᵇ ⟪ u ∙ σ ⟫ ≡ u
  VarCons u σ = refl

opaque
  unfolding _⨟_ _⟪_⟫ subTm ↑ₛ _∙_
  ShiftCons : ∀ {Θ Δ Γ}(u : Bi Tm Θ Δ)(σ : TmSub Θ Δ Γ) → ↑ₛ ⨟ (u ∙ σ) ≡ σ
  ShiftCons u σ = funext λ p → refl

opaque
  unfolding _⨟_ _∙_
  Map : ∀ {Θ Γ Δ Ξ}(u : Bi Tm Θ Δ)(σ : TmSub Θ Δ Γ)(τ : TmSub Θ Ξ Δ)
      → (u ∙ σ) ⨟ τ ≡ (u ⟪ τ ⟫) ∙ (σ ⨟ τ)
  Map u σ τ = funext λ { (os p) → refl ; (o' p) → refl }

opaque
  unfolding _⨟_ _⟪_⟫ subTm idS
  IdL : ∀ {Θ Δ Γ}(σ : TmSub Θ Δ Γ) → idS ⨟ σ ≡ σ
  IdL σ = funext λ p → refl

opaque
  unfolding _⨟_ _⟪_⟫ subTm ↑ₛ _∙_ idS
  SCons : ∀ {Θ Δ Γ}(σ : TmSub Θ Δ (tt ∷ Γ)) → (var₀ᵇ ⟪ σ ⟫) ∙ (↑ₛ ⨟ σ) ≡ σ
  SCons σ = funext λ { (os q) → cong (λ z → σ (os z)) (sym (oe-uniq q)) ; (o' q) → refl }

-- ── the lift/idS commutations (term + type lift) ──
opaque
  unfolding _∙_ idS _⨾_
  liftΓ-idS↾ : ∀ {Θ sup Γ}(ψ : sup ⊑ Γ) → liftΓ {Θ} (idS ↾ ψ) ≡ idS ↾ (os ψ)
  liftΓ-idS↾ ψ = funext λ { (os q) → cong (λ z → tmvar ⇑[ oe , os z ]) (sym (oe-uniq (q ⨾ ψ)))
                          ; (o' q) → refl }
  liftΘ-idS↾ : ∀ {Θ sup Γ}(ψ : sup ⊑ Γ) → liftΘ {Θ} (idS ↾ ψ) ≡ idS ↾ ψ
  liftΘ-idS↾ ψ = funext λ p → cong (λ z → tmvar ⇑[ z , p ⨾ ψ ]) (oe-uniq (o' oe))

-- ── IdSubst : subTm with the identity-embedding is the embedding (the bi-scoped sub-idEmb) ──
opaque
  unfolding subTm _⟪_⟫ idS
  subTm-idEmb : ∀ {Θ Θ′ Γ sup}(t : Tm Θ′ sup)(φ : Θ′ ⊑ Θ)(ψ : sup ⊑ Γ)
              → subTm t φ (idS ↾ ψ) ≡ t ⇑[ φ , ψ ]
  subTm-idEmb tmvar φ ψ = cong (λ z → tmvar ⇑[ z , ψ ]) (sym (oe-uniq φ))
  subTm-idEmb (app l r cθ cγ) φ ψ =
    trans (cong₂ appᵇ (subTm-idEmb l (thinL cθ ⨾ φ) (thinL cγ ⨾ ψ))
                      (subTm-idEmb r (thinR cθ ⨾ φ) (thinR cγ ⨾ ψ)))
          (cong₂ (λ cΘ cΓ → app l r (cov cΘ) (cov cΓ) ⇑[ out cΘ , out cΓ ])
                 (cop-thin-⨾ cθ φ) (cop-thin-⨾ cγ ψ))
  subTm-idEmb (lam a (use t) cθ) φ ψ =
    trans (cong (λ s → lamᵇ (a ⇑ (thinL cθ ⨾ φ)) (subTm t (thinR cθ ⨾ φ) s)) (liftΓ-idS↾ ψ))
          (trans (cong (lamᵇ (a ⇑ (thinL cθ ⨾ φ))) (subTm-idEmb t (thinR cθ ⨾ φ) (os ψ)))
                 (cong (λ c → lam a (use t) (cov c) ⇑[ out c , ψ ]) (cop-thin-⨾ cθ φ)))
  subTm-idEmb (lam a (drop t) cθ) φ ψ =
    trans (cong (λ Z → lamᵇ (a ⇑ (thinL cθ ⨾ φ)) (wkΓ-T Z)) (subTm-idEmb t (thinR cθ ⨾ φ) ψ))
          (cong (λ c → lam a (drop t) (cov c) ⇑[ out c , ψ ]) (cop-thin-⨾ cθ φ))
  subTm-idEmb (Lam (use t)) φ ψ =
    trans (cong (λ s → Lamᵇ (subTm t (os φ) s)) (liftΘ-idS↾ ψ))
          (cong Lamᵇ (subTm-idEmb t (os φ) ψ))
  subTm-idEmb (Lam (drop t)) φ ψ = cong (λ Z → Lamᵇ (wkΘ-T Z)) (subTm-idEmb t φ ψ)
  subTm-idEmb (App e a cθ) φ ψ =
    trans (cong (λ Z → Appᵇ Z (a ⇑ (thinR cθ ⨾ φ))) (subTm-idEmb e (thinL cθ ⨾ φ) ψ))
          (cong (λ c → App e a (cov c) ⇑[ out c , ψ ]) (cop-thin-⨾ cθ φ))

  IdSubst : ∀ {Θ Γ}(u : Bi Tm Θ Γ) → u ⟪ idS ⟫ ≡ u
  IdSubst (t ⇑[ φ , ψ ]) = subTm-idEmb t φ ψ

opaque
  unfolding _⨟_
  IdR : ∀ {Θ Δ Γ}(σ : TmSub Θ Δ Γ) → σ ⨟ idS ≡ σ
  IdR σ = funext λ p → IdSubst (σ p)

-- ── register the foundational term-σ laws (Clos/Ass/lift-def follow once fusion lands) ──
{-# REWRITE IdCons VarCons ShiftCons Map IdL IdR SCons IdSubst #-}

-- ════════════════════════════════════════════════════════════════════════════
-- FUSION INFRASTRUCTURE (towards Clos).  Mirrors TyLaws' sub-thin/lift-⨟/sub-fusion,
-- but bi-scoped: renaming `_⟨_,_⟩b` carries TWO thinnings; each smart constructor
-- recomputes covers, so renaming distributes via `cop-⨾` on each scope.
-- ════════════════════════════════════════════════════════════════════════════

-- ── renaming distributes over the smart constructors (via cop-⨾) ──
opaque
  unfolding _⨾_
  appᵇ-⟨⟩b : ∀ {Θ Γ Θ′ Γ′}(X Y : Bi Tm Θ Γ)(ψΘ : Θ ⊑ Θ′)(ψΓ : Γ ⊑ Γ′)
           → (appᵇ X Y) ⟨ ψΘ , ψΓ ⟩b ≡ appᵇ (X ⟨ ψΘ , ψΓ ⟩b) (Y ⟨ ψΘ , ψΓ ⟩b)
  appᵇ-⟨⟩b (x ⇑[ θx , φx ]) (y ⇑[ θy , φy ]) ψΘ ψΓ =
    sym (cong₂ (λ cΘ cΓ → app x y (cov cΘ) (cov cΓ) ⇑[ out cΘ , out cΓ ])
               (cop-⨾ θx θy ψΘ) (cop-⨾ φx φy ψΓ))

  Appᵇ-⟨⟩b : ∀ {Θ Γ Θ′ Γ′}(E : Bi Tm Θ Γ)(a : Ty ↑ Θ)(ψΘ : Θ ⊑ Θ′)(ψΓ : Γ ⊑ Γ′)
           → (Appᵇ E a) ⟨ ψΘ , ψΓ ⟩b ≡ Appᵇ (E ⟨ ψΘ , ψΓ ⟩b) (a ⟨ ψΘ ⟩)
  Appᵇ-⟨⟩b (e ⇑[ θe , φ ]) (a ⇑ θa) ψΘ ψΓ =
    sym (cong (λ c → App e a (cov c) ⇑[ out c , φ ⨾ ψΓ ]) (cop-⨾ θe θa ψΘ))

  lamᵇ-⟨⟩b : ∀ {Θ Γ Θ′ Γ′}(A : Ty ↑ Θ)(X : Bi Tm Θ (tt ∷ Γ))(ψΘ : Θ ⊑ Θ′)(ψΓ : Γ ⊑ Γ′)
           → (lamᵇ A X) ⟨ ψΘ , ψΓ ⟩b ≡ lamᵇ (A ⟨ ψΘ ⟩) (X ⟨ ψΘ , os ψΓ ⟩b)
  lamᵇ-⟨⟩b (a ⇑ θa) (t ⇑[ θᵦ , os φ ]) ψΘ ψΓ =
    sym (cong (λ c → lam a (use t) (cov c) ⇑[ out c , φ ⨾ ψΓ ]) (cop-⨾ θa θᵦ ψΘ))
  lamᵇ-⟨⟩b (a ⇑ θa) (t ⇑[ θᵦ , o' φ ]) ψΘ ψΓ =
    sym (cong (λ c → lam a (drop t) (cov c) ⇑[ out c , φ ⨾ ψΓ ]) (cop-⨾ θa θᵦ ψΘ))

  Lamᵇ-⟨⟩b : ∀ {Θ Γ Θ′ Γ′}(X : Bi Tm (tt ∷ Θ) Γ)(ψΘ : Θ ⊑ Θ′)(ψΓ : Γ ⊑ Γ′)
           → (Lamᵇ X) ⟨ ψΘ , ψΓ ⟩b ≡ Lamᵇ (X ⟨ os ψΘ , ψΓ ⟩b)
  Lamᵇ-⟨⟩b (t ⇑[ os θ , φ ]) ψΘ ψΓ = refl
  Lamᵇ-⟨⟩b (t ⇑[ o' θ , φ ]) ψΘ ψΓ = refl

-- ── rename the TERM scope of a sub's targets, and the lift-commutation (renaming-natural) ──
thinSubΓ : ∀ {Θ Δ Δ′ Γ} → Δ ⊑ Δ′ → TmSub Θ Δ Γ → TmSub Θ Δ′ Γ
thinSubΓ ψ σ p = (σ p) ⟨ oi , ψ ⟩b

opaque
  unfolding _∙_ idS _⨾_
  lift-thinSubΓ : ∀ {Θ Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(σ : TmSub Θ Δ Γ)
                → liftΓ (thinSubΓ ψ σ) ≡ thinSubΓ (os ψ) (liftΓ σ)
  lift-thinSubΓ ψ σ = funext λ { (os p) → cong (λ z → tmvar ⇑[ oe , os z ]) (sym (oe-uniq (oe ⨾ ψ)))
                               ; (o' p) → refl }

-- the lam-DROP renaming distribution: push ⟨ψ⟩b INSIDE wkΓ-T (the o' stays explicit,
-- so the smart-ctor dispatches and `⨾oi` fires under opacity) — refl, no `_⨾_` unfold.
lamᵇ-drop-⟨⟩Γ : ∀ {Θ Γ Γ′}(A : Ty ↑ Θ)(Z : Bi Tm Θ Γ)(ψ : Γ ⊑ Γ′)
              → (lamᵇ A (wkΓ-T Z)) ⟨ oi , ψ ⟩b ≡ lamᵇ A (wkΓ-T (Z ⟨ oi , ψ ⟩b))
lamᵇ-drop-⟨⟩Γ (a ⇑ θa) (z ⇑[ θz , φz ]) ψ = refl

-- Lam-renaming at ψΘ = oi, stated with LITERAL oi (so `θ ⨾ oi` fires `⨾oi`, unlike the
-- `os oi` that the general Lamᵇ-⟨⟩b would produce) — refl, dispatching on the type binder.
Lamᵇ-⟨⟩Γ : ∀ {Θ Γ Γ′}(X : Bi Tm (tt ∷ Θ) Γ)(ψ : Γ ⊑ Γ′)
         → (Lamᵇ X) ⟨ oi , ψ ⟩b ≡ Lamᵇ (X ⟨ oi , ψ ⟩b)
Lamᵇ-⟨⟩Γ (t ⇑[ os θ , φ ]) ψ = refl
Lamᵇ-⟨⟩Γ (t ⇑[ o' θ , φ ]) ψ = refl

-- ── subTm-thinΓ : subTm commutes with TERM-scope renaming (the bi-scoped sub-thin) ──
opaque
  unfolding subTm
  subTm-thinΓ : ∀ {Θ Θ′ Δ Δ′ sup}(t : Tm Θ′ sup)(φ : Θ′ ⊑ Θ)(ψ : Δ ⊑ Δ′)(σ : TmSub Θ Δ sup)
              → subTm t φ (thinSubΓ ψ σ) ≡ (subTm t φ σ) ⟨ oi , ψ ⟩b
  subTm-thinΓ tmvar φ ψ σ = refl
  subTm-thinΓ (app l r cθ cγ) φ ψ σ =
    trans (cong₂ appᵇ (subTm-thinΓ l (thinL cθ ⨾ φ) ψ (selL cγ σ))
                      (subTm-thinΓ r (thinR cθ ⨾ φ) ψ (selR cγ σ)))
          (sym (appᵇ-⟨⟩b (subTm l (thinL cθ ⨾ φ) (selL cγ σ)) (subTm r (thinR cθ ⨾ φ) (selR cγ σ)) oi ψ))
  subTm-thinΓ (lam a (use t) cθ) φ ψ σ =
    trans (cong (λ s → lamᵇ (a ⇑ (thinL cθ ⨾ φ)) (subTm t (thinR cθ ⨾ φ) s)) (lift-thinSubΓ ψ σ))
          (trans (cong (lamᵇ (a ⇑ (thinL cθ ⨾ φ))) (subTm-thinΓ t (thinR cθ ⨾ φ) (os ψ) (liftΓ σ)))
                 (sym (lamᵇ-⟨⟩b (a ⇑ (thinL cθ ⨾ φ)) (subTm t (thinR cθ ⨾ φ) (liftΓ σ)) oi ψ)))
  subTm-thinΓ (lam a (drop t) cθ) φ ψ σ =
    trans (cong (λ Z → lamᵇ (a ⇑ (thinL cθ ⨾ φ)) (wkΓ-T Z)) (subTm-thinΓ t (thinR cθ ⨾ φ) ψ σ))
          (sym (lamᵇ-drop-⟨⟩Γ (a ⇑ (thinL cθ ⨾ φ)) (subTm t (thinR cθ ⨾ φ) σ) ψ))
  subTm-thinΓ (Lam (use t)) φ ψ σ =
    trans (cong Lamᵇ (subTm-thinΓ t (os φ) ψ (liftΘ σ)))
          (sym (Lamᵇ-⟨⟩Γ (subTm t (os φ) (liftΘ σ)) ψ))
  subTm-thinΓ (Lam (drop t)) φ ψ σ =
    trans (cong (λ Z → Lamᵇ (wkΘ-T Z)) (subTm-thinΓ t φ ψ σ))
          (sym (Lamᵇ-⟨⟩Γ (wkΘ-T (subTm t φ σ)) ψ))
  subTm-thinΓ (App e a cθ) φ ψ σ =
    trans (cong (λ Z → Appᵇ Z (a ⇑ (thinR cθ ⨾ φ))) (subTm-thinΓ e (thinL cθ ⨾ φ) ψ σ))
          (sym (Appᵇ-⟨⟩b (subTm e (thinL cθ ⨾ φ) σ) (a ⇑ (thinR cθ ⨾ φ)) oi ψ))

-- bridge: the single-var term-weakening IS the bi-scoped renaming by (oi , o' oi)
wkΓ-T≡⟨⟩b : ∀ {Θ Γ}(u : Bi Tm Θ Γ) → wkΓ-T u ≡ u ⟨ oi , o' oi ⟩b
wkΓ-T≡⟨⟩b (s ⇑[ a , b ]) = cong (λ y → s ⇑[ a , y ]) (sym (⨾-o' tt b oi))

-- ── term-weakening of a sub commutes (sub-wkΓSub = subTm-thinΓ at o' oi); wkΓ-skip ──
opaque
  unfolding _⟪_⟫
  sub-wkΓSub : ∀ {Θ Δ Γ}(u : Bi Tm Θ Γ)(τ : TmSub Θ Δ Γ) → u ⟪ wkΓ-Sub τ ⟫ ≡ wkΓ-T (u ⟪ τ ⟫)
  sub-wkΓSub (t ⇑[ θ , φ ]) τ =
    trans (cong (subTm t θ) (funext λ p → wkΓ-T≡⟨⟩b ((τ ↾ φ) p)))
          (trans (subTm-thinΓ t θ (o' oi) (τ ↾ φ)) (sym (wkΓ-T≡⟨⟩b (subTm t θ (τ ↾ φ)))))

opaque
  unfolding _⟪_⟫ subTm _∙_ _⨾_
  wkΓ-skip : ∀ {Θ Δ Γ}(u : Bi Tm Θ Γ)(v : Bi Tm Θ Δ)(ρ : TmSub Θ Δ Γ) → (wkΓ-T u) ⟪ v ∙ ρ ⟫ ≡ u ⟪ ρ ⟫
  wkΓ-skip (t ⇑[ θ , φ ]) v ρ = refl

-- ── liftΓ commutes with composition (the bi-scoped lift-⨟) ──
opaque
  unfolding _⨟_ _∙_
  liftΓ-⨟ : ∀ {Θ Γ Δ Ξ}(σ : TmSub Θ Δ Γ)(τ : TmSub Θ Ξ Δ) → (liftΓ σ) ⨟ (liftΓ τ) ≡ liftΓ (σ ⨟ τ)
  liftΓ-⨟ σ τ = funext λ { (os p) → refl
                         ; (o' p) → trans (wkΓ-skip (σ p) var₀ᵇ (wkΓ-Sub τ)) (sub-wkΓSub (σ p) τ) }

-- ── liftΓ and wkΘ-Sub commute (DIFFERENT scopes → TRUE, unlike same-scope) ──
opaque
  unfolding _∙_
  liftΓ-wkΘSub : ∀ {Θ Δ Γ}(ρ : TmSub Θ Δ Γ) → liftΓ (wkΘ-Sub ρ) ≡ wkΘ-Sub (liftΓ ρ)
  liftΓ-wkΘSub ρ = funext λ { (os p) → cong (λ z → tmvar ⇑[ z , os oe ]) (sym (oe-uniq (o' oe)))
                            ; (o' p) → refl }

-- ════════════════════════════════════════════════════════════════════════════
-- subTm-renΘ : subTm commutes with TYPE-scope renaming (rename φ AND σ by ξ, so the
-- Lam binder regeneralises ξ→os ξ — no exchange).  Mirror of subTm-thinΓ; the literal-
-- oi bookkeeping is now on the TERM scope (the lam binder), the general ξ on the type.
-- ════════════════════════════════════════════════════════════════════════════
thinSubΘ : ∀ {Θ Θ′ Δ Γ} → Θ ⊑ Θ′ → TmSub Θ Δ Γ → TmSub Θ′ Δ Γ
thinSubΘ ξ σ p = (σ p) ⟨ ξ , oi ⟩b

-- the lam distributions at ψΓ = oi, stated with LITERAL oi on the term scope
lamᵇ-⟨⟩Θ : ∀ {Θ Θ′ Γ}(A : Ty ↑ Θ)(X : Bi Tm Θ (tt ∷ Γ))(ξ : Θ ⊑ Θ′)
         → (lamᵇ A X) ⟨ ξ , oi ⟩b ≡ lamᵇ (A ⟨ ξ ⟩) (X ⟨ ξ , oi ⟩b)
lamᵇ-⟨⟩Θ (a ⇑ θa) (t ⇑[ θᵦ , os φ ]) ξ =
  sym (cong (λ c → lam a (use t) (cov c) ⇑[ out c , φ ]) (cop-⨾ θa θᵦ ξ))
lamᵇ-⟨⟩Θ (a ⇑ θa) (t ⇑[ θᵦ , o' φ ]) ξ =
  sym (cong (λ c → lam a (drop t) (cov c) ⇑[ out c , φ ]) (cop-⨾ θa θᵦ ξ))

lamᵇ-drop-⟨⟩Θ : ∀ {Θ Θ′ Γ}(A : Ty ↑ Θ)(Z : Bi Tm Θ Γ)(ξ : Θ ⊑ Θ′)
              → (lamᵇ A (wkΓ-T Z)) ⟨ ξ , oi ⟩b ≡ lamᵇ (A ⟨ ξ ⟩) (wkΓ-T (Z ⟨ ξ , oi ⟩b))
lamᵇ-drop-⟨⟩Θ (a ⇑ θa) (z ⇑[ θz , φz ]) ξ =
  sym (cong (λ c → lam a (drop z) (cov c) ⇑[ out c , φz ]) (cop-⨾ θa θz ξ))

-- the Lam-DROP distribution: push ⟨ξ⟩b INSIDE wkΘ-T (o' explicit, ⨾oi fires) — refl
Lamᵇ-drop-⟨⟩Θ : ∀ {Θ Θ′ Γ}(Y : Bi Tm Θ Γ)(ξ : Θ ⊑ Θ′)
              → (Lamᵇ (wkΘ-T Y)) ⟨ ξ , oi ⟩b ≡ Lamᵇ (wkΘ-T (Y ⟨ ξ , oi ⟩b))
Lamᵇ-drop-⟨⟩Θ (y ⇑[ θ , φ ]) ξ = refl

-- the two lift naturalities for the type renaming
opaque
  unfolding _⨾_
  os-⨾ : ∀ {Γ Δ Θ}(φ : Γ ⊑ Δ)(ξ : Δ ⊑ Θ) → os φ ⨾ os ξ ≡ os (φ ⨾ ξ)
  os-⨾ φ ξ = refl
  lift-thinSubΘ : ∀ {Θ Θ′ Δ Γ}(ξ : Θ ⊑ Θ′)(σ : TmSub Θ Δ Γ)
                → liftΘ (thinSubΘ ξ σ) ≡ thinSubΘ (os ξ) (liftΘ σ)
  lift-thinSubΘ ξ σ = funext λ p → refl

opaque
  unfolding _∙_
  liftΓ-thinSubΘ : ∀ {Θ Θ′ Δ Γ}(ξ : Θ ⊑ Θ′)(σ : TmSub Θ Δ Γ)
                 → liftΓ (thinSubΘ ξ σ) ≡ thinSubΘ ξ (liftΓ σ)
  liftΓ-thinSubΘ ξ σ = funext λ { (os p) → refl ; (o' p) → refl }

opaque
  unfolding subTm
  subTm-renΘ : ∀ {Θ Θ′ Θ″ Δ sup}(t : Tm Θ″ sup)(φ : Θ″ ⊑ Θ)(ξ : Θ ⊑ Θ′)(σ : TmSub Θ Δ sup)
             → subTm t (φ ⨾ ξ) (thinSubΘ ξ σ) ≡ (subTm t φ σ) ⟨ ξ , oi ⟩b
  subTm-renΘ tmvar φ ξ σ = refl
  subTm-renΘ (app l r cθ cγ) φ ξ σ =
    trans (cong₂ appᵇ (subTm-renΘ l (thinL cθ ⨾ φ) ξ (selL cγ σ))
                      (subTm-renΘ r (thinR cθ ⨾ φ) ξ (selR cγ σ)))
          (sym (appᵇ-⟨⟩b (subTm l (thinL cθ ⨾ φ) (selL cγ σ)) (subTm r (thinR cθ ⨾ φ) (selR cγ σ)) ξ oi))
  subTm-renΘ (lam a (use t) cθ) φ ξ σ =
    trans (cong (λ s → lamᵇ (a ⇑ (thinL cθ ⨾ (φ ⨾ ξ))) (subTm t (thinR cθ ⨾ (φ ⨾ ξ)) s)) (liftΓ-thinSubΘ ξ σ))
          (trans (cong (lamᵇ (a ⇑ (thinL cθ ⨾ (φ ⨾ ξ)))) (subTm-renΘ t (thinR cθ ⨾ φ) ξ (liftΓ σ)))
                 (sym (lamᵇ-⟨⟩Θ (a ⇑ (thinL cθ ⨾ φ)) (subTm t (thinR cθ ⨾ φ) (liftΓ σ)) ξ)))
  subTm-renΘ (lam a (drop t) cθ) φ ξ σ =
    trans (cong (λ Z → lamᵇ (a ⇑ (thinL cθ ⨾ (φ ⨾ ξ))) (wkΓ-T Z)) (subTm-renΘ t (thinR cθ ⨾ φ) ξ σ))
          (sym (lamᵇ-drop-⟨⟩Θ (a ⇑ (thinL cθ ⨾ φ)) (subTm t (thinR cθ ⨾ φ) σ) ξ))
  subTm-renΘ (Lam (use t)) φ ξ σ =
    trans (cong (λ z → Lamᵇ (subTm t z (liftΘ (thinSubΘ ξ σ)))) (sym (os-⨾ φ ξ)))
    (trans (cong (λ s → Lamᵇ (subTm t (os φ ⨾ os ξ) s)) (lift-thinSubΘ ξ σ))
    (trans (cong Lamᵇ (subTm-renΘ t (os φ) (os ξ) (liftΘ σ)))
           (sym (Lamᵇ-⟨⟩b (subTm t (os φ) (liftΘ σ)) ξ oi))))
  subTm-renΘ (Lam (drop t)) φ ξ σ =
    trans (cong (λ Z → Lamᵇ (wkΘ-T Z)) (subTm-renΘ t φ ξ σ))
          (sym (Lamᵇ-drop-⟨⟩Θ (subTm t φ σ) ξ))
  subTm-renΘ (App e a cθ) φ ξ σ =
    trans (cong (λ Z → Appᵇ Z (a ⇑ (thinR cθ ⨾ (φ ⨾ ξ)))) (subTm-renΘ e (thinL cθ ⨾ φ) ξ σ))
          (sym (Appᵇ-⟨⟩b (subTm e (thinL cθ ⨾ φ) σ) (a ⇑ (thinR cθ ⨾ φ)) ξ oi))

-- bridge: type-weakening = renaming by (o' oi , oi)
wkΘ-T≡⟨⟩b : ∀ {Θ Γ}(u : Bi Tm Θ Γ) → wkΘ-T u ≡ u ⟨ o' oi , oi ⟩b
wkΘ-T≡⟨⟩b (s ⇑[ a , b ]) = cong (λ x → s ⇑[ x , b ]) (sym (⨾-o' tt a oi))

-- subTm commutes with type-weakening (subTm-level + Bi-level), from subTm-renΘ at o' oi
sub-wkΘSub-tm : ∀ {Θ Θ′ Δ sup}(t : Tm Θ′ sup)(θ : Θ′ ⊑ Θ)(ρ : TmSub Θ Δ sup)
              → subTm t (o' θ) (wkΘ-Sub ρ) ≡ wkΘ-T (subTm t θ ρ)
sub-wkΘSub-tm t θ ρ =
  trans (cong (subTm t (o' θ)) (funext λ p → wkΘ-T≡⟨⟩b (ρ p)))
  (trans (cong (λ z → subTm t z (thinSubΘ (o' oi) ρ)) (sym (⨾-o' tt θ oi)))
  (trans (subTm-renΘ t θ (o' oi) ρ) (sym (wkΘ-T≡⟨⟩b (subTm t θ ρ)))))

opaque
  unfolding _⟪_⟫
  sub-wkΘSub-bi : ∀ {Θ Δ Γ}(u : Bi Tm Θ Γ)(τ : TmSub Θ Δ Γ) → (wkΘ-T u) ⟪ wkΘ-Sub τ ⟫ ≡ wkΘ-T (u ⟪ τ ⟫)
  sub-wkΘSub-bi (t ⇑[ θ , φ ]) τ = sub-wkΘSub-tm t θ (τ ↾ φ)

-- ── liftΘ commutes with composition (now via subTm-renΘ at o' oi) ──
opaque
  unfolding _⨟_ _⟪_⟫
  liftΘ-⨟ : ∀ {Θ Γ Δ Ξ}(σ : TmSub Θ Δ Γ)(τ : TmSub Θ Ξ Δ) → (liftΘ σ) ⨟ (liftΘ τ) ≡ liftΘ (σ ⨟ τ)
  liftΘ-⨟ σ τ = funext λ p → sub-wkΘSub-bi (σ p) τ

-- ════════════════════════════════════════════════════════════════════════════
-- FUSION (Clos): the binder distributions lamᵇ-⟪⟫/Lamᵇ-⟪⟫, then subTm-fusion.
-- ════════════════════════════════════════════════════════════════════════════

-- lift-restriction commutations
opaque
  unfolding _∙_ _⨾_
  liftΓ-↾ : ∀ {Θ Δ sup Γ}(τ : TmSub Θ Δ Γ)(φ : sup ⊑ Γ) → liftΓ (τ ↾ φ) ≡ liftΓ τ ↾ os φ
  liftΓ-↾ τ φ = funext λ { (os q) → refl ; (o' q) → refl }
  liftΓ-↾-o' : ∀ {Θ Δ sup Γ}(τ : TmSub Θ Δ Γ)(φ : sup ⊑ Γ) → liftΓ τ ↾ o' φ ≡ wkΓ-Sub (τ ↾ φ)
  liftΓ-↾-o' τ φ = funext λ p → refl
liftΘ-↾ : ∀ {Θ Δ sup Γ}(τ : TmSub Θ Δ Γ)(φ : sup ⊑ Γ) → liftΘ (τ ↾ φ) ≡ liftΘ τ ↾ φ
liftΘ-↾ τ φ = refl

-- subTm-level term-weakening naturality (from subTm-thinΓ at o' oi)
sub-wkΓSub-tm : ∀ {Θ Θ′ Δ sup}(t : Tm Θ′ sup)(θ : Θ′ ⊑ Θ)(ρ : TmSub Θ Δ sup)
              → subTm t θ (wkΓ-Sub ρ) ≡ wkΓ-T (subTm t θ ρ)
sub-wkΓSub-tm t θ ρ =
  trans (cong (subTm t θ) (funext λ p → wkΓ-T≡⟨⟩b (ρ p)))
        (trans (subTm-thinΓ t θ (o' oi) ρ) (sym (wkΓ-T≡⟨⟩b (subTm t θ ρ))))

-- the non-binder distributions (definitional via Fac-L); lam/Lam split the binder
opaque
  unfolding _⟪_⟫ subTm _↾_
  appᵇ-⟪⟫ : ∀ {Θ Δ Γ}(X Y : Bi Tm Θ Γ)(τ : TmSub Θ Δ Γ) → (appᵇ X Y) ⟪ τ ⟫ ≡ appᵇ (X ⟪ τ ⟫) (Y ⟪ τ ⟫)
  appᵇ-⟪⟫ (x ⇑[ θx , φx ]) (y ⇑[ θy , φy ]) τ = refl
  Appᵇ-⟪⟫ : ∀ {Θ Δ Γ}(E : Bi Tm Θ Γ)(a : Ty ↑ Θ)(τ : TmSub Θ Δ Γ) → (Appᵇ E a) ⟪ τ ⟫ ≡ Appᵇ (E ⟪ τ ⟫) a
  Appᵇ-⟪⟫ (e ⇑[ θe , φe ]) a τ = refl

opaque
  unfolding _⟪_⟫ subTm
  lamᵇ-⟪⟫ : ∀ {Θ Δ Γ}(A : Ty ↑ Θ)(Y : Bi Tm Θ (tt ∷ Γ))(τ : TmSub Θ Δ Γ)
          → (lamᵇ A Y) ⟪ τ ⟫ ≡ lamᵇ A (Y ⟪ liftΓ τ ⟫)
  lamᵇ-⟪⟫ (a ⇑ θa) (t ⇑[ θᵦ , os φ ]) τ =
    cong (λ s → lamᵇ (a ⇑ θa) (subTm t θᵦ s)) (liftΓ-↾ τ φ)
  lamᵇ-⟪⟫ (a ⇑ θa) (t ⇑[ θᵦ , o' φ ]) τ =
    trans (cong (lamᵇ (a ⇑ θa)) (sym (sub-wkΓSub-tm t θᵦ (τ ↾ φ))))
          (cong (λ s → lamᵇ (a ⇑ θa) (subTm t θᵦ s)) (sym (liftΓ-↾-o' τ φ)))

  Lamᵇ-⟪⟫ : ∀ {Θ Δ Γ}(Y : Bi Tm (tt ∷ Θ) Γ)(τ : TmSub Θ Δ Γ)
          → (Lamᵇ Y) ⟪ τ ⟫ ≡ Lamᵇ (Y ⟪ wkΘ-Sub τ ⟫)
  Lamᵇ-⟪⟫ (t ⇑[ os θ , φ ]) τ = refl
  Lamᵇ-⟪⟫ (t ⇑[ o' θ , φ ]) τ = cong Lamᵇ (sym (sub-wkΘSub-tm t θ (τ ↾ φ)))

-- subTm-fusion (Clos at the engine level) + Clos + Ass
opaque
  unfolding _⟪_⟫ subTm _⨟_
  subTm-fusion : ∀ {Θ Θ′ Δ Ξ sup}(t : Tm Θ′ sup)(φ : Θ′ ⊑ Θ)(σ : TmSub Θ Δ sup)(τ : TmSub Θ Ξ Δ)
               → (subTm t φ σ) ⟪ τ ⟫ ≡ subTm t φ (σ ⨟ τ)
  subTm-fusion tmvar φ σ τ = refl
  subTm-fusion (app l r cθ cγ) φ σ τ =
    trans (appᵇ-⟪⟫ (subTm l (thinL cθ ⨾ φ) (selL cγ σ)) (subTm r (thinR cθ ⨾ φ) (selR cγ σ)) τ)
          (cong₂ appᵇ (subTm-fusion l (thinL cθ ⨾ φ) (selL cγ σ) τ)
                      (subTm-fusion r (thinR cθ ⨾ φ) (selR cγ σ) τ))
  subTm-fusion (lam a (use t) cθ) φ σ τ =
    trans (lamᵇ-⟪⟫ (a ⇑ (thinL cθ ⨾ φ)) (subTm t (thinR cθ ⨾ φ) (liftΓ σ)) τ)
          (cong (lamᵇ (a ⇑ (thinL cθ ⨾ φ)))
                (trans (subTm-fusion t (thinR cθ ⨾ φ) (liftΓ σ) (liftΓ τ))
                       (cong (subTm t (thinR cθ ⨾ φ)) (liftΓ-⨟ σ τ))))
  subTm-fusion (lam a (drop t) cθ) φ σ τ =
    trans (lamᵇ-⟪⟫ (a ⇑ (thinL cθ ⨾ φ)) (wkΓ-T (subTm t (thinR cθ ⨾ φ) σ)) τ)
          (cong (lamᵇ (a ⇑ (thinL cθ ⨾ φ)))
                (trans (wkΓ-skip (subTm t (thinR cθ ⨾ φ) σ) var₀ᵇ (wkΓ-Sub τ))
                (trans (sub-wkΓSub (subTm t (thinR cθ ⨾ φ) σ) τ)
                       (cong wkΓ-T (subTm-fusion t (thinR cθ ⨾ φ) σ τ)))))
  subTm-fusion (Lam (use t)) φ σ τ =
    trans (Lamᵇ-⟪⟫ (subTm t (os φ) (liftΘ σ)) τ)
          (cong Lamᵇ (trans (subTm-fusion t (os φ) (liftΘ σ) (liftΘ τ))
                            (cong (subTm t (os φ)) (liftΘ-⨟ σ τ))))
  subTm-fusion (Lam (drop t)) φ σ τ =
    trans (Lamᵇ-⟪⟫ (wkΘ-T (subTm t φ σ)) τ)
          (cong Lamᵇ (trans (sub-wkΘSub-bi (subTm t φ σ) τ)
                            (cong wkΘ-T (subTm-fusion t φ σ τ))))
  subTm-fusion (App e a cθ) φ σ τ =
    trans (Appᵇ-⟪⟫ (subTm e (thinL cθ ⨾ φ) σ) (a ⇑ (thinR cθ ⨾ φ)) τ)
          (cong (λ Z → Appᵇ Z (a ⇑ (thinR cθ ⨾ φ))) (subTm-fusion e (thinL cθ ⨾ φ) σ τ))

  Clos : ∀ {Θ Δ Ξ Γ}(u : Bi Tm Θ Γ)(σ : TmSub Θ Δ Γ)(τ : TmSub Θ Ξ Δ) → (u ⟪ σ ⟫) ⟪ τ ⟫ ≡ u ⟪ σ ⨟ τ ⟫
  Clos (t ⇑[ θ , φ ]) σ τ = subTm-fusion t θ (σ ↾ φ) τ

opaque
  unfolding _⨟_
  Ass : ∀ {Θ Γ Δ Δ′ Ξ}(σ : TmSub Θ Δ Γ)(τ : TmSub Θ Δ′ Δ)(υ : TmSub Θ Ξ Δ′) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
  Ass σ τ υ = funext λ p → Clos (σ p) τ υ

-- register fusion + associativity (the term σ-calculus is now closed)
{-# REWRITE Clos Ass #-}
