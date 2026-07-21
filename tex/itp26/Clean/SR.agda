{-# OPTIONS --rewriting #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Clean.SR — STLC subject reduction.  Reduction `_⟶_` (β + ξ-congruence) on
-- things-with-thinning; `preserve` via `sub-pres` on the β-environment `A ∙ idS`.
--
-- Separate module (registers NO rewrites; `--rewriting` only — preserve's
-- with-clauses would otherwise trip --local-confluence-check against the σ-laws).
-- The inversions are DEFINITIONAL: the structural context makes cohL/cohR (app)
-- and `rest (os/o' ξ)` (lam) compute, so there is no subst anywhere.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.SR where
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite
open import Clean.Sub
open import Clean.Typing

-- the identity substitution is well-typed (head ↦ ⊢fresh, tail ↦ wkSub of the rest)
opaque
  unfolding idS wkSub _⨾_
  idS-wt : ∀ {Γ}(Φ : Cx Γ) → WtSub idS Φ Φ
  idS-wt ε        = ⟨⟩
  idS-wt (Φ ,- A) = wkSub-pres (idS-wt Φ) ◂ ⊢fresh {Ψ = Φ}{A = A}

-- restriction by a thinning preserves well-typedness (the σ↾θ analogue of selL-pres)
opaque
  unfolding _⨾_
  rest-pres : ∀ {sup Γ Δ}{σ : Sub Δ Γ}{Φ Ψ}(θ : sup ⊑ Γ) → WtSub σ Φ Ψ → WtSub (σ ↾ θ) (rest θ Φ) Ψ
  rest-pres oz     ⟨⟩        = ⟨⟩
  rest-pres (os θ) (wt ◂ ⊢u) = rest-pres θ wt ◂ ⊢u
  rest-pres (o' θ) (wt ◂ ⊢u) = rest-pres θ wt

-- the β-environment  A ∙ idS  is well-typed (head ↦ ⊢A, tail ↦ idS-wt)
opaque
  unfolding _∙_
  β-wt : ∀ {Δ}{Φ : Cx Δ}{A′}(A : Tm ↑ Δ) → Φ ⊢↑ A ∶ A′ → WtSub (A ∙ idS) (Φ ,- A′) Φ
  β-wt {Φ = Φ} A ⊢A = idS-wt Φ ◂ ⊢A

-- substitution applied to a thing-with-thinning
opaque
  unfolding _⟪_⟫
  sub-pres↑ : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ Ψ}{X : Tm ↑ Γ}{A} → Φ ⊢↑ X ∶ A → WtSub σ Φ Ψ → Ψ ⊢↑ (X ⟪ σ ⟫) ∶ A
  sub-pres↑ {X = x ⇑ θ} ⊢X wt = sub-pres (rest-pres θ wt) ⊢X

-- ── INVERSIONS (definitional: cohL/cohR for app, structural rest for lam) ──
app↑-inv : ∀ {Δ}{Φ : Cx Δ}{B}(L R : Tm ↑ Δ) → Φ ⊢↑ app↑ L R ∶ B → Σ Ty λ A → (Φ ⊢↑ L ∶ (A ⇒ B)) × (Φ ⊢↑ R ∶ A)
app↑-inv (a ⇑ α) (b ⇑ β) (⊢app {A = A} ⊢a ⊢b) = A , ⊢a , ⊢b
lam↑-inv : ∀ {Δ}{Φ : Cx Δ}{C}(X : Tm ↑ (tt ∷ Δ)) → Φ ⊢↑ lam↑ X ∶ C → Σ Ty λ A → Σ Ty λ B → (C ≡ (A ⇒ B)) × ((Φ ,- A) ⊢↑ X ∶ B)
lam↑-inv (t ⇑ os ξ) (⊢lam  {A = A}{B = B} ⊢t) = A , B , refl , ⊢t
lam↑-inv (t ⇑ o' ξ) (⊢lamᵈ {A = A}{B = B} ⊢t) = A , B , refl , ⊢t

-- ── single-step reduction (β + congruence) ──
data _⟶_ : ∀ {Δ} → Tm ↑ Δ → Tm ↑ Δ → Set where
  β      : ∀ {Δ}(X : Tm ↑ (tt ∷ Δ))(A : Tm ↑ Δ) → app↑ (lam↑ X) A ⟶ X ⟪ A ∙ idS ⟫
  ξ-app₁ : ∀ {Δ}{L L′ R : Tm ↑ Δ} → L ⟶ L′ → app↑ L R ⟶ app↑ L′ R
  ξ-app₂ : ∀ {Δ}{L R R′ : Tm ↑ Δ} → R ⟶ R′ → app↑ L R ⟶ app↑ L R′
  ξ-lam  : ∀ {Δ}{X X′ : Tm ↑ (tt ∷ Δ)} → X ⟶ X′ → lam↑ X ⟶ lam↑ X′
infix 3 _⟶_

-- ── SUBJECT REDUCTION ──
preserve : ∀ {Δ}{Φ : Cx Δ}{B}{e e′ : Tm ↑ Δ} → Φ ⊢↑ e ∶ B → e ⟶ e′ → Φ ⊢↑ e′ ∶ B
preserve ⊢e (β X A) with app↑-inv (lam↑ X) A ⊢e
... | A′ , ⊢lamX , ⊢A with lam↑-inv X ⊢lamX
...   | _ , _ , refl , ⊢X = sub-pres↑ ⊢X (β-wt A ⊢A)
preserve ⊢e (ξ-app₁ {L = L}{L′ = L′}{R = R} L⟶) with app↑-inv L R ⊢e
... | A′ , ⊢L , ⊢R = ⊢app↑ {L = L′}{R = R} (preserve ⊢L L⟶) ⊢R
preserve ⊢e (ξ-app₂ {L = L}{R = R}{R′ = R′} R⟶) with app↑-inv L R ⊢e
... | A′ , ⊢L , ⊢R = ⊢app↑ {L = L}{R = R′} ⊢L (preserve ⊢R R⟶)
preserve ⊢e (ξ-lam {X = X}{X′ = X′} X⟶) with lam↑-inv X ⊢e
... | A , _ , refl , ⊢X = ⊢lam↑ {X = X′} (preserve ⊢X X⟶)
