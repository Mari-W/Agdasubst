{-# OPTIONS --rewriting #-}
-- Sf.STLCSigmaSR — STLC subject reduction on the functional σ-calculus.  Separate
-- module: it REGISTERS no rewrites (only USES them), and preserve's with-clauses
-- would otherwise trip --local-confluence-check against the σ-laws.
module Sf.STLCSigmaSR where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Agda.Builtin.Equality.Rewrite
open import Sf.Scaffold ⊤
open import Sf.Fac ⊤
open import Sf.STLCSigma

-- ════════════════════════════════════════════════════════════════════════════
-- §5  SUBJECT REDUCTION.  β-reduction + congruence; preservation via sub-pres↑.
-- Inversions are DEFINITIONAL: ⊢app↑ peels via Fac-L, ⊢lam↑ via the ∙ᶜ-coherence.
-- ════════════════════════════════════════════════════════════════════════════
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)

app↑-inv : ∀ {Δ}{Φ : Ctx Δ}{B}(L R : Tm ↑ Δ)
         → Φ ⊢↑ app↑ L R ∶ B → Σ Ty λ A → (Φ ⊢↑ L ∶ (A ⇒ B)) × (Φ ⊢↑ R ∶ A)
app↑-inv (a ⇑ α) (b ⇑ β) (⊢app {A = A} ⊢a ⊢b) = A , ⊢a , ⊢b

lam↑-inv : ∀ {Δ}{Φ : Ctx Δ}{C}(X : Tm ↑ (tt ∷ Δ)) → Φ ⊢↑ lam↑ X ∶ C
         → Σ Ty λ A → Σ Ty λ B → (C ≡ (A ⇒ B)) × ((A ∙ᶜ Φ) ⊢↑ X ∶ B)
lam↑-inv {Φ = Φ} (t ⇑ os ξ) (⊢lam  {A = A}{B = B} ⊢t) = A , B , refl , subst (λ Ξ → Ξ ⊢ t ∶ B) (sym (∙ᶜ-os A Φ ξ)) ⊢t
lam↑-inv {Φ = Φ} (t ⇑ o' ξ) (⊢lamᵈ {A = A}{B = B} ⊢t) = A , B , refl , subst (λ Ξ → Ξ ⊢ t ∶ B) (sym (∙ᶜ-o' A Φ ξ)) ⊢t

-- single-step reduction (β + congruence)
data _⟶_ : ∀ {Δ} → Tm ↑ Δ → Tm ↑ Δ → Set where
  β     : ∀ {Δ}(X : Tm ↑ (tt ∷ Δ))(A : Tm ↑ Δ) → app↑ (lam↑ X) A ⟶ X ⟪ A ∙ idS ⟫
  ξ-app₁ : ∀ {Δ}{L L′ R : Tm ↑ Δ} → L ⟶ L′ → app↑ L R ⟶ app↑ L′ R
  ξ-app₂ : ∀ {Δ}{L R R′ : Tm ↑ Δ} → R ⟶ R′ → app↑ L R ⟶ app↑ L R′
  ξ-lam  : ∀ {Δ}{X X′ : Tm ↑ (tt ∷ Δ)} → X ⟶ X′ → lam↑ X ⟶ lam↑ X′
infix 3 _⟶_

-- THE SUBSTITUTION σ = A ∙ id used by β is well-typed (head ↦ ⊢A, tail ↦ ⊢var)
opaque
  unfolding _∙_ idS
  β-wt : ∀ {Δ}{Φ : Ctx Δ}{A′}(A : Tm ↑ Δ) → Φ ⊢↑ A ∶ A′ → WtSub (A ∙ idS) (A′ ∙ᶜ Φ) Φ
  β-wt A ⊢A (os q) = ⊢A
  β-wt A ⊢A (o' q) = ⊢var

-- SUBJECT REDUCTION
preserve : ∀ {Δ}{Φ : Ctx Δ}{B}{e e′ : Tm ↑ Δ} → Φ ⊢↑ e ∶ B → e ⟶ e′ → Φ ⊢↑ e′ ∶ B
preserve {Φ = Φ} ⊢e (β X A) with app↑-inv {Φ = Φ} (lam↑ X) A ⊢e
... | A′ , ⊢lamX , ⊢A with lam↑-inv {Φ = Φ} X ⊢lamX
...   | _ , _ , refl , ⊢X = sub-pres↑ {Φ = A′ ∙ᶜ Φ} {Ψ = Φ} X (A ∙ idS) ⊢X (β-wt A ⊢A)
preserve {Φ = Φ} ⊢e (ξ-app₁ {L = L}{L′ = L′}{R = R} L⟶) with app↑-inv {Φ = Φ} L R ⊢e
... | A′ , ⊢L , ⊢R = ⊢app↑ {Φ = Φ}{L = L′}{R = R} (preserve {Φ = Φ} ⊢L L⟶) ⊢R
preserve {Φ = Φ} ⊢e (ξ-app₂ {L = L}{R = R}{R′ = R′} R⟶) with app↑-inv {Φ = Φ} L R ⊢e
... | A′ , ⊢L , ⊢R = ⊢app↑ {Φ = Φ}{L = L}{R = R′} ⊢L (preserve {Φ = Φ} ⊢R R⟶)
preserve {Φ = Φ} ⊢e (ξ-lam {X = X}{X′ = X′} X⟶) with lam↑-inv {Φ = Φ} X ⊢e
... | A , _ , refl , ⊢X = ⊢lam↑ {Φ = Φ}{A = A}{X = X′} (preserve {Φ = A ∙ᶜ Φ} ⊢X X⟶)
