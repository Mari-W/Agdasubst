{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- SUBJECT-REDUCTION for the MULTI-SORTED co-de-Bruijn System F.  β (expr
-- substitution) and type-β (type substitution) are the TWO instances of the ONE
-- unified `Sub` / `sub-pres` (FOpMS.Typing): β substitutes `arg ∙ ids`, type-β
-- substitutes `A ∙ ids`, both a single-entry-then-`ids` vector.  We give the
-- reduction relation `_⟶_` and the proven reduct-typing CONTENT (`⊢-inst` /
-- `⊢-instTy`) of the β / type-β contractions, all via `sub-pres` + `id-pres`.
-- ════════════════════════════════════════════════════════════════════════════
module FOpMS.SR where
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Agda.Builtin.Equality.Rewrite
open import FOpMS.ThinRw
open import FOpMS.Tm
open import FOpMS.Typing

private variable
  s s′ : Sort
  Δ Θ sup : Scope

-- ════ the IDENTITY well-typed substitution ════
⊢fresh-ids : ∀ {Δ}{Ψ : Cx Δ}{A : Tm type ↑ Δ} → (Ψ ,- A) ⊢↑ var↑ ∶ (A ⟪ wkSub ids ⟫)
⊢fresh-ids {Ψ = Ψ}{A = A} =
  subst (λ T → (Ψ ,- A) ⊢↑ var↑ ∶ T)
        (sym (trans (wkSub-⟪⟫ {s = expr} A ids) (cong (wk↑ expr) (⟪⟫-id A)))) ⊢fresh
id-pres : ∀ {Δ}(Ψ : Cx Δ) → WtSub Ψ ids Ψ
id-pres ε        = ε
id-pres (Ψ ,*)   = var↑ ∙* wkSub-pres-ty (id-pres Ψ)
id-pres (Ψ ,- A) = ⊢fresh-ids ∙- wkSub-pres-tm A (id-pres Ψ)

-- ════ reduction relation (⇑-carrier level, cased binders so ⊢lamᵘ/⊢Lamᵘ INVERT) ════
data _⟶_ : ∀ {Δ} → Tm expr ↑ Δ → Tm expr ↑ Δ → Set where
  βᵘ  : ∀ {Δ sup}{A : Tm type ↑ Δ}{x : Tm expr (expr ∷ sup)}{ξ : sup ⊑ Δ}{arg : Tm expr ↑ Δ}
      → app↑ (lam↑ A (x ⇑ os ξ)) arg ⟶ ((x ⇑ os ξ) ⟪ arg ∙ ids ⟫)
  βᵈ  : ∀ {Δ sup}{A : Tm type ↑ Δ}{x : Tm expr sup}{ξ : sup ⊑ Δ}{arg : Tm expr ↑ Δ}
      → app↑ (lam↑ A (x ⇑ o' ξ)) arg ⟶ ((x ⇑ o' ξ) ⟪ arg ∙ ids ⟫)
  ξ-fun : ∀ {Δ}{f f′ arg : Tm expr ↑ Δ} → f ⟶ f′ → app↑ f arg ⟶ app↑ f′ arg
  ξ-arg : ∀ {Δ}{f arg arg′ : Tm expr ↑ Δ} → arg ⟶ arg′ → app↑ f arg ⟶ app↑ f arg′
  ξ-App : ∀ {Δ}{e e′ : Tm expr ↑ Δ}{A : Tm type ↑ Δ} → e ⟶ e′ → App↑ e A ⟶ App↑ e′ A
infix 3 _⟶_

-- ════════════════════════════════════════════════════════════════════════════
-- SUBJECT-REDUCTION CONTENT: β and type-β are the TWO instances of the ONE
-- unified `sub-pres`.  Each contracts a redex by substituting a SINGLE entry then
-- identity — `arg ∙ ids` (expr-β) / `A ∙ ids` (type-β) — the multi-sorted `Sub`.
--
-- These are the reduct-typing obligations of  `app↑ (lam↑ D e) v ⟶ e ⟪ v ∙ ids ⟫`
-- and  `App↑ (Lam↑ e) A ⟶ e ⟪ A ∙ ids ⟫`.  The `_⟶_`-DISPATCHING `preserve` needs
-- the raw support-level reduction (Sf-style, with a re-embed lemma): at the
-- ⇑-carrier level the smart constructors `app↑`/`App↑` are not unification-
-- invertible (the arrow domain / cover thinnings sit under `cop`), so `preserve`
-- cannot solve them — the substitution CONTENT below is what SR actually uses,
-- and it is fully proven with no postulates.
-- ════════════════════════════════════════════════════════════════════════════

-- expr-β: replace the bound EXPR-var by a term `v` typed at its classifier `Dom`.
⊢-inst : ∀ {Δ}{Φ : Cx Δ}{e : Tm expr ↑ (expr ∷ Δ)}{B : Tm type ↑ (expr ∷ Δ)}
           {Dom : Tm type ↑ Δ}{v : Tm expr ↑ Δ}
       → (Φ ,- Dom) ⊢↑ e ∶ B → Φ ⊢↑ v ∶ Dom → Φ ⊢↑ (e ⟪ v ∙ ids ⟫) ∶ (B ⟪ v ∙ ids ⟫)
⊢-inst {Φ = Φ}{Dom = Dom} ⊢e ⊢v =
  sub-pres (subst (λ D → Φ ⊢↑ _ ∶ D) (sym (⟪⟫-id Dom)) ⊢v ∙- id-pres Φ) ⊢e

-- type-β: replace the bound TYPE-var by a type `A` (ty-vars carry no typing).
⊢-instTy : ∀ {Δ}{Φ : Cx Δ}{e : Tm expr ↑ (type ∷ Δ)}{B : Tm type ↑ (type ∷ Δ)}(A : Tm type ↑ Δ)
         → (Φ ,*) ⊢↑ e ∶ B → Φ ⊢↑ (e ⟪ A ∙ ids ⟫) ∶ (B ⟪ A ∙ ids ⟫)
⊢-instTy {Φ = Φ} A ⊢e = sub-pres (A ∙* id-pres Φ) ⊢e
