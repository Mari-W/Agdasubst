{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- PROBE 6 (step b): TYPE-SUBSTITUTION PRESERVES TYPING, over the vector calculus,
-- with INTRINSIC typing.  Then `subTyTm` IS `subTyTm-pres` (a typed term maps to a
-- typed term).  Measure: which σ-steps survive?  Prediction from the probes —
-- ONLY the former-distribution transport; no atom-bridge, no context-coherence,
-- no funext, no opacity.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.VecTyped where
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Clean.F.VecCover   -- Scope, Ty, _↑_, _⇒↑_, sub, _⟪_⟫, Sub, ⟪⟫-⇒↑

-- term context = a list of types over the type-scope Θ; type-sub maps it pointwise
Cx : Scope → Set
Cx Θ = List (Ty ↑ Θ)
subCx : ∀ {Θ Δ} → Cx Θ → Sub Δ Θ → Cx Δ
subCx Γ στ = map (_⟪ στ ⟫) Γ

data _∋_ {Θ} : Cx Θ → Ty ↑ Θ → Set where
  here  : ∀ {Γ A}   → (A ∷ Γ) ∋ A
  there : ∀ {Γ A B} → Γ ∋ A → (B ∷ Γ) ∋ A

-- intrinsically-typed System-F-arrow terms (term-scope = the context Γ, de Bruijn)
data Tm (Θ : Scope) : Cx Θ → Ty ↑ Θ → Set where
  var : ∀ {Γ A}   → Γ ∋ A                       → Tm Θ Γ A
  app : ∀ {Γ A B} → Tm Θ Γ (A ⇒↑ B) → Tm Θ Γ A  → Tm Θ Γ B
  lam : ∀ {Γ A B} → Tm Θ (A ∷ Γ) B              → Tm Θ Γ (A ⇒↑ B)

-- a term-var substitutes to a term-var — STRUCTURAL, no σ-step (subCx is just map)
subVar : ∀ {Θ Δ Γ A}(x : Γ ∋ A)(στ : Sub Δ Θ) → subCx Γ στ ∋ (A ⟪ στ ⟫)
subVar here      στ = here
subVar (there x) στ = there (subVar x στ)

-- ════ TYPE-SUBSTITUTION PRESERVES TYPING — = the substitution action itself ════
-- var: structural.  app/lam: the SOLE σ-step is the arrow-distribution transport
-- ⟪⟫-⇒↑ (a clean structural lemma — no opacity, no funext).  NO atom-bridge (⟪⟫ is
-- transparent ⇒ it's the definition).  NO context coherence (typing is intrinsic).
subTyTm : ∀ {Θ Δ Γ A} → Tm Θ Γ A → (στ : Sub Δ Θ) → Tm Δ (subCx Γ στ) (A ⟪ στ ⟫)
subTyTm (var x)               στ = var (subVar x στ)
subTyTm (app {A = A}{B = B} f a) στ =
  app (subst (Tm _ _) (⟪⟫-⇒↑ A B στ) (subTyTm f στ)) (subTyTm a στ)
subTyTm (lam {A = A}{B = B} b)   στ =
  subst (Tm _ _) (sym (⟪⟫-⇒↑ A B στ)) (lam (subTyTm b στ))
