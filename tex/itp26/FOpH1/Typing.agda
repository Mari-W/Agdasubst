{-# OPTIONS --rewriting --local-confluence-check #-}
-- EXTRINSIC typing for the raw System F terms, and TYPE-substitution preserves typing.
-- Terms stay raw; typing is a relation ⇒ the substitution *lemma* is on derivations,
-- and the only equational glue is at the TYPE-classifier level (the non-refl σ-laws),
-- never a transport of terms.
module FOpH1.Typing where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import Agda.Builtin.Equality.Rewrite
open import FOpH1.ThinRw
open import FOpH1.Ty
open import FOpH1.Tm

Cx : Scope → Set
Cx Θ = List (Ty ↑ Θ)
wkCx : Cx Θ → Cx (tt ∷ Θ)
wkCx = map (_⟨ o' oi ⟩↑)
subCx : Cx Θ → Sub Δ Θ → Cx Δ
subCx Γ σ = map (_⟪ σ ⟫) Γ

data Lookup {Θ} : Cx Θ → ℕ → Ty ↑ Θ → Set where
  here  : ∀ {A Γ}     → Lookup (A ∷ Γ) zero A
  there : ∀ {A B Γ i} → Lookup Γ i A → Lookup (B ∷ Γ) (suc i) A

data _⊢_∶_ {Θ} (Γ : Cx Θ) : Tm Θ → Ty ↑ Θ → Set where
  ⊢var : ∀ {i A}     → Lookup Γ i A                          → Γ ⊢ var i ∶ A
  ⊢lam : ∀ {A t B}   → (A ∷ Γ) ⊢ t ∶ B                       → Γ ⊢ lam A t ∶ (A ⇒↑ B)
  ⊢app : ∀ {t u A B} → Γ ⊢ t ∶ (A ⇒↑ B) → Γ ⊢ u ∶ A         → Γ ⊢ app t u ∶ B
  ⊢Lam : ∀ {t B}     → wkCx Γ ⊢ t ∶ B                        → Γ ⊢ Lam t ∶ (∀↑ B)
  ⊢App : ∀ {t B}(A : Ty ↑ Θ) → Γ ⊢ t ∶ (∀↑ B)               → Γ ⊢ App t A ∶ (B ⟪ A ∙ ids ⟫)
infix 4 _⊢_∶_

-- context coherences (list-lifted pure FOpH1.Ty lemmas)
subCx-wk : ∀ {Θ Δ}(Γ : Cx Θ)(σ : Sub Δ Θ) → subCx (wkCx Γ) (lift σ) ≡ wkCx (subCx Γ σ)
subCx-wk []      σ = refl
subCx-wk (C ∷ Γ) σ rewrite wk-⟪⟫ C σ | subCx-wk Γ σ = refl
App-comm : ∀ {Θ Δ}(B : Ty ↑ (tt ∷ Θ))(A : Ty ↑ Θ)(σ : Sub Δ Θ)
         → (B ⟪ A ∙ ids ⟫) ⟪ σ ⟫ ≡ (B ⟪ lift σ ⟫) ⟪ (A ⟪ σ ⟫) ∙ ids ⟫
App-comm B A σ rewrite Clos B (A ∙ ids) σ | ⨟-idₗ σ | sym (inst-lift σ (A ⟪ σ ⟫)) | sym (Clos B (lift σ) ((A ⟪ σ ⟫) ∙ ids)) = refl

subLookup : ∀ {Θ Δ}{Γ : Cx Θ}{i A}(σ : Sub Δ Θ) → Lookup Γ i A → Lookup (subCx Γ σ) i (A ⟪ σ ⟫)
subLookup σ here      = here
subLookup σ (there l) = there (subLookup σ l)

-- ★ TYPE-substitution preserves typing.  Substs appear ONLY at the type classifier
-- (the non-refl σ-laws ⟪⟫-⇒↑ / ⟪⟫-∀↑ / App-comm) — never on a term.
⊢-subTy : ∀ {Θ Δ}{Γ : Cx Θ}{t A}(σ : Sub Δ Θ) → Γ ⊢ t ∶ A → subCx Γ σ ⊢ subTyTm t σ ∶ (A ⟪ σ ⟫)
⊢-subTy σ (⊢var l)            = ⊢var (subLookup σ l)
-- ⟪⟫-⇒↑ is now REFL ⇒ NO subst needed (the arrow classifier reduces definitionally)
⊢-subTy {Γ = Γ} σ (⊢lam {A}{t}{B} d)  = ⊢lam (⊢-subTy σ d)
⊢-subTy {Γ = Γ} σ (⊢app {t}{u}{A}{B} df da) = ⊢app (⊢-subTy σ df) (⊢-subTy σ da)
⊢-subTy {Γ = Γ} σ (⊢Lam {t}{B} d)     =
  subst (subCx Γ σ ⊢ Lam (subTyTm t (lift σ)) ∶_) (sym (⟪⟫-∀↑ B σ))
    (⊢Lam (subst (λ Ψ → Ψ ⊢ subTyTm t (lift σ) ∶ (B ⟪ lift σ ⟫)) (subCx-wk Γ σ) (⊢-subTy (lift σ) d)))
⊢-subTy {Γ = Γ} σ (⊢App {t}{B} A d)  =
  subst (subCx Γ σ ⊢ App (subTyTm t σ) (A ⟪ σ ⟫) ∶_) (sym (App-comm B A σ))
    (⊢App {B = B ⟪ lift σ ⟫} (A ⟪ σ ⟫)
      (subst (subCx Γ σ ⊢ subTyTm t σ ∶_) (⟪⟫-∀↑ B σ) (⊢-subTy σ d)))
