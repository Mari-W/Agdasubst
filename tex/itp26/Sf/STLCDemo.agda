{-# OPTIONS --rewriting #-}
module STLCDemo where
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import STLC

-- (1) the σ-laws + renaming traversal compute as rewrites (all hold by refl):
_ : (e [ σ ]) [ τ ] ≡ e [ σ ⨟ τ ]                 ; _ = refl   -- Clos
_ : e [ id ] ≡ e                                   ; _ = refl   -- identity
_ : (` zero) [ e ∙ σ ] ≡ e                         ; _ = refl   -- variable lookup
_ : (ƛ e) [ σ ] ≡ ƛ (e [ (` zero) ∙ (σ ⨟ wk) ])    ; _ = refl   -- Inst-ƛ (lift)
_ : (e₁ · e₂) ⟨ ρ ⟩ ≡ (e₁ ⟨ ρ ⟩) · (e₂ ⟨ ρ ⟩)     ; _ = refl   -- renaming traversal (definitional!)
_ : (ƛ e) ⟨ ρ ⟩ ≡ ƛ (e ⟨ ρ ↑ᴿ ⟩)                  ; _ = refl   -- renaming-under-binder (definitional, via embed-↑)
_ : ((` zero {n}) ∙ wk) ⨟ σ ≡ σ                    ; _ = refl   -- η/surjective-pairing critical pair joins

-- (2) the preservation theorems are total (no holes/postulates beyond funext):
ren-preserves : ∀ {m n}{Γ : Ctx m}{Δ : Ctx n}{ρ}{e}{A}
              → ρ ∶ Γ ⇒ᴿ Δ → Γ ⊢ e ∶ A → Δ ⊢ (e ⟨ ρ ⟩) ∶ A
ren-preserves = ren-pres
sub-preserves : ∀ {m n}{Γ : Ctx m}{Δ : Ctx n}{σ}{e}{A}
              → σ ∶ Γ ⇒ˢ Δ → Γ ⊢ e ∶ A → Δ ⊢ (e [ σ ]) ∶ A
sub-preserves = sub-pres

-- (3) identity substitution preserves typing:
id-sub-pres : ∀ {n}{Γ : Ctx n}{e}{A} → Γ ⊢ e ∶ A → Γ ⊢ (e [ id ]) ∶ A
id-sub-pres ⊢e = sub-pres {σ = id} (λ x → ⊢`) ⊢e
