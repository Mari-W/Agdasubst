{-# OPTIONS --rewriting #-}
module STLConeDemo where
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import STLCone
-- σ-laws compute as rewrites (definitional, outside the block):
_ : ∀ {m n k}{e : Tm m}{σ : Sub m n}{τ : Sub n k} → (e [ σ ]) [ τ ] ≡ e [ σ ⨟ τ ] ; _ = refl
_ : ∀ {n}{e : Tm n} → e [ id ] ≡ e                                                ; _ = refl
-- preservation theorems are usable:
sub-preserves : ∀ {m n}{Γ : Ctx m}{Δ : Ctx n}{σ}{e}{A} → σ ∶ Γ ⇒ˢ Δ → Γ ⊢ e ∶ A → Δ ⊢ (e [ σ ]) ∶ A
sub-preserves = sub-pres
