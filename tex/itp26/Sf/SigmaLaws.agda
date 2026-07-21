{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.SigmaLaws — CONFIRMATION that the full σ_SP (Schäfer/Stark / autosubst) law
-- set holds for the STLC `sub`, each by literal `refl` in the σ_SP PRIMITIVES:
--     id · ↑ · _[_](=sub/⟪⟫) · _⨟_ · _∙_(opaque cons) · var₀.
-- `wkSub`/`lift` are NOT primitives — they are DERIVED (bottom of file:
-- wkSub σ ≡ σ ⨟ ↑,  lift σ ≡ var₀ ∙ (σ ⨟ ↑)).
--
-- All laws hold by `refl` because they are REGISTERED REWRITES (see Sf.STLC /
-- Sf.Sub / Sf.Thin).  The de-Bruijn VARIABLE seam is gone: VarCons is refl, with
-- no `ren-var` side condition.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.SigmaLaws where
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sf.STLC
open import Sf.STLCInst  -- activates the Inst-· / Inst-ƛ rewrites

-- 1. Inst-· :  (l · r)[σ]  =  l[σ] · r[σ]
law-Inst-· : ∀ {sₗ sᵣ Γ Δ}(l : Tm sₗ)(r : Tm sᵣ)(cv : Cover sₗ sᵣ Γ)(σ : Sub Δ Γ)
           → sub (app (pair l r cv)) σ ≡ app↑ (sub l (selL cv σ)) (sub r (selR cv σ))
law-Inst-· l r cv σ = refl

-- 2. Inst-ƛ :  (ƛ t)[σ]  =  ƛ (t[⇑σ])     with the up-arrow ⇑σ = lift σ
law-Inst-ƛ : ∀ {Γ Δ}(t : Tm (tt ∷ Γ))(σ : Sub Δ Γ) → sub (lam (use t)) σ ≡ lam↑ (sub t (lift σ))
law-Inst-ƛ t σ = refl

-- 3. VarCons :  var₀[u ∙ σ]  =  u            (opaque-∙ form, registered rewrite)
law-VarCons : ∀ {Γ Δ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → var₀ ⟪ u ∙ σ ⟫ ≡ u
law-VarCons u σ = refl

-- 4. Map :  (u ∙ σ) ⨟ τ  =  u[τ] ∙ (σ ⨟ τ)  (opaque-∙ form, registered rewrite)
law-Map : ∀ {Γ Δ Θ}(u : Tm ↑ Δ)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → (u ∙ σ) ⨟ τ ≡ (u ⟪ τ ⟫) ∙ (σ ⨟ τ)
law-Map u σ τ = refl

-- 5. EmptyComp :  [] ⨟ τ  =  []
law-Empty : ∀ {Δ Θ}(τ : Sub Θ Δ) → ([] {Δ}) ⨟ τ ≡ []
law-Empty τ = refl

-- 6. Clos :  (u⟪τ⟫)⟪υ⟫  =  u⟪τ ⨟ υ⟫         (registered rewrite)
law-Clos : ∀ {Δ Δ′ Θ}(u : Tm ↑ Δ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (u ⟪ τ ⟫) ⟪ υ ⟫ ≡ u ⟪ τ ⨟ υ ⟫
law-Clos u τ υ = refl

-- 7. Ass :  (σ ⨟ τ) ⨟ υ  =  σ ⨟ (τ ⨟ υ)     (registered rewrite)
law-Ass : ∀ {Γ Δ Δ′ Θ}(σ : Sub Δ Γ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
law-Ass σ τ υ = refl

-- 8. IdL :  idS ⨟ σ  =  σ                    (registered rewrite)
law-IdL : ∀ {Γ Δ}(σ : Sub Δ Γ) → idS ⨟ σ ≡ σ
law-IdL σ = refl

-- 9. IdR :  σ ⨟ idS  =  σ                     (registered rewrite)
law-IdR : ∀ {Γ Δ}(σ : Sub Δ Γ) → σ ⨟ idS ≡ σ
law-IdR σ = refl

-- 10. IdCons :  var₀ ∙ ↑  =  idS              (opaque-∙ form, registered rewrite)
law-IdCons : ∀ {Γ} → var₀ ∙ (↑ₛ {Γ = Γ}) ≡ idS {tt ∷ Γ}
law-IdCons = refl

-- 11. SCons / η :  (var₀[σ]) ∙ (↑ ⨟ σ)  =  σ  (registered rewrite; abstract σ, no split!)
law-SCons : ∀ {Γ Δ}(σ : Sub Δ (tt ∷ Γ)) → (var₀ ⟪ σ ⟫) ∙ (↑ₛ ⨟ σ) ≡ σ
law-SCons σ = refl

-- 12. IdSubst :  t[idS]  =  t⇑oi              (registered rewrite)
law-IdSubst : ∀ {sup}(t : Tm sup) → sub t idS ≡ (t ⇑ oi)
law-IdSubst t = refl

-- 13. ShiftCons :  ↑ ⨟ (u ∙ σ)  =  σ          (opaque-∙ form, registered rewrite)
law-ShiftCons : ∀ {Γ Δ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → ↑ₛ ⨟ (u ∙ σ) ≡ σ
law-ShiftCons u σ = refl

-- ── faithfulness: wkSub and lift are DERIVED from the primitive ↑ (= ↑ₛ) ──
derived-wkSub : ∀ {s Γ Δ}(σ : Sub Δ Γ) → wkSub {s} σ ≡ σ ⨟ ↑ₛ
derived-wkSub = wkSub≡⨟↑
derived-lift  : ∀ {s Γ Δ}(σ : Sub Δ Γ) → lift {s} σ ≡ var₀ ∙ (σ ⨟ ↑ₛ)
derived-lift  = lift≡⇑
