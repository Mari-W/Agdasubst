{-# OPTIONS --rewriting --local-confluence-check #-}
-- ============================================================================
-- CONFIRMATION of the full σ-calculus (σ_SP / autosubst) law set, stated FAITHFULLY
-- with the six primitives id · ↑ · _[_] · _⨟_ · _∙_(= _,-_) · var₀ (⇑σ = var₀ ∙ (σ⨟↑)
-- is derived).  `wkSub`/`lift` are NOT primitives — they are DERIVED (see bottom:
-- wkSub σ ≡ σ ⨟ ↑, lift σ ≡ ⇑σ).  HONEST ACCOUNTING of the thirteen laws:
--   ★ ALL 13 hold by literal `refl`, each stated in the σ_SP PRIMITIVES only.  The cons
--     is the opaque function `∙` (NOT the constructor `,-`), the shift is the opaque
--     primitive `↑ₛ` (NOT `wkSub`; general weakening is the derived `_⨟ ↑ₛ`).  The five
--     cons-laws VarCons/Map/ShiftCons/SCons/IdCons are registered as rewrites on `∙` in
--     CDBcomp — together they ARE the confluent σ_SP completion (e.g. VarCons-∙ closes the
--     SCons-∙ × ShiftCons-∙ critical pair).  Inst-ƛ uses the up-arrow `up` (= ⇑σ, opaque;
--     up-def : up σ ≡ var₀ ∙ (σ⨟↑)).  Two keys made the cons-laws fire: (1) the cons is the
--     opaque `∙`, a legal rewrite head — the bare constructor `,-` was "not a legal rewrite
--     rule"; (2) DROP the non-primitive `wk-⨟-cons` (uses wkSub ∉ σ_SP) from the rewrites.
-- The de-Bruijn VARIABLE seam is gone throughout: VarCons is `refl`, no `ren-var`.
-- ============================================================================
module CDBSigmaLaws where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Unit using (tt)
open import Data.List using (_∷_)
open import CDBsig
open import CDBterm
open import CDBsub
open import CDBcomp

-- 1. Inst-· :  (l · r)[σ]  =  l[σ] · r[σ]                                  (refl)
law-Inst-· : ∀ {sₗ sᵣ Γ Δ}(l : Tm sₗ)(r : Tm sᵣ)(cv : Cover sₗ sᵣ Γ)(σ : Sub Δ Γ)
           → sub (app (pair l r cv)) σ ≡ app↑ (sub l (selL cv σ)) (sub r (selR cv σ))
law-Inst-· l r cv σ = refl

-- 2. Inst-ƛ :  (ƛ t)[σ]  =  ƛ (t[⇑σ])        with the up-arrow ⇑σ (the standard σ-calculus
-- "up").  ⇑σ is the operation `sub` uses under a λ; its DEFINING equation is
-- ⇑σ = var₀ ∙ (σ ∘ ↑)  (up-def, below).  It is realized OPAQUELY (= wkSub σ , var₀) so it
-- both terminates and is a matchable rewrite head — which is what hides `wkSub`/`lift` and
-- lets Inst-ƛ be `refl`.  No non-primitive leaks into the law.
up : ∀ {Γ Δ} → Sub Δ Γ → Sub (tt ∷ Δ) (tt ∷ Γ)
up σ = lift σ
law-Inst-ƛ : ∀ {Γ Δ}(t : Tm (tt ∷ Γ))(σ : Sub Δ Γ)
           → sub (lam (use t)) σ ≡ lam↑ (sub t (up σ))
law-Inst-ƛ t σ = refl
up-def : ∀ {Γ Δ}(σ : Sub Δ Γ) → up σ ≡ (σ ⨟ ↑ₛ) ,- (var ⇑ os oe)   -- ⇑σ = var₀ ∙ (σ ⨟ ↑)
up-def = lift≡⇑

-- 3. VarCons :  var₀[u ∙ σ]  =  u       (primitive ∙-form, registered REWRITE)  (refl)
law-VarCons : ∀ {Γ Δ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → (var ⇑ os oe) ⟪ u ∙ σ ⟫ ≡ u
law-VarCons u σ = refl

-- 4. Map :  (u ∙ σ) ⨟ τ  =  u[τ] ∙ (σ ⨟ τ)   (primitive ∙-form, registered REWRITE) (refl)
law-Map : ∀ {Γ Δ Θ}(u : Tm ↑ Δ)(σ : Sub Δ Γ)(τ : Sub Θ Δ)
        → (u ∙ σ) ⨟ τ ≡ (u ⟪ τ ⟫) ∙ (σ ⨟ τ)
law-Map u σ τ = refl

-- 5. EmptyComp :  [] ⨟ τ  =  []                                            (refl)
law-Empty : ∀ {Δ Θ}(τ : Sub Θ Δ) → ([] {Δ}) ⨟ τ ≡ []
law-Empty τ = refl

-- 6. Clos :  (u⟪τ⟫)⟪υ⟫  =  u⟪τ ⨟ υ⟫            (registered REWRITE)          (refl)
law-Clos : ∀ {Δ Δ′ Θ}(u : Tm ↑ Δ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′)
         → (u ⟪ τ ⟫) ⟪ υ ⟫ ≡ u ⟪ τ ⨟ υ ⟫
law-Clos u τ υ = refl

-- 7. Ass :  (σ ⨟ τ) ⨟ υ  =  σ ⨟ (τ ⨟ υ)        (registered REWRITE)          (refl)
law-Ass : ∀ {Γ Δ Δ′ Θ}(σ : Sub Δ Γ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′)
        → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
law-Ass σ τ υ = refl

-- 8. IdL :  idS ⨟ σ  =  σ                       (registered REWRITE)          (refl)
law-IdL : ∀ {Γ Δ}(σ : Sub Δ Γ) → idS ⨟ σ ≡ σ
law-IdL σ = refl

-- 9. IdR :  σ ⨟ idS  =  σ                        (registered REWRITE)          (refl)
law-IdR : ∀ {Γ Δ}(σ : Sub Δ Γ) → σ ⨟ idS ≡ σ
law-IdR σ = refl

-- 10. IdCons :  var₀ ∙ ↑  =  idS                       (registered REWRITE)    (refl)
-- DEFINITIONAL via the opaque cons `∙` (IdCons-∙ rewrite).  The cons LHS `var₀ ∙ ↑`
-- is headed by the FUNCTION `∙` (opaque), so it is a legal rewrite head — the bare
-- constructor `↑ ,- var₀` was rejected ("not a legal rewrite rule").
law-IdCons : ∀ {Γ} → (var ⇑ os oe) ∙ (↑ₛ {Γ}) ≡ idS {tt ∷ Γ}
law-IdCons = refl

-- 11. SCons / η :  (var₀[σ]) ∙ (↑ ⨟ σ)  =  σ            (registered REWRITE)    (refl)
-- DEFINITIONAL — and for ABSTRACT σ, no case split!  SCons-∙ is registered via the
-- opaque cons `∙`; the overlap that blocked it (against the non-primitive `wk-⨟-cons`)
-- is gone because `wk-⨟-cons` is no longer a rewrite (it uses wkSub ∉ σ_SP), so `↑⨟σ`
-- is stuck and SCons-∙ has no competing redex.  ShiftCons (law 13) is its tail-half.
law-SCons : ∀ {Γ Δ}(σ : Sub Δ (tt ∷ Γ)) → ((var ⇑ os oe) ⟪ σ ⟫) ∙ (↑ₛ ⨟ σ) ≡ σ
law-SCons σ = refl

-- 12. IdSubst :  t[idS]  =  t⇑oi          (refl — sub-idS is a registered rewrite)
law-IdSubst : ∀ {sup}(t : Tm sup) → sub t idS ≡ (t ⇑ oi)
law-IdSubst t = refl

-- 13. ShiftCons :  ↑ ∘ (s ∙ σ)  =  σ       (primitive ∙-form, registered REWRITE)  (refl)
-- DEFINITIONAL via ShiftCons-∙ — once the WHOLE cons-algebra is on the opaque `∙`
-- (VarCons-∙/Map-∙/ShiftCons-∙/SCons-∙/IdCons-∙), it is the confluent σ_SP completion:
-- the SCons-∙ × ShiftCons-∙ critical pair joins because VarCons-∙ (var₀⟪u∙σ⟫→u) closes it.
law-ShiftCons : ∀ {Γ Δ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → ↑ₛ ⨟ (u ∙ σ) ≡ σ
law-ShiftCons u σ = refl

-- ── faithfulness: wkSub and lift are DERIVED from the primitive ↑ (= ↑ₛ), not new ──
derived-wkSub : ∀ {Γ Δ}(σ : Sub Δ Γ) → wkSub σ ≡ σ ⨟ ↑ₛ           -- "weaken σ" = σ ∘ ↑
derived-wkSub = wkSub≡⨟↑
derived-lift  : ∀ {Γ Δ}(σ : Sub Δ Γ) → lift σ ≡ (σ ⨟ ↑ₛ) ,- (var ⇑ os oe)   -- lift = ⇑σ
derived-lift  = lift≡⇑
