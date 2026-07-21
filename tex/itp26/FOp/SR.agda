{-# OPTIONS --rewriting --local-confluence-check #-}
-- SUBJECT REDUCTION for extrinsic System F: Γ ⊢ t ∶ A → t ⟶ t′ → Γ ⊢ t′ ∶ A.
-- Term substitution preserves typing (⊢-subTm), type substitution preserves typing
-- (⊢-subTy from FOp.Typing); β and type-β are handled by those two lemmas.
module FOp.SR where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; _,_; _×_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open import Agda.Builtin.Equality.Rewrite
open import FOp.ThinRw
open import FOp.Ty
open import FOp.Tm
open import FOp.Typing


-- ════ term renaming preserves typing ════
_⊨ᴿ_∶_ : Cx Θ → Ren → Cx Θ → Set
_⊨ᴿ_∶_ {Θ} Δ ρ Γ = ∀ {i}{A : Ty ↑ Θ} → Lookup Γ i A → Lookup Δ (ρ i) A
wk-Lookup : ∀ {Γ : Cx Θ}{i A} → Lookup Γ i A → Lookup (wkCx Γ) i (A ⟨ o' oi ⟩↑)
wk-Lookup here      = here
wk-Lookup (there l) = there (wk-Lookup l)
liftᴿ-⊨ : ∀ {Δ Γ : Cx Θ}{ρ A} → Δ ⊨ᴿ ρ ∶ Γ → (A ∷ Δ) ⊨ᴿ liftR ρ ∶ (A ∷ Γ)
liftᴿ-⊨ env here      = here
liftᴿ-⊨ env (there l) = there (env l)
wkᴿ-⊨ : ∀ {Δ Γ : Cx Θ}{ρ} → Δ ⊨ᴿ ρ ∶ Γ → wkCx Δ ⊨ᴿ ρ ∶ wkCx Γ
wkᴿ-⊨ {Γ = A ∷ Γ} env here      = wk-Lookup (env here)
wkᴿ-⊨ {Γ = A ∷ Γ} env (there l) = wkᴿ-⊨ (λ l₀ → env (there l₀)) l
⊢-ren : ∀ {Δ Γ : Cx Θ}{t A ρ} → Γ ⊢ t ∶ A → Δ ⊨ᴿ ρ ∶ Γ → Δ ⊢ renTm ρ t ∶ A
⊢-ren (⊢var l)   env = ⊢var (env l)
⊢-ren (⊢lam d)   env = ⊢lam (⊢-ren d (liftᴿ-⊨ env))
⊢-ren (⊢app f a) env = ⊢app (⊢-ren f env) (⊢-ren a env)
⊢-ren (⊢Lam {B = B} d) env = ⊢Lam {B = B} (⊢-ren d (wkᴿ-⊨ env))
⊢-ren (⊢App {B = B} A d) env = ⊢App {B = B} A (⊢-ren d env)
wkTm-⊢ : ∀ {Δ : Cx Θ}{t A B} → Δ ⊢ t ∶ A → (B ∷ Δ) ⊢ renTm suc t ∶ A
wkTm-⊢ d = ⊢-ren d there

-- ════ term substitution preserves typing ════
_⊨_∶_ : Cx Θ → (ℕ → Tm Θ) → Cx Θ → Set
_⊨_∶_ {Θ} Δ σ Γ = ∀ {i}{A : Ty ↑ Θ} → Lookup Γ i A → Δ ⊢ σ i ∶ A
⊢-wkTy : ∀ {Δ : Cx Θ}{t A} → Δ ⊢ t ∶ A → wkCx Δ ⊢ wkTyTm t ∶ (A ⟨ o' oi ⟩↑)
⊢-wkTy {Δ = Δ}{A = A} d =
  subst (λ Ψ → Ψ ⊢ _ ∶ (A ⟨ o' oi ⟩↑)) (subCx-wkids Δ)
    (subst (subCx Δ (wkSub ids) ⊢ _ ∶_) (wk-ty A) (⊢-subTy (wkSub ids) d))
  where subCx-wkids : ∀ {Θ}(Γ : Cx Θ) → subCx Γ (wkSub ids) ≡ wkCx Γ
        subCx-wkids []      = refl
        subCx-wkids (C ∷ Γ) rewrite wk-ty C | subCx-wkids Γ = refl
liftˢ-⊨ : ∀ {Δ Γ : Cx Θ}{σ A} → Δ ⊨ σ ∶ Γ → (A ∷ Δ) ⊨ liftS σ ∶ (A ∷ Γ)
liftˢ-⊨ env here      = ⊢var here
liftˢ-⊨ env (there l) = wkTm-⊢ (env l)
wkˢ-⊨ : ∀ {Δ Γ : Cx Θ}{σ} → Δ ⊨ σ ∶ Γ → wkCx Δ ⊨ (λ n → wkTyTm (σ n)) ∶ wkCx Γ
wkˢ-⊨ {Γ = A ∷ Γ} env here      = ⊢-wkTy (env here)
wkˢ-⊨ {Γ = A ∷ Γ} env (there l) = wkˢ-⊨ (λ l₀ → env (there l₀)) l
⊢-subTm : ∀ {Δ Γ : Cx Θ}{t A σ} → Γ ⊢ t ∶ A → Δ ⊨ σ ∶ Γ → Δ ⊢ subTm σ t ∶ A
⊢-subTm (⊢var l)   env = env l
⊢-subTm (⊢lam d)   env = ⊢lam (⊢-subTm d (liftˢ-⊨ env))
⊢-subTm (⊢app f a) env = ⊢app (⊢-subTm f env) (⊢-subTm a env)
⊢-subTm (⊢Lam {B = B} d) env = ⊢Lam {B = B} (⊢-subTm d (wkˢ-⊨ env))
⊢-subTm (⊢App {B = B} A d) env = ⊢App {B = B} A (⊢-subTm d env)
-- single substitution env (for β)
sub0-⊨ : ∀ {Γ : Cx Θ}{a A} → Γ ⊢ a ∶ A → Γ ⊨ (a ∷ˢ var) ∶ (A ∷ Γ)
sub0-⊨ ⊢a here      = ⊢a
sub0-⊨ ⊢a (there l) = ⊢var l

-- ════ reduction (raw terms) + SUBJECT REDUCTION ════
data _⟶_ {Θ} : Tm Θ → Tm Θ → Set where
  β    : ∀ {A b a}  → app (lam A b) a ⟶ sub0 a b
  βT   : ∀ {t}{A : Ty ↑ Θ} → App (Lam t) A ⟶ subTyTm t (A ∙ ids)
  ξ-f  : ∀ {f f′ a} → f ⟶ f′ → app f a ⟶ app f′ a
  ξ-a  : ∀ {f a a′} → a ⟶ a′ → app f a ⟶ app f a′
  ξ-l  : ∀ {A b b′}  → b ⟶ b′ → lam A b ⟶ lam A b′
  ξ-L  : ∀ {t t′}   → t ⟶ t′ → Lam t ⟶ Lam t′
  ξ-A  : ∀ {t t′ A} → t ⟶ t′ → App t A ⟶ App t′ A
infix 3 _⟶_

subCx-inst : ∀ {Θ}(Γ : Cx Θ)(A : Ty ↑ Θ) → subCx (wkCx Γ) (A ∙ ids) ≡ Γ
subCx-inst []      A = refl
subCx-inst (C ∷ Γ) A rewrite wk-cancel C A ids | ⟪⟫-id C | subCx-inst Γ A = refl

-- ════ injectivity of the type formers (peel via registered Fac / bindUp) ════
domOf codOf : ∀ {Δ} → Ty ↑ Δ → Ty ↑ Δ
domOf (tvar ⇑ θ)              = tvar ⇑ θ
domOf (_⇒_ (pair l r cv) ⇑ θ) = l ⇑ (thinL cv ⨾ θ)
domOf (∀' b ⇑ θ)              = ∀' b ⇑ θ
codOf (tvar ⇑ θ)              = tvar ⇑ θ
codOf (_⇒_ (pair l r cv) ⇑ θ) = r ⇑ (thinR cv ⨾ θ)
codOf (∀' b ⇑ θ)              = ∀' b ⇑ θ
domOf-⇒↑ : ∀ {Δ}(A B : Ty ↑ Δ) → domOf (A ⇒↑ B) ≡ A
domOf-⇒↑ A B = refl
codOf-⇒↑ : ∀ {Δ}(A B : Ty ↑ Δ) → codOf (A ⇒↑ B) ≡ B
codOf-⇒↑ A B = refl
⇒↑-injˡ : ∀ {Δ}{A B A′ B′ : Ty ↑ Δ} → (A ⇒↑ B) ≡ (A′ ⇒↑ B′) → A ≡ A′
⇒↑-injˡ {A = A}{B}{A′}{B′} e = trans (sym (domOf-⇒↑ A B)) (trans (cong domOf e) (domOf-⇒↑ A′ B′))
⇒↑-injʳ : ∀ {Δ}{A B A′ B′ : Ty ↑ Δ} → (A ⇒↑ B) ≡ (A′ ⇒↑ B′) → B ≡ B′
⇒↑-injʳ {A = A}{B}{A′}{B′} e = trans (sym (codOf-⇒↑ A B)) (trans (cong codOf e) (codOf-⇒↑ A′ B′))
bodyOf : ∀ {Δ} → Ty ↑ Δ → Ty ↑ (tt ∷ Δ)
bodyOf (tvar ⇑ θ)         = tvar ⇑ o' θ
bodyOf (_⇒_ x ⇑ θ)        = _⇒_ x ⇑ o' θ
bodyOf (∀' (use b) ⇑ θ)   = b ⇑ os θ
bodyOf (∀' (drop b) ⇑ θ)  = b ⇑ o' θ
bodyOf-∀↑ : ∀ {Δ}(B : Ty ↑ (tt ∷ Δ)) → bodyOf (∀↑ B) ≡ B
bodyOf-∀↑ (b ⇑ os φ) = refl
bodyOf-∀↑ (b ⇑ o' φ) = refl
∀↑-inj : ∀ {Δ}{B B′ : Ty ↑ (tt ∷ Δ)} → (∀↑ B) ≡ (∀↑ B′) → B ≡ B′
∀↑-inj {B = B}{B′} e = trans (sym (bodyOf-∀↑ B)) (trans (cong bodyOf e) (bodyOf-∀↑ B′))

-- ════ inversion of the inner binder (projection form: reduces via Fac / bindUp) ════
⊢lam-inv : ∀ {Γ : Cx Θ}{A t C} → Γ ⊢ lam A t ∶ C → (domOf C ∷ Γ) ⊢ t ∶ codOf C
⊢lam-inv (⊢lam d) = d
⊢Lam-inv : ∀ {Γ : Cx Θ}{t C} → Γ ⊢ Lam t ∶ C → wkCx Γ ⊢ t ∶ bodyOf C
⊢Lam-inv (⊢Lam {B = B} d) = subst (wkCx _ ⊢ _ ∶_) (sym (bodyOf-∀↑ B)) d

-- ★ SUBJECT REDUCTION — Γ ⊢ t ∶ A preserved under t ⟶ t′
preserve : ∀ {Γ : Cx Θ}{t t′ A} → Γ ⊢ t ∶ A → t ⟶ t′ → Γ ⊢ t′ ∶ A
preserve (⊢app {A = A′}{B = B} df da) β = ⊢-subTm (⊢lam-inv {C = A′ ⇒↑ B} df) (sub0-⊨ da)
-- casing B's thinning makes ∀↑ B reduce (⇒ bodyOf(∀↑ B)=B by refl); then only the
-- context coherence subCx-inst remains — no ∀-injectivity, no ∀↑-inj subst.
preserve {Γ = Γ} (⊢App {B = _ ⇑ os _} A df) (βT {t = t}) =
  subst (λ Ψ → Ψ ⊢ subTyTm t (A ∙ ids) ∶ _) (subCx-inst Γ A) (⊢-subTy (A ∙ ids) (⊢Lam-inv df))
preserve {Γ = Γ} (⊢App {B = _ ⇑ o' _} A df) (βT {t = t}) =
  subst (λ Ψ → Ψ ⊢ subTyTm t (A ∙ ids) ∶ _) (subCx-inst Γ A) (⊢-subTy (A ∙ ids) (⊢Lam-inv df))
preserve (⊢app f a) (ξ-f r) = ⊢app (preserve f r) a
preserve (⊢app f a) (ξ-a r) = ⊢app f (preserve a r)
preserve (⊢lam d)   (ξ-l r) = ⊢lam (preserve d r)
preserve (⊢Lam {B = B} d) (ξ-L r) = ⊢Lam {B = B} (preserve d r)
preserve (⊢App {B = B} A d) (ξ-A r) = ⊢App {B = B} A (preserve d r)
