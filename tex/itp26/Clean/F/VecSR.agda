{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- PROBE 7 — SUBJECT REDUCTION over the vector calculus, INTRINSICALLY.  With
-- type-indexed terms, `_⟶_ : Tm Θ Γ A → Tm Θ Γ A → Set` is type-preserving BY
-- CONSTRUCTION: the ONLY content is that β's contractum type-checks, which is
-- exactly `subTm` (term-substitution preserves typing).  No inversions, no
-- injectivity, no σ-substs, no preserve-proof — SR is definitional.
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.VecSR where
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Clean.F.VecCover using (Scope; Ty; _↑_; _⇒↑_)
open import Clean.F.VecTyped using (Cx; _∋_; here; there; Tm; var; app; lam)

-- ════ context inclusion + renaming (for lifting the substitution under λ) ════
data _⊆_ {Θ} : Cx Θ → Cx Θ → Set where
  done : [] ⊆ []
  keep : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → (A ∷ Γ) ⊆ (A ∷ Γ′)
  skip : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊆ (A ∷ Γ′)
⊆-refl : ∀ {Θ}{Γ : Cx Θ} → Γ ⊆ Γ
⊆-refl {Γ = []}    = done
⊆-refl {Γ = _ ∷ _} = keep ⊆-refl

renVar : ∀ {Θ}{Γ Γ′ : Cx Θ}{A} → Γ ∋ A → Γ ⊆ Γ′ → Γ′ ∋ A
renVar here      (keep i) = here
renVar (there x) (keep i) = there (renVar x i)
renVar x         (skip i) = there (renVar x i)
renTm : ∀ {Θ}{Γ Γ′ : Cx Θ}{A} → Tm Θ Γ A → Γ ⊆ Γ′ → Tm Θ Γ′ A
renTm (var x)   i = var (renVar x i)
renTm (app f a) i = app (renTm f i) (renTm a i)
renTm (lam b)   i = lam (renTm b (keep i))
wkTm : ∀ {Θ}{Γ : Cx Θ}{A B} → Tm Θ Γ A → Tm Θ (B ∷ Γ) A
wkTm t = renTm t (skip ⊆-refl)

-- ════ term-substitution environment + the ACTION (= preservation, intrinsic) ════
data Env (Θ : Scope) (Δ : Cx Θ) : Cx Θ → Set where
  ε   : Env Θ Δ []
  _∙_ : ∀ {Γ A} → Tm Θ Δ A → Env Θ Δ Γ → Env Θ Δ (A ∷ Γ)
infixr 5 _∙_
lookupE : ∀ {Θ}{Δ Γ : Cx Θ}{A} → Γ ∋ A → Env Θ Δ Γ → Tm Θ Δ A
lookupE here      (t ∙ ρ) = t
lookupE (there x) (t ∙ ρ) = lookupE x ρ
wkEnv : ∀ {Θ}{Δ Γ : Cx Θ}{B} → Env Θ Δ Γ → Env Θ (B ∷ Δ) Γ
wkEnv ε       = ε
wkEnv (t ∙ ρ) = wkTm t ∙ wkEnv ρ
liftEnv : ∀ {Θ}{Δ Γ : Cx Θ}{A} → Env Θ Δ Γ → Env Θ (A ∷ Δ) (A ∷ Γ)
liftEnv ρ = var here ∙ wkEnv ρ

-- term-substitution = subject-reduction's β-step, and it IS the preservation:
-- a typed term maps to a typed term, with NO σ-step (Env is data, types align).
subTm : ∀ {Θ}{Δ Γ : Cx Θ}{A} → Tm Θ Γ A → Env Θ Δ Γ → Tm Θ Δ A
subTm (var x)   ρ = lookupE x ρ
subTm (app f a) ρ = app (subTm f ρ) (subTm a ρ)
subTm (lam b)   ρ = lam (subTm b (liftEnv ρ))

idEnv : ∀ {Θ}{Γ : Cx Θ} → Env Θ Γ Γ
idEnv {Γ = []}    = ε
idEnv {Γ = _ ∷ _} = var here ∙ wkEnv idEnv
β-env : ∀ {Θ}{Γ : Cx Θ}{A} → Tm Θ Γ A → Env Θ Γ (A ∷ Γ)
β-env arg = arg ∙ idEnv

-- ════ REDUCTION — type-indexed ⇒ SUBJECT REDUCTION BY CONSTRUCTION ════
-- the β constructor TYPE-CHECKING is exactly subject reduction for β: its contractum
-- `subTm b (β-env arg)` is forced to have type `Tm Θ Γ B`, which it does.
data _⟶_ {Θ}{Γ : Cx Θ} : ∀ {A} → Tm Θ Γ A → Tm Θ Γ A → Set where
  β     : ∀ {A B}(b : Tm Θ (A ∷ Γ) B)(arg : Tm Θ Γ A) → app (lam b) arg ⟶ subTm b (β-env arg)
  ξ-fun : ∀ {A B}{f f′ : Tm Θ Γ (A ⇒↑ B)}{a : Tm Θ Γ A}     → f ⟶ f′ → app f a ⟶ app f′ a
  ξ-arg : ∀ {A B}{f : Tm Θ Γ (A ⇒↑ B)}{a a′ : Tm Θ Γ A}     → a ⟶ a′ → app f a ⟶ app f a′
  ξ-lam : ∀ {A B}{b b′ : Tm Θ (A ∷ Γ) B}            → b ⟶ b′ → lam b ⟶ lam b′
infix 3 _⟶_

-- SUBJECT REDUCTION: t ⟶ t′ already forces t′ : Tm Θ Γ A (the relation is
-- type-indexed).  The whole theorem is discharged by `_⟶_` compiling — the β
-- contractum is well-typed via `subTm`.  Stated explicitly:
preserve : ∀ {Θ}{Γ : Cx Θ}{A}{t t′ : Tm Θ Γ A} → t ⟶ t′ → Tm Θ Γ A
preserve {t′ = t′} _ = t′
