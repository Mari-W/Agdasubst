-- ════════════════════════════════════════════════════════════════════
-- SIMPLY TYPED λ-CALCULUS, intrinsically typed.
--
-- The small running example of the paper's introduction: intrinsically
-- typed syntax, two presentations of its denotational semantics, and a
-- progress theorem for weak-head reduction.  Substitution is defined
-- the textbook way — no σ-calculus and no rewrite rules — because this
-- is the baseline against which SystemF.agda is set.
--
-- No postulates, no rewriting.
-- ════════════════════════════════════════════════════════════════════
module STLC where

--! STLC >
--! TypeCtx {
data Type : Set where
  𝟙    : Type
  _⇒_  : Type → Type → Type

data Ctx : Set where
  ∅    : Ctx
  _▷_  : Ctx → Type → Ctx
--! }

variable
  Γ Γ₁ Γ₂ : Ctx
  T U : Type
--! Var
data _∋_ : Ctx → Type → Set where
  here   : (Γ ▷ T) ∋ T
  there  : Γ ∋ T → (Γ ▷ U) ∋ T

--! Expr
data _⊢_ Γ : Type → Set where
  con  : Γ ⊢ 𝟙
  var  : Γ ∋ T → Γ ⊢ T
  lam  : (Γ ▷ T) ⊢ U → Γ ⊢ (T ⇒ U)
  app  : Γ ⊢ (T ⇒ U) → Γ ⊢ T → Γ ⊢ U

--! Domains {
data ⊤ : Set where ∗ : ⊤

𝓣⟦_⟧        : Type → Set
𝓣⟦ 𝟙 ⟧      = ⊤
𝓣⟦ T ⇒ U ⟧  = 𝓣⟦ T ⟧ → 𝓣⟦ U ⟧
--! }
--! DenotationalA {
data 𝓖⟦_⟧ : Ctx → Set where
  []   : 𝓖⟦ ∅ ⟧
  _▷_  : 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧ → 𝓖⟦ Γ ▷ T ⟧

_◇_ : 𝓖⟦ Γ ⟧ → Γ ∋ T → 𝓣⟦ T ⟧
(_ ▷ v) ◇ here     = v
(γ ▷ _) ◇ there x  = γ ◇ x

𝓔⟦_⟧ : Γ ⊢ T → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔⟦ con        ⟧ γ = ∗
𝓔⟦ var x      ⟧ γ = γ ◇ x
𝓔⟦ lam e      ⟧ γ = λ v → 𝓔⟦ e ⟧ (γ ▷ v)
𝓔⟦ app e₁ e₂  ⟧ γ = 𝓔⟦ e₁ ⟧ γ (𝓔⟦ e₂ ⟧ γ)
--! }
--! DenotationalB {
𝓗⟦_⟧    : Ctx → Set
𝓗⟦ Γ ⟧  = ∀ {T} → Γ ∋ T → 𝓣⟦ T ⟧

_▷▷_ : 𝓗⟦ Γ ⟧ → 𝓣⟦ T ⟧ → 𝓗⟦ Γ ▷ T ⟧
(γ ▷▷ v) here       = v
(γ ▷▷ v) (there x)  = γ x

𝓔′⟦_⟧ : Γ ⊢ T → 𝓗⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔′⟦ con        ⟧ γ  = ∗
𝓔′⟦ var x      ⟧ γ  = γ x
𝓔′⟦ lam e      ⟧ γ  = λ v → 𝓔′⟦ e ⟧ (γ ▷▷ v)
𝓔′⟦ app e₁ e₂  ⟧ γ  = 𝓔′⟦ e₁ ⟧ γ (𝓔′⟦ e₂ ⟧ γ)
--! }

_  : ∅ ⊢ (𝟙 ⇒ 𝟙)
_  = lam (con)

_  : ∅ ⊢ (𝟙 ⇒ 𝟙)
_  = lam (var here)

variable
  e e₁ e₂ e′ e₁′ : Γ ⊢ T

-- The textbook substitution machinery, named as in the System F
-- development (SystemF.agda §2 and §5) so that the two can be compared
-- directly: ᴿ marks the renaming world, ˢ the substitution world.
opaque
  Ren : Ctx → Ctx → Set
  Ren Γ₁ Γ₂ = ∀ {T} → Γ₁ ∋ T → Γ₂ ∋ T

  Sub : Ctx → Ctx → Set
  Sub Γ₁ Γ₂ = ∀ {T} → Γ₁ ∋ T → Γ₂ ⊢ T

  -- weakening, and lifting a renaming under a binder
  wkᴿ : Ren Γ (Γ ▷ T)
  wkᴿ = there

  _⇑ᴿ : Ren Γ₁ Γ₂ → Ren (Γ₁ ▷ T) (Γ₂ ▷ T)
  (ρ ⇑ᴿ) here      = here
  (ρ ⇑ᴿ) (there x) = there (ρ x)

  _[_]ᴿ : Γ₁ ⊢ T → Ren Γ₁ Γ₂ → Γ₂ ⊢ T
  con        [ ρ ]ᴿ = con
  var x      [ ρ ]ᴿ = var (ρ x)
  lam e      [ ρ ]ᴿ = lam (e [ ρ ⇑ᴿ ]ᴿ)
  app e₁ e₂  [ ρ ]ᴿ = app (e₁ [ ρ ]ᴿ) (e₂ [ ρ ]ᴿ)

  -- the identity substitution, extension, and lifting under a binder
  idˢ : Sub Γ Γ
  idˢ = var

  _∙ˢ_ : Γ₂ ⊢ T → Sub Γ₁ Γ₂ → Sub (Γ₁ ▷ T) Γ₂
  (e ∙ˢ σ) here      = e
  (e ∙ˢ σ) (there x) = σ x

  _⇑ˢ : Sub Γ₁ Γ₂ → Sub (Γ₁ ▷ T) (Γ₂ ▷ T)
  (σ ⇑ˢ) here      = var here
  (σ ⇑ˢ) (there x) = (σ x) [ wkᴿ ]ᴿ

  _[_]ˢ : Γ₁ ⊢ T → Sub Γ₁ Γ₂ → Γ₂ ⊢ T
  con        [ σ ]ˢ = con
  var x      [ σ ]ˢ = σ x
  lam e      [ σ ]ˢ = lam (e [ σ ⇑ˢ ]ˢ)
  app e₁ e₂  [ σ ]ˢ = app (e₁ [ σ ]ˢ) (e₂ [ σ ]ˢ)

  _[_] : (Γ ▷ T) ⊢ U → Γ ⊢ T → Γ ⊢ U
  e [ e′ ] = e [ e′ ∙ˢ idˢ ]ˢ

--! SmallStep {
data _⟶_ {Γ} {T} : Γ ⊢ T → Γ ⊢ T → Set where
  β-lam  : app (lam e₁) e₂ ⟶ (e₁ [ e₂ ])
  ξ-app  : e₁ ⟶ e₁′ → app e₁ e₂ ⟶ app e₁′ e₂
--! }

--! Progress {
data Value {Γ} : Γ ⊢ T → Set where
  con  : Value con
  lam  : (e : (Γ ▷ T) ⊢ U) → Value (lam e)

data Progress (e : Γ ⊢ T) : Set where
  done  : Value e → Progress e
  step  : e ⟶ e′ → Progress e

progress : (e : ∅ ⊢ T) → Progress e
progress con      = done con
progress (lam e)  = done (lam e)
progress (app e₁ e₂)
  with progress e₁
... | step x        = step (ξ-app x)
... | done (lam e)  = step β-lam
--! }
