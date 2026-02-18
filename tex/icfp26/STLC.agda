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
  Γ Δ : Ctx
  T U V : Type
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

----------------------------------------
--! Domains {
data ⊤ : Set where ∗ : ⊤

𝓣⟦_⟧        : Type → Set
𝓣⟦ 𝟙 ⟧      = ⊤
𝓣⟦ T ⇒ U ⟧  = 𝓣⟦ T ⟧ → 𝓣⟦ U ⟧
--! }
----------------------------------------
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
----------------------------------------
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
----------------------------------------

_  : ∅ ⊢ (𝟙 ⇒ 𝟙)
_  = lam (con)

_  : ∅ ⊢ (𝟙 ⇒ 𝟙)
_  = lam (var here)

variable
  e e₁ e₂ e′ e₁′ e₂′ : Γ ⊢ T

opaque
  Ren : Ctx → Ctx → Set
  Ren Γ Δ = ∀ {T} → Γ ∋ T → Δ ∋ T

  Subst : Ctx → Ctx → Set
  Subst Γ Δ = ∀ {T} → Γ ∋ T → Δ ⊢ T

  rename : Ren Γ Δ → Γ ⊢ T → Δ ⊢ T
  rename ρ con = con
  rename ρ (var x) = var (ρ x)
  rename ρ (lam e) = lam (rename (λ { here → here ; (there x) → there (ρ x) }) e)
  rename ρ (app e₁ e₂) = app (rename ρ e₁) (rename ρ e₂)

  id : Subst Γ Γ
  id = var

  ren : Ren Γ Δ → Subst Γ Δ
  ren ρ = λ z → var (ρ z)

  lift : Subst Γ Δ → Subst (Γ ▷ T) (Δ ▷ T)
  lift σ here = var here
  lift σ (there x) = rename there (σ x)

  subst : Subst Γ Δ → Γ ⊢ T → Δ ⊢ T
  subst σ con = con
  subst σ (var x) = σ x
  subst σ (lam e) = lam (subst (lift σ) e)
  subst σ (app e₁ e₂) = app (subst σ e₁) (subst σ e₂)

  _⊕_ : Subst Γ Δ → Δ ⊢ T → Subst (Γ ▷ T) Δ
  (σ ⊕ e) here = e
  (σ ⊕ e) (there x) = σ x

  _[_] : (Γ ▷ T) ⊢ U → Γ ⊢ T → Γ ⊢ U 
  e [ e′ ] = subst (id ⊕ e′) e 

--! SmallStep {
data _⟶_ {Γ} {T} : Γ ⊢ T → Γ ⊢ T → Set where
  β-lam : ∀ {e₁ : (Γ ▷ U) ⊢ T} {e₂ : Γ ⊢ U} →  
    app {Γ = Γ} (lam e₁) e₂ ⟶ (e₁ [ e₂ ])
  ξ-app  : e₁ ⟶ e₁′ → app e₁ e₂ ⟶ app e₁′ e₂
--! }

--! Progress {
data Value {Γ} : Γ ⊢ T → Set where
  con  : Value con
  lam  : (e : (Γ ▷ T) ⊢ U) → Value (lam e)

data Progress : Γ ⊢ T → Set where
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
