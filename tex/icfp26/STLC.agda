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
data Expr (Γ : Ctx) : Type → Set where
  con  : Expr Γ 𝟙
  var  : Γ ∋ T → Expr Γ T
  lam  : Expr (Γ ▷ T) U → Expr Γ (T ⇒ U)
  app  : Expr Γ (T ⇒ U) → Expr Γ T → Expr Γ U

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

lookup : Γ ∋ T → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
lookup here (_ ▷ x) = x
lookup (there x) (γ ▷ _) = lookup x γ

𝓔⟦_⟧ : Expr Γ T → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔⟦ con       ⟧ γ = ∗
𝓔⟦ var x     ⟧ γ = lookup x γ
𝓔⟦ lam e     ⟧ γ = λ v → 𝓔⟦ e ⟧ (γ ▷ v)
𝓔⟦ app e₁ e₂ ⟧ γ = 𝓔⟦ e₁ ⟧ γ (𝓔⟦ e₂ ⟧ γ)
--! }
----------------------------------------
--! DenotationalB {
𝓗⟦_⟧    : Ctx → Set
𝓗⟦ Γ ⟧  = ∀ {T} → Γ ∋ T → 𝓣⟦ T ⟧

update : 𝓣⟦ T ⟧ → 𝓗⟦ Γ ⟧ → 𝓗⟦ Γ ▷ T ⟧
update v γ here       = v
update v γ (there x)  = γ x

𝓔′⟦_⟧ : Expr Γ T → 𝓗⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔′⟦ con        ⟧ γ  = ∗
𝓔′⟦ var x      ⟧ γ  = γ x
𝓔′⟦ lam e      ⟧ γ  = λ v → 𝓔′⟦ e ⟧ (update v γ)
𝓔′⟦ app e₁ e₂  ⟧ γ  = 𝓔′⟦ e₁ ⟧ γ (𝓔′⟦ e₂ ⟧ γ)
--! }
----------------------------------------

_  : Expr ∅ (𝟙 ⇒ 𝟙)
_  = lam (con)

_  : Expr ∅ (𝟙 ⇒ 𝟙)
_  = lam (var here)

variable
  e e₁ e₂ e′ e₁′ e₂′ : Expr Γ T

opaque
  Subst : Ctx → Ctx → Set
  Subst Γ Δ = ∀ {T} → Γ ∋ T → Expr Δ T

  id : Subst Γ Γ
  id = var

  rename : (∀ {T} → Γ ∋ T → Δ ∋ T) → Expr Γ T → Expr Δ T
  rename ρ con = con
  rename ρ (var x) = var (ρ x)
  rename ρ (lam e) = lam (rename (λ { here → here ; (there x) → there (ρ x) }) e)
  rename ρ (app e₁ e₂) = app (rename ρ e₁) (rename ρ e₂)

  ren : (∀ {T} → Γ ∋ T → Δ ∋ T) → Subst Γ Δ
  ren ρ = λ z → var (ρ z)

  lift : Subst Γ Δ → Subst (Γ ▷ T) (Δ ▷ T)
  lift σ here = var here
  lift σ (there x) = rename there (σ x)

  subst : Subst Γ Δ → Expr Γ T → Expr Δ T
  subst σ con = con
  subst σ (var x) = σ x
  subst σ (lam e) = lam (subst (lift σ) e)
  subst σ (app e₁ e₂) = app (subst σ e₁) (subst σ e₂)

  _⊕_ : Subst Γ Δ → Expr Δ T → Subst (Γ ▷ T) Δ
  (σ ⊕ e) here = e
  (σ ⊕ e) (there x) = σ x

  _[_] : Expr (Γ ▷ T) U → Expr Γ T → Expr Γ U 
  e [ e′ ] = subst (id ⊕ e′) e 

--! SmallStep {
data _⟶_ {Γ : Ctx} {T : Type} : Expr Γ T → Expr Γ T → Set where
  ⟶β : ∀ {e₁ : Expr (Γ ▷ U) T} {e₂ : Expr Γ U} →  
    app {Γ = Γ} (lam e₁) e₂ ⟶ (e₁ [ e₂ ])
  ⟶ξ  : e₁ ⟶ e₁′ → app e₁ e₂ ⟶ app e₁′ e₂
--! }

--! Progress {
data Value {Γ} : Expr Γ T → Set where
  con  : Value con
  lam  : (e : Expr (Γ ▷ T) U) → Value (lam e)

data Progress {Γ} : Expr Γ T → Set where
  done  : Value e → Progress e
  step  : e ⟶ e′ → Progress e

progress : (e : Expr ∅ T) → Progress e
progress con      = done con
progress (lam e)  = done (lam e)
progress (app e₁ e₂)
  with progress e₁
... | step x        = step (⟶ξ x)
... | done (lam e)  = step ⟶β
--! }
