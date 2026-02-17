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
  Γ : Ctx
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

postulate
  -- single substitution
  _[_] : Expr (Γ ▷ T) U → Expr Γ T → Expr Γ U 

--! SmallStep {
data _⟶_ {Γ : Ctx} {T : Type} : Expr Γ T → Expr Γ T → Set where
  ⟶β  : app (lam e₁) e₂ ⟶ (e₁ [ e₂ ])
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
