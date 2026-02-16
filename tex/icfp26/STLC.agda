module STLC where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

𝓣⟦_⟧ : Type → Set
𝓣⟦ nat ⟧ = ℕ
𝓣⟦ T ⇒ U ⟧ = 𝓣⟦ T ⟧ → 𝓣⟦ U ⟧

Ctx = List Type

variable
  Γ : Ctx
  T U V : Type

data _∈_ : Type → Ctx → Set where
  here  : T ∈ (T ∷ Γ)
  there : T ∈ Γ → T ∈ (U ∷ Γ)

data Expr (Γ : Ctx) : Type → Set where
  con : ℕ → Expr Γ nat
  var : T ∈ Γ → Expr Γ T
  lam : Expr (T ∷ Γ) U → Expr Γ (T ⇒ U)
  app : Expr Γ (T ⇒ U) → Expr Γ T → Expr Γ U

----------------------------------------

data 𝓖⟦_⟧ : Ctx → Set where
  []  : 𝓖⟦ [] ⟧
  _∷_ : 𝓣⟦ T ⟧ → 𝓖⟦ Γ ⟧ → 𝓖⟦ T ∷ Γ ⟧

lookup : T ∈ Γ → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
lookup here (x ∷ _) = x
lookup (there x) (_ ∷ γ) = lookup x γ

𝓔⟦_⟧ : Expr Γ T → 𝓖⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔⟦ con n ⟧ γ = n
𝓔⟦ var x ⟧ γ = lookup x γ
𝓔⟦ lam e ⟧ γ = λ v → 𝓔⟦ e ⟧ (v ∷ γ)
𝓔⟦ app e₁ e₂ ⟧ γ = 𝓔⟦ e₁ ⟧ γ (𝓔⟦ e₂ ⟧ γ)

----------------------------------------

𝓗⟦_⟧ : Ctx → Set
𝓗⟦ Γ ⟧ = ∀ {T} → T ∈ Γ → 𝓣⟦ T ⟧

update : 𝓣⟦ T ⟧ → 𝓗⟦ Γ ⟧ → 𝓗⟦ T ∷ Γ ⟧
update v γ here = v
update v γ (there x) = γ x

𝓔′⟦_⟧ : Expr Γ T → 𝓗⟦ Γ ⟧ → 𝓣⟦ T ⟧
𝓔′⟦ con n ⟧ γ = n
𝓔′⟦ var x ⟧ γ = γ x
𝓔′⟦ lam e ⟧ γ = λ v → 𝓔′⟦ e ⟧ (update v γ)
𝓔′⟦ app e₁ e₂ ⟧ γ = 𝓔′⟦ e₁ ⟧ γ (𝓔′⟦ e₂ ⟧ γ)

----------------------------------------

_ : Expr [] (nat ⇒ nat)
_ = lam (con zero)

_ : Expr [] (nat ⇒ nat)
_ = lam (var here)

variable
  e e₁ e₂ e′ e₁′ e₂′ : Expr Γ T

postulate
  -- single substitution
  _[_] : Expr (T ∷ Γ) U → Expr Γ T → Expr Γ U 

data _⟶_ {Γ : Ctx} {T : Type} : Expr Γ T → Expr Γ T → Set where
  ⟶β  : app (lam e₁) e₂ ⟶ (e₁ [ e₂ ])
  ⟶ξ  : e₁ ⟶ e₁′ → app e₁ e₂ ⟶ app e₁′ e₂

data Value {Γ} : Expr Γ T → Set where
  con : (n : ℕ) → Value (con n)
  lam : (e : Expr (T ∷ Γ) U) → Value (lam e)

data Progress {Γ} : Expr Γ T → Set where
  done : Value e → Progress e
  step : e ⟶ e′ → Progress e

progress : (e : Expr [] T) → Progress e
progress (con n) = done (con n)
progress (lam e) = done (lam e)
progress (app e₁ e₂)
  with progress e₁
... | step x = step (⟶ξ x)
... | done (lam e) = step ⟶β
