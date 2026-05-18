-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --double-check #-}
module SystemFo-semantics where
open import Agda.Builtin.Equality.Rewrite public

-- standard equational reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import SystemFo

-- single substitution, semantics, and progress
--! FO >
--! Sem >
--! SingleSub {
_[_] : Expr (Γ ▷ T′) T → Expr Γ T′ → Expr Γ T
e [ e′ ] = idˢ ∣ e [ idˢ ∣ e′ ∙ˢ Idˢ ]ˢ

_[*_*] : Expr (Γ ▷*) T → (T′ : Type Φ J) → Expr Γ (T [ T′ ]*)
e [* T′ *] = (T′ ∙ˢ idˢ) ∣ e [ idˢ ∣ T′ ∙ˢ* Idˢ ]ˢ
--! }

--! Definition
data _⟶_ : Expr Γ T → Expr Γ T → Set where
  β-λ   : (λx e₁ · e₂) ⟶ (e₁ [ e₂ ])
  β-Λ   : (Λα e ·* T′) ⟶ (e [* T′ *])
  ξ-·   : e₁ ⟶ e₁′ → (e₁ · e₂) ⟶ (e₁′ · e₂)
  ξ-·*  : e ⟶ e′ → (e ·* T) ⟶ (e′ ·* T)
  ξ-Λ   : e ⟶ e′ → (Λα e) ⟶ (Λα e′)
  ξ-conv : ∀{eq : T ≡β T′} → e ⟶ e′ → conv e eq ⟶ conv e′ eq
  β-conv : ∀{eq : T ≡β T} → conv e eq ⟶ e

data _⟶*_ : Expr Γ T → Expr Γ T → Set where
  ⟶refl  : e ⟶* e
  ⟶trans : e₁ ⟶ e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; contradiction)

--! ProgressDefs {
data Value : Expr Γ T → Set where
  λx : (e : Expr (Γ ▷ T₁) T₂) → Value (λx e)
  Λα : Value e → Value (Λα e)

data Progress : Expr Γ T → Set where
  done : (v : Value e) → Progress e
  step : (e⟶e′ : e ⟶ e′) → Progress e

data NoVar : Ctx Φ → Set where
  ∅   : NoVar ∅
  _▷* : NoVar Γ → NoVar {Φ ▷* J} (Γ ▷*)

noVar : NoVar Γ → ¬ (Γ ∋ T)
noVar (nv ▷*) (suc* x) = noVar nv x
--! }

{-# REWRITE β≡* #-}

admissible : ∀{A B : Type Φ J} → A ≡β B → A ≡ B
admissible (β≡β B A)      = refl
admissible (refl≡β A)     = refl
admissible (sym≡β x)      = sym (admissible x)
admissible (trans≡β x x₁) = trans (admissible x) (admissible x₁)
admissible (⇒≡β x x₁)     = cong₂ _⇒_ (admissible x) (admissible x₁)
admissible (Π≡β x)        = cong ∀α (admissible x)
admissible (ƛ≡β x)        = cong λα (admissible x)
admissible (·≡β x x₁)     = cong₂ _$_ (admissible x) (admissible x₁)

--! Progress
progress : NoVar Γ → (e : Expr Γ T) → Progress e
progress nv (` x) = ⊥-elim (noVar nv x)
progress nv (λx e) = done (λx e)
progress nv (e · e′)
  with progress nv e
... | done (λx e₁) = step β-λ
... | step e⟶e′ = step (ξ-· e⟶e′)
progress nv (Λα e)
  with progress (nv ▷*) e
... | done v = done (Λα v)
... | step e⟶e′ = step (ξ-Λ e⟶e′)
progress nv (e ·* T′)
  with progress nv e
... | done (Λα v) = step β-Λ
... | step e⟶e′ = step (ξ-·* e⟶e′)
progress nv (conv e eq) 
  with refl ← admissible eq
  with progress nv e
... | done v = step β-conv
... | step e⟶e′ = step (ξ-conv e⟶e′)

-- execution

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; ∃-syntax; _,_; _×_)

run : {T : Type ∅ ∗} → ℕ → (e : Expr ∅ T) → ∃[ e′ ] e ⟶* e′ × Maybe (Value e′)
run zero e = e , ⟶refl , nothing
run (suc n) e
  with progress ∅ e
... | done v = e , ⟶refl , just v
... | step {e′ = e′} e⟶e′
  with run n e′
... | e″ , e′⟶e″ , mve″ = e″ , ⟶trans e⟶e′ e′⟶e″ , mve″
