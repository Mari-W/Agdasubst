{-# OPTIONS --rewriting #-}
-- Can substitution be defined at all WITHOUT a renaming traversal underneath?
module NoRen where

open import Data.List using (List; []; _∷_)

data Sort : Set where expr type kind : Sort
Scope = List Sort
variable
  s s′ : Sort
  S S₁ S₂ : Scope

data _∋_ : Scope → Sort → Set where
  zero : (s ∷ S) ∋ s
  suc  : S ∋ s → (s′ ∷ S) ∋ s

data _⊢_ : Scope → Sort → Set where
  `_   : S ∋ s → S ⊢ s
  λx_  : (expr ∷ S) ⊢ expr → S ⊢ expr
  _·_  : S ⊢ expr → S ⊢ expr → S ⊢ expr

_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s

wkˢ : ∀ s → S →ˢ (s ∷ S)
wkˢ _ _ x = ` (suc x)

_∙ˢ_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂
(t ∙ˢ σ) _ zero    = t
(t ∙ˢ σ) _ (suc x) = σ _ x

-- the single-algebra attempt: lifting weakens the IMAGE of σ, which is a term,
-- so it must call the substitution traversal itself.
_⋯ˢ_ : S₁ ⊢ s → S₁ →ˢ S₂ → S₂ ⊢ s
_↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)

(` x)     ⋯ˢ σ = σ _ x
(λx e)    ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ _))
(e₁ · e₂) ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)

σ ↑ˢ s = (` zero) ∙ˢ λ _ x → (σ _ x) ⋯ˢ wkˢ s
