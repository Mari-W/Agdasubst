module Kits where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

data SortTy : Set where Var NoVar : SortTy

infix  4  _∋_
data _∋_ {ℓ} {A : Set ℓ} : List A → A → Set ℓ where
  zero  : ∀ {xs x} → (x ∷ xs) ∋ x
  suc   : ∀ {xs x x′} → xs ∋ x → (x′ ∷ xs) ∋ x

record Syntax : Set₁ where
  field
    Sort         : SortTy → Set
    _⊢_          : ∀ {st} → List (Sort Var) → Sort st → Set
    `_           : ∀ {S} {s : Sort Var} → S ∋ s → S ⊢ s
    `-injective  : ∀ {S s} {x₁ x₂ : s ∋ S} → ` x₁ ≡ ` x₂ → x₁ ≡ x₂
  
  private variable
    st                         : SortTy
    s s₁ s₂ s₃ s′ s₁′ s₂′ s₃′  : Sort st
    S S₁ S₂ S₃ S′ S₁′ S₂′ S₃′  : List (Sort Var)
    x x₁ x₂ x₃ x′ x₁′ x₂′ x₃′  : S ∋ s

  Scoped = List (Sort Var) → Sort Var → Set

  record Kit (_∋/⊢_ : Scoped) : Set where

    _∋/⊢[_]_ : ∀ {_∋/⊢_ : Scoped} → List (Sort Var) → Kit _∋/⊢_ → Sort Var → Set
    _∋/⊢[_]_ {_∋/⊢_} S K s = S ∋/⊢ s
    
    field
      id/`            : S ∋ s → S ∋/⊢ s
      `/id            : S ∋/⊢ s → S ⊢ s
      wk              : ∀ s' → S ∋/⊢ s → (s' ∷ S) ∋/⊢ s
      
      `/`-is-`        : ∀ (x : S ∋ s) → `/id (id/` x) ≡ ` x
      id/`-injective  : id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
      `/id-injective  :  ∀ {x/t₁ x/t₂ : S ∋/⊢ s} →
                         `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂
      wk-id/`         :  ∀ s' (x : S ∋ s) →
                         wk s' (id/` x) ≡ id/` (suc x)  
    opaque 
      _→ₖ_ : List (Sort Var) → List (Sort Var) → Set
      S₁ →ₖ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢ s

      infixl  8  _&_
      _&_ : S₁ ∋ s → S₁ →ₖ S₂ → S₂ ∋/⊢ s
      x & ϕ = ϕ _ x 
  
    
    -- wkm : ∀ s → S₁ →ₖ S₂ → S₁ →ₖ (s ∷ S₂)
    -- wkm s ϕ _ x = wk s (ϕ _ x)

    opaque 
      unfolding _→ₖ_
      _∷ₖ_ : S₂ ∋/⊢ s → S₁ →ₖ S₂ → (s ∷ S₁) →ₖ S₂
      (x/t ∷ₖ ϕ) _ zero     = x/t
      (x/t ∷ₖ ϕ) _ (suc x)  = ϕ _ x