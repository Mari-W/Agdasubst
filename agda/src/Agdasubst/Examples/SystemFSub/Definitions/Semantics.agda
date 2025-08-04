-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemFSub.Definitions.Semantics where

open import Agdasubst.Examples.SystemFSub.Definitions.Syntax
open import Agdasubst.Examples.SystemFSub.Substitution

data Neutral : S ⊢ s → Set 
data Value : S ⊢ s → Set 

data Neutral where
  `_  : ∀ (x : S ∋ s) → Neutral (` x)
  _·_ : Neutral e₁ → Value e₂ → Neutral (e₁ · e₂)
  _•t : Neutral e₁ → Neutral (e₁ • t₂)

data Value where
  λx_     : ∀ (e : (expr ∷ S) ⊢ expr) → Value (λx e)
  Λα_     : ∀ (e : (type ∷ S) ⊢ expr) → Value (Λα e)
  neutral : Neutral e → Value e

data _↪_ : S ⊢ s → S ⊢ s → Set where
  β-λ : ∀ {e₂ : S ⊢ expr} →
    ((λx e₁) · e₂) ↪ (e₁ [ e₂ ])
  β-Λ : ∀ {t₂ : S ⊢ type} →
    ((Λα e₁) • t₂) ↪ (e₁ [ t₂ ])
  ξ-λ :
    e ↪ e′ →
    (λx e) ↪ (λx e′)
  ξ-Λ :
    e ↪ e′ →
    (Λα e) ↪ (Λα e′)
  ξ-·₁ :
    e₁ ↪ e₁′ →
    (e₁ · e₂) ↪ (e₁′ · e₂)
  ξ-·₂ :
    e₂ ↪ e₂′ →
    (e₁ · e₂) ↪ (e₁ · e₂′)
  ξ-•₁ :
    e₁ ↪ e₁′ →
    (e₁ • t₂) ↪ (e₁′ • t₂)