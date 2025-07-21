-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemF.SubjectReduction where

open import Agdasubst.Examples.SystemF.Definitions.Syntax
open import Agdasubst.Examples.SystemF.Definitions.Typing
open import Agdasubst.Examples.SystemF.Definitions.Semantics
open import Agdasubst.Examples.SystemF.Substitution
open import Agdasubst.Examples.SystemF.SubstitutionPreservesTyping

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e′ →
  Γ ⊢ e′ ∶ t
subject-reduction (⊢· (⊢λ ⊢e₁) ⊢e₂)     (β-λ _)         = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ
subject-reduction (⊢• (⊢Λ ⊢e) ⊢t ⊢t′) β-Λ               = ⊢e ⊢⋯ₛ ⊢⦅ ⊢t ⦆ₛ
subject-reduction (⊢· ⊢e₁ ⊢e₂)          (ξ-·₁ e₁↪e₁′)   = ⊢· (subject-reduction ⊢e₁ e₁↪e₁′) ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)          (ξ-·₂ e₂↪e₂′ _) = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂′)
subject-reduction (⊢• ⊢e ⊢t ⊢t′)        (ξ-• e₁↪e₁′)    = ⊢• (subject-reduction ⊢e e₁↪e₁′) ⊢t ⊢t′ 