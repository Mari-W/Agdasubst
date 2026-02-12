-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemF.SubstitutionPreservesTyping where

open import Agdasubst.Examples.SystemF.Definitions.Syntax
open import Agdasubst.Examples.SystemF.Definitions.Typing
open import Agdasubst.Examples.SystemF.Substitution

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open ≡-Reasoning

_∶_–[_]→_ :  ∀ {K : Kit M} {S₁ S₂} → S₁ –[ K ]→ S₂ → Ctx S₁ → TypingKit K → Ctx S₂ → Set
ϕ ∶ Γ₁ –[ TK ]→ Γ₂ = Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁

--! SF >
--! SPT
_⊢⋯_ : ∀ {{K : Kit M}} {{TK : TypingKit K}}
    {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} 
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  ϕ ∶ Γ₁ –[ TK ]→ Γ₂ →
  Γ₂ ⊢ (e ⋯ ϕ) ∶ (t ⋯ ϕ)
⊢` {x = x} ⊢x  ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ x _ ⊢x) 
⊢λ ⊢e          ⊢⋯ ⊢ϕ = ⊢λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢Λ ⊢e          ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢e₁ ⊢e₂     ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢• ⊢e ⊢t ⊢t′   ⊢⋯ ⊢ϕ = ⊢• (⊢e ⊢⋯ ⊢ϕ) (⊢t ⊢⋯ ⊢ϕ) (⊢t′ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢★             ⊢⋯ ⊢ϕ = ⊢★
  
open TypingTraversal (mkTTraversal _⊢⋯_) hiding (_⊢⋯_) public  
