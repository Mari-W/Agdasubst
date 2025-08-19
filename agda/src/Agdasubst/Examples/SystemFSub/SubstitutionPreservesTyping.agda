-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemFSub.SubstitutionPreservesTyping where

open import Agdasubst.Examples.SystemFSub.Definitions.Syntax
open import Agdasubst.Examples.SystemFSub.Definitions.Typing
open import Agdasubst.Examples.SystemFSub.Substitution

_⊢⋯_ :
  ∀ {{K : Kit k}} {{TK : TypingKit K}}
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ (e ⋯ ϕ) ∶ (t ⋯ ϕ)
_⊑⋯_ :
  ∀ {{K : Kit k}} {{TK : TypingKit K}}
    {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ t₁ ⊑ t₂ →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ (t₁ ⋯ ϕ) ⊑ (t₂ ⋯ ϕ)

⊑-` t₁⊑t₂ y t₂⊑t₃  ⊑⋯ ⊢ϕ = ⊑-` (t₁⊑t₂ ⊑⋯ ⊢ϕ) (y ⊢⋯ ⊢ϕ) (t₂⊑t₃ ⊑⋯ ⊢ϕ)
⊑-`⊤               ⊑⋯ ⊢ϕ = ⊑-`⊤
⊑-⇒ t₁⊑t₂ t₁⊑t₃    ⊑⋯ ⊢ϕ = ⊑-⇒ (t₁⊑t₂ ⊑⋯ ⊢ϕ) (t₁⊑t₃ ⊑⋯ ⊢ϕ)
_⊑⋯_ {ϕ = ϕ} (⊑-∀ t₁⊑t₂) ⊢ϕ rewrite norm–idˢ ϕ = ⊑-∀ (t₁⊑t₂ ⊑⋯ (⊢ϕ ∋↑/⊢↑ _))
⊑-refl-var         ⊑⋯ ⊢ϕ = ⊑-refl  

⊢` {x = x} ⊢x      ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ x _ ⊢x)
_⊢⋯_ {ϕ = ϕ} (⊢λ ⊢e             ) ⊢ϕ rewrite norm–idˢ ϕ = ⊢λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
_⊢⋯_ {ϕ = ϕ} (⊢Λ ⊢e             ) ⊢ϕ rewrite norm–idˢ ϕ = ⊢Λ (⊢e ⊢⋯ ((⊢ϕ ∋↑/⊢↑ _) ∋↑/⊢↑ _))
_⊢⋯_ {ϕ = ϕ} (⊢· ⊢e₁ ⊢e₂        ) ⊢ϕ rewrite norm–idˢ ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
_⊢⋯_ {ϕ = ϕ} (⊢• ⊢t₁ ⊢t₂ t₂⊑t ⊢e) ⊢ϕ rewrite norm–idˢ ϕ = ⊢• (⊢t₁ ⊢⋯ ((⊢ϕ ∋↑/⊢↑ _) ∋↑/⊢↑ _)) (⊢t₂ ⊢⋯ ⊢ϕ) (t₂⊑t ⊑⋯ ⊢ϕ) (⊢e ⊢⋯ ⊢ϕ)  
⊢tt                ⊢⋯ ⊢ϕ = ⊢tt
⊢★                 ⊢⋯ ⊢ϕ = ⊢★  
⊢cstr t₁⊑t₂        ⊢⋯ ⊢ϕ = ⊢cstr (t₁⊑t₂ ⊑⋯ ⊢ϕ)
⊢⊑ ⊢e t₁⊑t₂        ⊢⋯ ⊢ϕ = ⊢⊑ (⊢e ⊢⋯ ⊢ϕ) (t₁⊑t₂ ⊑⋯ ⊢ϕ)  

open TypingTraversal (mkTTraversal _⊢⋯_) hiding (_⊢⋯_) public 