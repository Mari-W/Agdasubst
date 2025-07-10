-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
module Agdasubst.Examples.SystemF.SubstitutionPreservesTyping where

open import Agdasubst.Examples.SystemF.Definitions.Syntax
open import Agdasubst.Examples.SystemF.Definitions.Typing
open import Agdasubst.Examples.SystemF.Substitution

_⊢⋯_ :
  ∀ {{K : Kit k}} {{TK : TypingKit K}}
    {S₁ S₂ m} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort m}
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ (e ⋯ ϕ) ∶ (t ⋯ ϕ)
⊢` ⊢x        ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ⊢x)
⊢λ ⊢e        ⊢⋯ ⊢ϕ = ⊢λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢Λ ⊢e        ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢e₁ ⊢e₂   ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
⊢• ⊢e ⊢t ⊢t′ ⊢⋯ ⊢ϕ = ⊢• (⊢e ⊢⋯ ⊢ϕ) (⊢t ⊢⋯ ⊢ϕ) (⊢t′ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢★           ⊢⋯ ⊢ϕ = ⊢★ 

open TypingTraversal (mkTTraversal _⊢⋯_) hiding (_⊢⋯_) public