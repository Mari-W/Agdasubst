-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
module Agdasubst.Examples.SystemF.Substitution where

open import Agdasubst.Examples.SystemF.Definitions.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

_⋯_ : ∀ {{K : Kit k}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (x & ϕ)
(λx e)          ⋯ ϕ = λx (e ⋯ (ϕ ↑ₖ⋆ _))
(e₁ · e₂)       ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
(Λα e)          ⋯ ϕ = Λα (e ⋯ (ϕ ↑ₖ⋆ _))
(∀[α∶ k ] t)    ⋯ ϕ = ∀[α∶ (k ⋯ ϕ) ] (t ⋯ (ϕ ↑ₖ⋆ _))
(e • t)         ⋯ ϕ = (e ⋯ ϕ) • (t ⋯ ϕ)
★               ⋯ ϕ = ★

{-# REWRITE id↑≡id id↑⋆≡id #-}
⋯-id : ∀ {{K : Kit k}} (t : S ⊢ s) → t ⋯ id ≡ t
⋯-id {{K}} (` x)     = ⋯-id-`
⋯-id (λx e)          = cong λx_ (⋯-id e)
⋯-id (e₁ · e₂)       = cong₂ _·_ (⋯-id e₁) (⋯-id e₂)
⋯-id (t₁ ⇒ t₂)       = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
⋯-id (Λα t)          = cong Λα_ (⋯-id t)
⋯-id (∀[α∶ k ] t)    = cong₂ ∀[α∶_]_ (⋯-id k) (⋯-id t)
⋯-id (e • t)         = cong₂ _•_ (⋯-id e) (⋯-id t)
⋯-id ★               = refl

instance traversal = mkTraversal _⋯_ ⋯-id λ x ϕ → refl
open Traversal traversal hiding (_⋯_; ⋯-id; ⋯-var) public

{-# REWRITE dist–↑–; dist–↑⋆–; #-} 
⋯-fusion′ :
  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} →
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
⋯-fusion′ (` x)        ϕ₁ ϕ₂ =  ⋯-fusion-`
⋯-fusion′ (λx e)       ϕ₁ ϕ₂ = cong λx_ (⋯-fusion′ e (ϕ₁ ↑ₖ⋆ _) (ϕ₂ ↑ₖ⋆ _)) 
⋯-fusion′ (e₁ · e₂)    ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion′ e₁ ϕ₁ ϕ₂) (⋯-fusion′ e₂ ϕ₁ ϕ₂)
⋯-fusion′ (t₁ ⇒ t₂)    ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)  
⋯-fusion′ (Λα t)       ϕ₁ ϕ₂ = cong Λα_ (⋯-fusion′ t (ϕ₁ ↑ₖ type) (ϕ₂ ↑ₖ type))
⋯-fusion′ (∀[α∶ k ] t) ϕ₁ ϕ₂ = cong₂ ∀[α∶_]_ (⋯-fusion′ k ϕ₁ ϕ₂) (⋯-fusion′ t (ϕ₁ ↑ₖ type) (ϕ₂ ↑ₖ type))
⋯-fusion′ (e • t)      ϕ₁ ϕ₂ = cong₂ _•_ (⋯-fusion′ e ϕ₁ ϕ₂) (⋯-fusion′ t ϕ₁ ϕ₂)
⋯-fusion′ ★            ϕ₁ ϕ₂ = refl
   
instance compose = mkCompose ⋯-fusion′ 
open Compose compose hiding (⋯-fusion′) public

⋯-fusion : -- rewritable variant of  ⋯-fusion′
  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} →
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ let instance _ = K₁ ⊔ K₂ in t ⋯ (ϕ₁ ; ϕ₂)
⋯-fusion {{K₁}} {{K₂}} = let instance _ = K₁ ⊔ K₂ in ⋯-fusion′ 

-- Rewrite System  


{-# REWRITE 
  id-def ∙-def₁ ∙-def₂ wk-def wkm-def ;-def 
  `/`-cancel def-&/⋯Cₛ def-&/⋯Cᵣ &/⋯→& &/⋯→&′ &/⋯→⋯ &/⋯→⋯′
  interact η-id η-law left-id right-id norm-id distributivity
  ⋯-id ⋯-fusion
  associativityᵣᵣᵣ associativityᵣᵣₛ associativityᵣᵣₖ
  associativityᵣₛᵣ associativityᵣₛₛ associativityᵣₛₖ
  associativityᵣₖᵣ associativityᵣₖₛ associativityᵣₖₖ
  associativityₛᵣᵣ associativityₛᵣₛ associativityₛᵣₖ
  associativityₛₛᵣ associativityₛₛₛ associativityₛₛₖ 
  associativityₛₖᵣ associativityₛₖₛ associativityₛₖₖ
  associativityₖᵣᵣ associativityₖᵣₛ associativityₖᵣₖ
  associativityₖₛᵣ associativityₖₛₛ associativityₖₛₖ
  associativityₖₖᵣ                  associativityₖₖₖ 
#-} --             associativityₖₖₛ  