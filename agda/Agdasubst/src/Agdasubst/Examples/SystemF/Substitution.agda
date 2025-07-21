-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemF.Substitution where

open import Agdasubst.Examples.SystemF.Definitions.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

_⋯_ : ∀ {{K : Kit k}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (x & ϕ)
(λx e)          ⋯ ϕ = λx (e ⋯ (ϕ ↑ᴷ★ _))
(e₁ · e₂)       ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
(Λα e)          ⋯ ϕ = Λα (e ⋯ (ϕ ↑ᴷ★ _))
(∀[α∶ k ] t)    ⋯ ϕ = ∀[α∶ (k ⋯ ϕ) ] (t ⋯ (ϕ ↑ᴷ★ _))
(e • t)         ⋯ ϕ = (e ⋯ ϕ) • (t ⋯ ϕ)
★               ⋯ ϕ = ★

{-# REWRITE id↑≡id id↑★≡id #-}
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

{-# REWRITE dist–↑–; dist–↑★–; #-} 
⋯-compositionality′ :
  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} →
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
⋯-compositionality′ (` x)        ϕ₁ ϕ₂ =  ⋯-compositionality-`
⋯-compositionality′ (λx e)       ϕ₁ ϕ₂ = cong λx_ (⋯-compositionality′ e (ϕ₁ ↑ᴷ★ _) (ϕ₂ ↑ᴷ★ _)) 
⋯-compositionality′ (e₁ · e₂)    ϕ₁ ϕ₂ = cong₂ _·_  (⋯-compositionality′ e₁ ϕ₁ ϕ₂) (⋯-compositionality′ e₂ ϕ₁ ϕ₂)
⋯-compositionality′ (t₁ ⇒ t₂)    ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-compositionality′ t₁ ϕ₁ ϕ₂) (⋯-compositionality′ t₂ ϕ₁ ϕ₂)  
⋯-compositionality′ (Λα t)       ϕ₁ ϕ₂ = cong Λα_ (⋯-compositionality′ t (ϕ₁ ↑ᴷ type) (ϕ₂ ↑ᴷ type))
⋯-compositionality′ (∀[α∶ k ] t) ϕ₁ ϕ₂ = cong₂ ∀[α∶_]_ (⋯-compositionality′ k ϕ₁ ϕ₂) (⋯-compositionality′ t (ϕ₁ ↑ᴷ type) (ϕ₂ ↑ᴷ type))
⋯-compositionality′ (e • t)      ϕ₁ ϕ₂ = cong₂ _•_ (⋯-compositionality′ e ϕ₁ ϕ₂) (⋯-compositionality′ t ϕ₁ ϕ₂)
⋯-compositionality′ ★            ϕ₁ ϕ₂ = refl
   
instance compose = mkCompose ⋯-compositionality′ 
open Compose compose hiding (⋯-compositionality) public 

⋯-compositionality : -- rewritable variant of  ⋯-compositionality′
  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} →
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ _⋯_ {{_}} t (ϕ₁ ;[ K₁ ;ᶜ K₂ ] ϕ₂)
⋯-compositionality {{K₁}} {{K₂}} = let instance _ = K₁ ⊔ K₂; _ = K₁ ;ᶜ K₂ in ⋯-compositionality′

{-# REWRITE 
  id`-def `id-def comp-wk-def 
  extZ-def extS-def comp-def 
  idR-def idS-def wkR-def wkS-def appR-def appS-def 
  app-var app-compositionality
  interact η-id η-law left-id right-id norm-id distributivity
  ⋯-id ⋯-compositionality
  associativity
#-}  