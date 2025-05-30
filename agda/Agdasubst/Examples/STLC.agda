{-# OPTIONS --rewriting #-}
module Examples.STLC where

open import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Prelude

data Sort : SORT where
  expr : Sort Bind
  type : Sort NoBind

open WithSort Sort
open SortsMeta 

data _⊢_ : SCOPED where
  `_        : S ∋ s → S ⊢ s               
  λx_       : (expr ∷ S) ⊢ expr → S ⊢ expr        
  _·_       : S ⊢ expr → S ⊢ expr → S ⊢ expr      
  _⇒_       : S ⊢ type → S ⊢ type → S ⊢ type 

open import Derive

module Derived where
syn : Syntax
syn = mkSyntax _⊢_ `_ (λ { refl → refl }) 
  
open Syntax syn hiding (_⊢_; `_)

_⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (x & ϕ)
(λx e)          ⋯ ϕ = λx (e ⋯ (ϕ ↑ₖ* _))
(e₁ · e₂)       ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
 
opaque
  unfolding all_kit_definitions
    
  ⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ id ⦃ K ⦄ ≡ t
  ⋯-id ⦃ K ⦄ (` x)     = `/`-is-` ⦃ K ⦄ x
  ⋯-id (λx t)          = cong λx_ (
    t ⋯ (id ↑ₖ expr)    ≡⟨ cong (t ⋯_) (~-ext id↑ₖ~id) ⟩
    t ⋯ id             ≡⟨ ⋯-id t ⟩
    t                  ∎)
  ⋯-id (t₁ · t₂)       = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (t₁ ⇒ t₂)       = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)

traversal : Traversal
traversal = record
  { _⋯_ = _⋯_ 
  ; ⋯-id = ⋯-id 
  ; ⋯-var = λ x ϕ → refl 
  }

open Traversal traversal hiding (_⋯_; ⋯-id; ⋯-var)

opaque 
  unfolding all_kit_and_compose_definitions

  ⋯-fusion :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
      ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄ 
      (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →  
      (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ⨟[ C ] ϕ₂) 
  ⋯-fusion (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂) 
  ⋯-fusion (λx t)         ϕ₁ ϕ₂ = cong λx_ (
    (t ⋯ (ϕ₁ ↑ₖ expr)) ⋯ (ϕ₂ ↑ₖ expr)  ≡⟨ ⋯-fusion t (ϕ₁ ↑ₖ expr) (ϕ₂ ↑ₖ expr) ⟩
    t ⋯ ((ϕ₁ ↑ₖ expr) ⨟ (ϕ₂ ↑ₖ expr))   ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑ₖ-⨟ expr ϕ₁ ϕ₂))) ⟩
    t ⋯ ((ϕ₁ ⨟ ϕ₂) ↑ₖ expr)           ∎)
  ⋯-fusion (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion t₁ ϕ₁ ϕ₂) (⋯-fusion t₂ ϕ₁ ϕ₂)
  ⋯-fusion (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-fusion t₁ ϕ₁ ϕ₂) (⋯-fusion t₂ ϕ₁ ϕ₂) 

compose : ComposeTraversal 
compose = record { ⋯-fusion = ⋯-fusion }

open ComposeTraversal compose hiding (⋯-fusion)

open import SigmaCalculus

rules : Rules 
rules = record 
  { Sort = Sort 
  ; syn = syn 
  ; traversal = traversal 
  ; compose = compose
  }

module RewriteSystem where
  open Rules rules public
  ⋯id : ⦃ K : Kit _∋/⊢_ ⦄ (T : S ⊢ s) → T ⋯ id ⦃ K ⦄ ≡ T 
  ⋯id _ = ⋯-id _ 

  ⋯-fusionᵣᵣ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ ρ₁) ⋯ ρ₂ ≡ T ⋯ (ρ₁ ⨟ ρ₂)
  ⋯-fusionᵣᵣ ρ₁ ρ₂ T = ⋯-fusion T ρ₁ ρ₂

  ⋯-fusionᵣₛ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ ρ₁) ⋯ σ₂ ≡ T ⋯ (ρ₁ ⨟ σ₂)
  ⋯-fusionᵣₛ ρ₁ σ₂ T = ⋯-fusion T ρ₁ σ₂

  ⋯-fusionₛᵣ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ σ₁) ⋯ ρ₂ ≡ T ⋯ (σ₁ ⨟ ρ₂)
  ⋯-fusionₛᵣ σ₁ ρ₂ T = ⋯-fusion T σ₁ ρ₂

  ⋯-fusionₛₛ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ σ₁) ⋯ σ₂ ≡ T ⋯ (σ₁ ⨟ σ₂)
  ⋯-fusionₛₛ σ₁ σ₂ T = ⋯-fusion T σ₁ σ₂

module _ where 
  open RewriteSystem
  {-# REWRITE &-def₁ &-def₂ id-def ∷-def₁ ∷-def₂ wkᵣ-def ⨟ᵣᵣ-def ⨟ᵣₛ-def ⨟ₛᵣ-def ⨟ₛₛ-def left-idᵣᵣ right-idᵣᵣ left-idᵣₛ left-idₛᵣ right-idₛᵣ left-idₛₛ right-idₛₛ interact associativityᵣᵣᵣ associativityᵣᵣₛ associativityᵣₛᵣ associativityᵣₛₛ associativityₛᵣᵣ associativityₛᵣₛ  associativityₛₛᵣ associativityₛₛₛ η-id η-law distributivityᵣᵣ distributivityᵣₛ distributivityₛᵣ distributivityₛₛ ⋯id ⋯-fusionᵣᵣ ⋯-fusionᵣₛ ⋯-fusionₛᵣ ⋯-fusionₛₛ #-}
