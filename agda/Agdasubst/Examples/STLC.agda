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

syn : Syntax 
syn = record 
  { _⊢_ = _⊢_ 
  ; `_ = `_
  ; `-injective = λ { refl → refl } 
  }
  
open Syntax syn hiding (_⊢_; `_)

_⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (x &ₖ ϕ)
(λx e)          ⋯ ϕ = λx (e ⋯ (ϕ ↑ₖ* _))
(e₁ · e₂)       ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
 
opaque
  unfolding all_kit_definitions
    
  ⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ idₖ ⦃ K ⦄ ≡ t
  ⋯-id ⦃ K ⦄ (` x)     = `/`-is-` ⦃ K ⦄ x
  ⋯-id (λx t)          = cong λx_ (
    t ⋯ (idₖ ↑ₖ expr)  ≡⟨ cong (t ⋯_) (~-ext id↑~id) ⟩
    t ⋯ idₖ            ≡⟨ ⋯-id t ⟩
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
      (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)
    → (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ⨟ₖₖ ϕ₂)
  ⋯-fusion (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
  ⋯-fusion (λx t)         ϕ₁ ϕ₂ = cong λx_ (
    (t ⋯ (ϕ₁ ↑ₖ expr)) ⋯ (ϕ₂ ↑ₖ expr)   ≡⟨ ⋯-fusion t (ϕ₁ ↑ₖ expr) (ϕ₂ ↑ₖ expr) ⟩
    t ⋯ ((ϕ₁ ↑ₖ expr) ⨟ₖₖ (ϕ₂ ↑ₖ expr)) ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑-⨟ expr ϕ₁ ϕ₂))) ⟩
    t ⋯ ((ϕ₁ ⨟ₖₖ ϕ₂) ↑ₖ expr)           ∎)
  ⋯-fusion (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion t₁ ϕ₁ ϕ₂) (⋯-fusion t₂ ϕ₁ ϕ₂)
  ⋯-fusion (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-fusion t₁ ϕ₁ ϕ₂) (⋯-fusion t₂ ϕ₁ ϕ₂)

compose : ComposeTraversal
compose = record { ⋯-fusion = ⋯-fusion }

open import SigmaCalculus

rules : Rules 
rules = record 
  { Sort = Sort 
  ; syn = syn 
  ; traversal = traversal 
  ; compose = compose
  }
open Rules rules

{-# REWRITE 
  &ᵣ-def₁ &ᵣ-def₂ idᵣ-def wkᵣ-def ∷ᵣ-def₁ ∷ᵣ-def₂ 
  &ₛ-def₁ &ₛ-def₂ idₛ-def ∷ₛ-def₁ ∷ₛ-def₂
  ⨟ᵣᵣ-def ⨟ᵣₛ-def ⨟ₛᵣ-def ⨟ₛₛ-def

  left-idᵣᵣ right-idᵣᵣ left-idᵣₛ left-idₛᵣ right-idₛᵣ left-idₛₛ right-idₛₛ
  interactᵣ interactₛ
  associativityᵣᵣᵣ associativityᵣᵣₛ associativityᵣₛᵣ associativityᵣₛₛ associativityₛᵣᵣ associativityₛᵣₛ  associativityₛₛᵣ associativityₛₛₛ
  η-idᵣ η-idₛ η-lawᵣ η-lawₛ
  distributivityᵣᵣ distributivityᵣₛ distributivityₛᵣ distributivityₛₛ
  ⋯idᵣ ⋯idₛ
  compositionalityᵣᵣ compositionalityᵣₛ compositionalityₛᵣ compositionalityₛₛ  
#-}
