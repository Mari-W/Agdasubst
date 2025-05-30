{-# OPTIONS --rewriting --backtracking-instance-search #-}
module Examples.STLC where

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

unquoteDecl syn = deriveSyntax Sort _⊢_ `_ syn
  
open Syntax syn hiding (_⊢_; `_)

_⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (x & ϕ)
(λx e)          ⋯ ϕ = λx (e ⋯ (ϕ ↑ₖ⋆ _))
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

  ⋯-fusion′ :
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ C : ComposeKit K₁ K₂ ⦄ 
      (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
      (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ _⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t (ϕ₁ ⨟[ C ] ϕ₂)
  ⋯-fusion′ (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
  ⋯-fusion′ ⦃ K₁ = K₁ ⦄ ⦃ K₂ = K₂ ⦄ ⦃ C = C ⦄ (λx t)         ϕ₁ ϕ₂ = cong λx_ (
    (_⋯_ ⦃ K = K₁ ⦄ t (ϕ₁ ↑ₖ expr)) ⋯ (ϕ₂ ↑ₖ expr)       ≡⟨ ⋯-fusion′ t (ϕ₁ ↑ₖ expr) (ϕ₂ ↑ₖ expr) ⟩
    _⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t ((ϕ₁ ↑ₖ expr) ⨟ (ϕ₂ ↑ₖ expr))   
      ≡⟨ cong (_⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t) (sym (Kit.~-ext (K₁ ⊔ K₂) (dist-↑ₖ-⨟ expr ϕ₁ ϕ₂))) ⟩
     _⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t ((Kit._↑ₖ_ (K₁ ⊔ K₂) (ϕ₁ ⨟ ϕ₂) expr))           ∎) 
  ⋯-fusion′ (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)
  ⋯-fusion′ (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)  

compose : ComposeTraversal 
compose = record { ⋯-fusion = ⋯-fusion′ }

open ComposeTraversal compose hiding (⋯-fusion)

⋯-fusion : 
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ _⋯_ ⦃ K₁ ⊔ K₂ ⦄ t (ϕ₁ ⨟[ K₁ ⨟ₖ K₂ ] ϕ₂)
⋯-fusion ⦃ K₁ ⦄ ⦃ K₂ ⦄ = ⋯-fusion′ ⦃ C = K₁ ⨟ₖ K₂ ⦄

open import SigmaCalculus 

⋯id : ⦃ K : Kit _∋/⊢_ ⦄ (T : S ⊢ s) → T ⋯ id ⦃ K ⦄ ≡ T 
⋯id _ = ⋯-id _ 

rules : Rules 
rules = record 
  { Sort = Sort 
  ; syn = syn 
  ; traversal = traversal 
  ; compose = compose
  }
open Rules rules

{-# REWRITE 
  &-def₁ &-def₂ id-def ∷-def₁ ∷-def₂
  wkᵣ-def

  interact
  left-id right-id
  η-id η-law
  distributivity
  
  ⋯id 
  ⋯-fusion 
  associativity
#-}

associativityᵣᵣᵣ  : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (ρ₃ : S₃ →ᵣ S₄) → (ρ₁ ⨟ ρ₂) ⨟ ρ₃ ≡ ρ₁ ⨟ (ρ₂ ⨟ ρ₃)
associativityᵣᵣᵣ a b c = {!    !}
