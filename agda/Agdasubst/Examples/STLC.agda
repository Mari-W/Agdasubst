-- Author(s): Marius Weidner (2025)
{-# OPTIONS --rewriting #-}
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

_⋯_ : ∀ {{K : Kit k }} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = (λ x ϕ → `/id (x & ϕ)) x ϕ
_⋯_ {k} {S₁} {.Bind} {.expr} {S₂} (λx e) ϕ = {!   !} -- λx (e ⋯ (ϕ ↑ₖ⋆ _))
(e₁ · e₂)       ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)  
 
opaque
  unfolding all_kit_definitions 
    
  ⋯-id : ∀ {{K : Kit k }} (t : S ⊢ s) → t ⋯ id {{K }} ≡ t
  ⋯-id {{K }} (` x)    = `/`-is-` {{K }} x
  ⋯-id (λx t)          = cong λx_ (
    t ⋯ (id ↑ₖ expr)   ≡⟨ cong (t ⋯_) (~-ext id↑ₖ~id) ⟩
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
    ∀ {{K₁ : Kit k₁ }} {{K₂ : Kit k₂ }} {{K₃ : Kit k₃ }} {{C : ComposeKit K₁ K₂ K₃ }} 
      (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
      (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
  ⋯-fusion′ (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
  ⋯-fusion′ (λx t)         ϕ₁ ϕ₂ = cong λx_ (
    (t ⋯ (ϕ₁ ↑ₖ expr)) ⋯ (ϕ₂ ↑ₖ expr)      ≡⟨ ⋯-fusion′ t (ϕ₁ ↑ₖ expr) (ϕ₂ ↑ₖ expr) ⟩
      t  ⋯ ((ϕ₁ ↑ₖ expr) ; (ϕ₂ ↑ₖ expr))  ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑ₖ-; expr ϕ₁ ϕ₂))) ⟩
      t ⋯ (((ϕ₁ ; ϕ₂) ↑ₖ expr))           ∎)  
  ⋯-fusion′ (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)
  ⋯-fusion′ (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)   

compose : Compose 
compose = record { ⋯-fusion = ⋯-fusion′ }

open Compose compose hiding (⋯-fusion)

⋯-fusion :  
  ∀ {{K₁ : Kit k₁ }} {{K₂ : Kit k₂}}
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ let instance _ = K₁ ⊔ K₂ in t ⋯ (ϕ₁ ; ϕ₂)
⋯-fusion {{K₁ }} {{K₂ }} = let instance _ = K₁ ⊔ K₂ in ⋯-fusion′

⋯id : {{K : Kit k }} (T : S ⊢ s) → T ⋯ id {{K }} ≡ T 
⋯id _ = ⋯-id _ 
  