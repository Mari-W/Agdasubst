-- Author(s): Marius Weidner (2025)
module Examples.SimplyTyped.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

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
syn = record { _⊢_  = _⊢_ ; `_ = `_ ; `-injective = λ { refl → refl } }
open Syntax syn hiding (_⊢_; `_) 

_⋯_ : ∀ {{K : Kit k}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (x & ϕ)
(λx e)          ⋯ ϕ = λx (e ⋯ (ϕ ↑ₖ⋆ _))
(e₁ · e₂)       ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ) 

{-# REWRITE id↑≡id id↑⋆≡id #-} -- special cases of rewrite rules added later
⋯-id : ∀ {{K : Kit k}} (t : S ⊢ s) → t ⋯ id ≡ t
⋯-id (` x)     = ⋯-id-`
⋯-id (λx e)    = cong λx_ (⋯-id e)
⋯-id (e₁ · e₂) = cong₂ _·_ (⋯-id e₁) (⋯-id e₂)
⋯-id (t₁ ⇒ t₂) = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)

traversal : Traversal
traversal = record { _⋯_ = _⋯_   ; ⋯-id = ⋯-id ; ⋯-var = λ _ _ → refl }
open Traversal traversal hiding (_⋯_; ⋯-id; ⋯-var)

{-# REWRITE dist–↑–; dist–↑⋆–; #-} 
⋯-fusion′ :
  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} 
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
⋯-fusion′ (` x)     ϕ₁ ϕ₂ = ⋯-fusion-`
⋯-fusion′ (λx t)    ϕ₁ ϕ₂ = cong λx_ (⋯-fusion′ t (ϕ₁ ↑ₖ _) (ϕ₂ ↑ₖ _))   
⋯-fusion′ (t₁ · t₂) ϕ₁ ϕ₂ = cong₂ _·_ (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)
⋯-fusion′ (t₁ ⇒ t₂) ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)   

compose : Compose 
compose = record { ⋯-fusion′ = ⋯-fusion′ }

open Compose compose hiding (⋯-fusion′) 

⋯-fusion :  
  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}}
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ let instance _ = K₁ ⊔ K₂ in t ⋯ (ϕ₁ ; ϕ₂)
⋯-fusion {{K₁}} {{K₂}} = let instance _ = K₁ ⊔ K₂ in ⋯-fusion′

  