-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
module Examples.SystemFSubtyping.Definitions where

-- Imports ---------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Prelude public

-- Syntax definition

data Sort : SORT where
  expr : Sort Bind
  type : Sort Bind
  kind : Sort NoBind
  cstr : Sort Bind
  

open WithSort Sort public
open SortsMeta public

data _⊢_ : SCOPED where
  `_        : S ∋ s → S ⊢ s     
  λx_     : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_     : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_ : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_     : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_     : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_     : S ⊢ type → S ⊢ type → S ⊢ type
  ★       : S ⊢ kind
 
variable
  e e₁ e₂ e₃ e₄ e′ e₁′ e₂′ e₃′ e₄′ : S ⊢ expr
  t t₁ t₂ t₃ t₄ t′ t₁′ t₂′ t₃′ t₄′ : S ⊢ type
  ★ₖ ★ₖ′                           : S ⊢ kind

syn : Syntax 
syn = record { _⊢_  = _⊢_ ; `_ = `_ ; `-injective = λ { refl → refl } }
open Syntax syn hiding (_⊢_; `_) public

-- Traversal definition

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

traversal : Traversal
traversal = record { _⋯_ = _⋯_  ; ⋯-id = ⋯-id  ; ⋯-var = λ x ϕ → refl }
open Traversal traversal hiding (_⋯_; ⋯-id; ⋯-var) public

-- Compositionality definition

{-# REWRITE dist–↑–; dist–↑⋆–; #-} 
⋯-fusion′ :
  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} →
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ;[ C ] ϕ₂)
⋯-fusion′ (` x)        ϕ₁ ϕ₂ =  ⋯-fusion-`
⋯-fusion′ (λx e)       ϕ₁ ϕ₂ = cong λx_ (⋯-fusion′ e (ϕ₁ ↑ₖ⋆ _) (ϕ₂ ↑ₖ⋆ _)) 
⋯-fusion′ (e₁ · e₂)    ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion′ e₁ ϕ₁ ϕ₂) (⋯-fusion′ e₂ ϕ₁ ϕ₂)
⋯-fusion′ (t₁ ⇒ t₂)    ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)  
⋯-fusion′ (Λα t)       ϕ₁ ϕ₂ = cong Λα_ (⋯-fusion′ t (ϕ₁ ↑ₖ type) (ϕ₂ ↑ₖ type))
⋯-fusion′ (∀[α∶ k ] t) ϕ₁ ϕ₂ = cong₂ ∀[α∶_]_ (⋯-fusion′ k ϕ₁ ϕ₂) (⋯-fusion′ t (ϕ₁ ↑ₖ type) (ϕ₂ ↑ₖ type))
⋯-fusion′ (e • t)      ϕ₁ ϕ₂ = cong₂ _•_ (⋯-fusion′ e ϕ₁ ϕ₂) (⋯-fusion′ t ϕ₁ ϕ₂)
⋯-fusion′ ★            ϕ₁ ϕ₂ = refl
   
compose : Compose 
compose = record { ⋯-fusion′ = ⋯-fusion′ }
open Compose compose hiding (⋯-fusion′) public


⋯-fusion : -- rewritable variant of  ⋯-fusion′
  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} →
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ let instance _ = K₁ ⊔ K₂ in t ⋯ (ϕ₁ ; ϕ₂)
⋯-fusion {{K₁}} {{K₂}} = let instance _ = K₁ ⊔ K₂ in ⋯-fusion′ 

-- Rewrite System 

{-# REWRITE 
  id-def ∙-def₁ ∙-def₂ wk-def wkm-def ;-def def-&/⋯Cₛ def-&/⋯Cᵣ
  &/⋯-law₁ 
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