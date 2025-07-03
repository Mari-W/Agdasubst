-- Author(s): Marius Weidner (2025)
module Examples.SystemF where

-- Imports ---------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Prelude

-- Syntax definition

data Sort : SORT where
  expr : Sort Bind
  type : Sort Bind
  kind : Sort NoBind

open WithSort Sort
open SortsMeta

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
open Syntax syn hiding (_⊢_; `_) 

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
open Traversal traversal hiding (_⋯_; ⋯-id; ⋯-var)

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
open Compose compose hiding (⋯-fusion′)

⋯-fusion : 
  ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} →
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ let instance _ = K₁ ⊔ K₂ in t ⋯ (ϕ₁ ; ϕ₂)
⋯-fusion {{K₁}} {{K₂}} = let instance _ = K₁ ⊔ K₂ in ⋯-fusion′ 

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

--Typing ----------------------------------------------------------------------

instance _ = record { Sort = Sort; syn = syn; traversal = traversal; compose = compose } 

open import Extensions.StandardTyping

types : Types
types = record
  { ↑ᵗ = λ { expr → _ , type ; type → _ , kind ; kind → _ , kind } } 

open Types types

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ′ Γ₁′ Γ₂′ Γ₃′ : Ctx S

data _⊢_∶_ : {s : Sort m} → Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {s : Sort Bind} {x : S ∋ s} {t} → 
    Γ ∋ x ∶ t →
    -------------
    Γ ⊢ (` x) ∶ t
  ⊢λ : 
    (t ∷ₜ Γ) ⊢ e ∶ (weaken t′) → 
    ------------------------
    Γ ⊢ (λx e) ∶ (t ⇒ t′)
  ⊢Λ :
    (★ₖ ∷ₜ Γ) ⊢ e ∶ t →  
    -------------------------
    Γ ⊢ (Λα e) ∶ (∀[α∶ ★ₖ ] t)
  ⊢· : 
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    --------------------
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢• : 
    Γ ⊢ e ∶ (∀[α∶ ★ₖ ] t′) →
    Γ ⊢ t ∶ ★ₖ →
    (★ₖ ∷ₜ Γ) ⊢ t′ ∶ ★ₖ′ →
    ------------------------
    Γ ⊢ (e • t) ∶ (t′ [ t ])
  ⊢★ : 
    ---------
    Γ ⊢ t ∶ ★
 
typing : Typing
typing = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }

open Typing typing hiding (_⊢_∶_; ⊢`) 

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

open TypingTraversal record { _⊢⋯_ = _⊢⋯_ } hiding (_⊢⋯_)

-- Semantics -------------------------------------------------------------------

data Val : S ⊢ expr → Set where
  vλ : Val (λx e)
  vΛ : Val (Λα e)

data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  β-λ :
    Val e₂ →
    ----------------------------
    ((λx e₁) · e₂) ↪ (e₁ [ e₂ ])
  β-Λ :
    ------------------------
    ((Λα e) • t) ↪ (e [ t ])
  ξ-·₁ :
    e₁ ↪ e →
    --------------------
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    --------------------
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-• :
    e ↪ e′ →
    ------------------
    (e • t) ↪ (e′ • t) 

subject-reduction :
  Γ ⊢ e ∶ t →
  e ↪ e′ →
  Γ ⊢ e′ ∶ t
subject-reduction (⊢· (⊢λ ⊢e₁) ⊢e₂)     (β-λ _)         = ⊢e₁ ⊢⋯ₛ ⊢⦅ ⊢e₂ ⦆ₛ
subject-reduction (⊢• (⊢Λ ⊢e) ⊢t ⊢t′) β-Λ               = ⊢e ⊢⋯ₛ ⊢⦅ ⊢t ⦆ₛ
subject-reduction (⊢· ⊢e₁ ⊢e₂)          (ξ-·₁ e₁↪e₁′)   = ⊢· (subject-reduction ⊢e₁ e₁↪e₁′) ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)          (ξ-·₂ e₂↪e₂′ _) = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e₂′)
subject-reduction (⊢• ⊢e ⊢t ⊢t′)        (ξ-• e₁↪e₁′)    = ⊢• (subject-reduction ⊢e e₁↪e₁′) ⊢t ⊢t′ 