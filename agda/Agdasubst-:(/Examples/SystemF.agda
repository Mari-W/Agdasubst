{-# OPTIONS --rewriting #-}
module Examples.SystemF where

-- Imports ---------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax; proj₂)
open import Data.List using (drop)

open import Agda.Builtin.Equality.Rewrite

open import Prelude

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
  k k₁ k₂ k₃ k₄ k′ k₁′ k₂′ k₃′ k₄′ : S ⊢ kind 

syn : Syntax
syn = record { _⊢_ = _⊢_ ; `_ = `_ ; `-injective = λ { refl → refl } }
  
open Syntax syn hiding (_⊢_; `_)

_⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
(` x)           ⋯ ϕ = `/id (x & ϕ)
(λx e)          ⋯ ϕ = λx (e ⋯ (ϕ ↑ₖ⋆ _))
(e₁ · e₂)       ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
(t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
(Λα e)          ⋯ ϕ = Λα (e ⋯ (ϕ ↑ₖ⋆ _))
(∀[α∶ k ] t)    ⋯ ϕ = ∀[α∶ (k ⋯ ϕ) ] (t ⋯ (ϕ ↑ₖ⋆ _))
(e • t)         ⋯ ϕ = (e ⋯ ϕ) • (t ⋯ ϕ)
★               ⋯ ϕ = ★
  
opaque
  unfolding all_kit_definitions
    
  ⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ (t : S ⊢ s) → t ⋯ id ⦃ K ⦄ ≡ t
  ⋯-id ⦃ K ⦄ (` x)     = `/`-is-` ⦃ K ⦄ x
  ⋯-id (λx t)          = cong λx_ (
    t ⋯ (id ↑ₖ expr)   ≡⟨ cong (t ⋯_) (~-ext id↑ₖ~id) ⟩
    t ⋯ id             ≡⟨ ⋯-id t ⟩
    t                  ∎)
  ⋯-id (t₁ · t₂)       = cong₂ _·_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (t₁ ⇒ t₂)       = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
  ⋯-id (Λα t)          = cong Λα_ (
    t ⋯ (id ↑ₖ type)   ≡⟨ cong (t ⋯_) (~-ext id↑ₖ~id) ⟩
    t ⋯ id             ≡⟨ ⋯-id t ⟩
    t                  ∎)
  ⋯-id (∀[α∶ k ] t)    = cong₂ ∀[α∶_]_ (⋯-id k) (
    t ⋯ (id ↑ₖ type)   ≡⟨ cong (t ⋯_) (~-ext id↑ₖ~id) ⟩
    t ⋯ id             ≡⟨ ⋯-id t ⟩
    t                  ∎)
  ⋯-id (e • t)         = cong₂ _•_ (⋯-id e) (⋯-id t)
  ⋯-id ★               = refl

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
    ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ C : ComposeKit K₁ K₂ ⦄ →
      (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
      (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ _⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t (ϕ₁ ；[ C ] ϕ₂)
  ⋯-fusion′ (` x)          ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
  ⋯-fusion′ ⦃ K₁ = K₁ ⦄ ⦃ K₂ = K₂ ⦄ (λx t)  ϕ₁ ϕ₂ = let instance _ = K₁ ⊔ K₂ in cong λx_ (
    (t ⋯ (ϕ₁ ↑ₖ expr)) ⋯ (ϕ₂ ↑ₖ expr)        ≡⟨ ⋯-fusion′ t (ϕ₁ ↑ₖ expr) (ϕ₂ ↑ₖ expr) ⟩
    t ⋯ ((ϕ₁ ↑ₖ expr) ； (ϕ₂ ↑ₖ expr))       ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑ₖ-； expr ϕ₁ ϕ₂))) ⟩
    t ⋯ ((ϕ₁ ； ϕ₂) ↑ₖ expr)                 ∎) 
  ⋯-fusion′ (t₁ · t₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)
  ⋯-fusion′ (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-fusion′ t₁ ϕ₁ ϕ₂) (⋯-fusion′ t₂ ϕ₁ ϕ₂)  
  ⋯-fusion′ ⦃ K₁ = K₁ ⦄ ⦃ K₂ = K₂ ⦄ (Λα t)  ϕ₁ ϕ₂ = let instance _ = K₁ ⊔ K₂ in cong Λα_ (
    (t ⋯ (ϕ₁ ↑ₖ type)) ⋯ (ϕ₂ ↑ₖ type)        ≡⟨ ⋯-fusion′ t (ϕ₁ ↑ₖ type) (ϕ₂ ↑ₖ type) ⟩
    t ⋯ ((ϕ₁ ↑ₖ type) ； (ϕ₂ ↑ₖ type))       ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑ₖ-； type ϕ₁ ϕ₂))) ⟩
    t ⋯ ((ϕ₁ ； ϕ₂) ↑ₖ type)                 ∎)
  ⋯-fusion′ ⦃ K₁ = K₁ ⦄ ⦃ K₂ = K₂ ⦄ (∀[α∶ k ] t) ϕ₁ ϕ₂ = let instance _ = K₁ ⊔ K₂ in cong₂ ∀[α∶_]_ 
    (⋯-fusion′ k ϕ₁ ϕ₂) 
    ((t ⋯ (ϕ₁ ↑ₖ type)) ⋯ (ϕ₂ ↑ₖ type)        ≡⟨ ⋯-fusion′ t (ϕ₁ ↑ₖ type) (ϕ₂ ↑ₖ type) ⟩
     t ⋯ ((ϕ₁ ↑ₖ type) ； (ϕ₂ ↑ₖ type))       ≡⟨ cong (t ⋯_) (sym (~-ext (dist-↑ₖ-； type ϕ₁ ϕ₂))) ⟩
     t ⋯ ((ϕ₁ ； ϕ₂) ↑ₖ type)                 ∎)
  ⋯-fusion′ (e • t)         ϕ₁ ϕ₂ = cong₂ _•_ (⋯-fusion′ e ϕ₁ ϕ₂) (⋯-fusion′ t ϕ₁ ϕ₂)
  ⋯-fusion′ ★               ϕ₁ ϕ₂ = refl
  

compose : ComposeTraversal 
compose = record { ⋯-fusion = ⋯-fusion′ }

open ComposeTraversal compose hiding (⋯-fusion)

⋯-fusion : 
  ∀ ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ →
    (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) → 
    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ _⋯_ ⦃ K = K₁ ⊔ K₂ ⦄ t (ϕ₁ ；[ K₁ ；ₖ K₂ ] ϕ₂)
⋯-fusion ⦃ K₁ ⦄ ⦃ K₂ ⦄ = let instance _ = K₁ ；ₖ K₂ in ⋯-fusion′ 

⋯id : ⦃ K : Kit _∋/⊢_ ⦄ (T : S ⊢ s) → T ⋯ id ⦃ K ⦄ ≡ T 
⋯id _ = ⋯-id _ 

{-# REWRITE 
  &-def₁ &-def₂ id-def ∷-def₁ ∷-def₂ wk-def wkm-def

  interact
  left-id right-id
  η-id η-law
 
  distributivity
  associativity
  
  ⋯id 
  ⋯-fusion 
#-}

--Typing ----------------------------------------------------------------------

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
    (k ∷ₜ Γ) ⊢ e ∶ t →  
    -------------------------
    Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
  ⊢· : 
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    --------------------
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢• : 
    Γ ⊢ e ∶ (∀[α∶ k ] t′) →
    Γ ⊢ t ∶ k →
    (k ∷ₜ Γ) ⊢ t′ ∶ k′ →
    ------------------------
    Γ ⊢ (e • t) ∶ (t′ [ t ])
  ⊢★ : 
    ---------
    Γ ⊢ t ∶ ★

typing : Typing
typing = record { _⊢_∶_ = _⊢_∶_ ; ⊢` = ⊢` }

open Typing typing hiding (_⊢_∶_; ⊢`) 


_⊢⋯_ :
  ∀ ⦃ K : Kit _∋/⊢_ ⦄ ⦃ TK : TypingKit K ⦄
    ⦃ C₁ : ComposeKit K Kₛ ⦄ ⦃ C₂ : ComposeKit K Kᵣ ⦄ ⦃ C₃ : ComposeKit K K ⦄
    {S₁ S₂ m} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {s : Sort m}
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {ϕ : S₁ –[ K ]→ S₂} →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ∋*/⊢*[ TK ] ϕ ∶ Γ₁ →
  Γ₂ ⊢ (e ⋯ ϕ) ∶ (t ⋯ ϕ)
⊢` ⊢x ⊢⋯ ⊢ϕ = ⊢`/id (⊢ϕ _ _ ⊢x)
⊢λ ⊢e ⊢⋯ ⊢ϕ = ⊢λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢Λ ⊢e ⊢⋯ ⊢ϕ = ⊢Λ (⊢e ⊢⋯ (⊢ϕ ∋↑/⊢↑ _))
⊢· ⊢e₁ ⊢e₂ ⊢⋯ ⊢ϕ = ⊢· (⊢e₁ ⊢⋯ ⊢ϕ) (⊢e₂ ⊢⋯ ⊢ϕ)
_⊢⋯_ ⦃ K = K ⦄ ⦃ C₂ = C₂ ⦄ {Γ₂ = Γ₂} {ϕ = ϕ} (⊢• {e = e} {t′ = t′} {t = t}  ⊢e ⊢t ⊢t′) ⊢ϕ = subst (Γ₂ ⊢ (e ⋯ ϕ) • (t ⋯ ϕ) ∶_) 
  (cong (t′ ⋯_) (
    ((id/` zero ∙ (ϕ ； wkᵣ)) ； ((t ⋯ ϕ) ∙ id))   
  ≡⟨ {!   !} ⟩     
    (((t ∙ id) ；[ Kₛ ；ₖ K ] ϕ)) ∎)) 
  (⊢• (⊢e ⊢⋯ ⊢ϕ) (⊢t ⊢⋯ ⊢ϕ) (⊢t′ ⊢⋯ (⊢ϕ ∋↑/⊢↑ _)))  
  -- (id/` K zero ∙ (ϕ ；[ K ；ₖ Kᵣ  ] wkᵣ)) ；[ K ；ₖ S ] (t ⋯ ϕ ∙ idS)
  -- ≡ 
  -- ((t ∙ idS) ；[ S ；ₖ K  ] ϕ)  

⊢★ ⊢⋯ ⊢ϕ = ⊢★ 



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
