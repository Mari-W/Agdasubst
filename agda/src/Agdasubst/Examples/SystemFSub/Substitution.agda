-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemFSub.Substitution where

open import Agdasubst.Examples.SystemFSub.Definitions.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

--! FS >

module _ where
  private _⋯_ : ∀ {{K : Kit M}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
  (` x)          ⋯ ϕ = x `⋯ ϕ

  --!! LambdaExT
  (λx e)         ⋯ ϕ = λx (e ⋯ (ϕ ↑ expr))

  (e₁ · e₂)      ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
  (t₁ ⇒ t₂)      ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
  (Λα e)         ⋯ ϕ = Λα (e ⋯ (ϕ ↑★ _))
  (∀[α⊑ t₁ ] t₂) ⋯ ϕ = ∀[α⊑ (t₁ ⋯ ϕ) ] (t₂ ⋯ (ϕ ↑★ _))
  (e • t)        ⋯ ϕ = (e ⋯ ϕ) • (t ⋯ ϕ)
  `tt            ⋯ ϕ = `tt
  `⊤             ⋯ ϕ = `⊤
  (t₁ ∶⊑ t₂)     ⋯ ϕ = (t₁ ⋯ ϕ) ∶⊑ (t₂ ⋯ ϕ)
  ★              ⋯ ϕ = ★  
  sat            ⋯ ϕ = sat
  ✰              ⋯ ϕ = ✰


  {-# REWRITE id↑≡id id↑★≡id #-}
  ⋯-right-id : ∀ {{K : Kit M}} (t : S ⊢ s) → t ⋯ id ≡ t
  ⋯-right-id {{K}} (` x)    = `⋯-right-id x
  ⋯-right-id (λx e)         = cong λx_ (⋯-right-id e)
  ⋯-right-id (e₁ · e₂)      = cong₂ _·_ (⋯-right-id e₁) (⋯-right-id e₂)
  ⋯-right-id (t₁ ⇒ t₂)      = cong₂ _⇒_ (⋯-right-id t₁) (⋯-right-id t₂)
  ⋯-right-id (Λα t)         = cong Λα_ (⋯-right-id t)
  ⋯-right-id (∀[α⊑ t₁ ] t₂) = cong₂ ∀[α⊑_]_ (⋯-right-id t₁) (⋯-right-id t₂)
  ⋯-right-id (e • t)        = cong₂ _•_ (⋯-right-id e) (⋯-right-id t)
  ⋯-right-id `tt            = refl
  ⋯-right-id `⊤             = refl
  ⋯-right-id (t₁ ∶⊑ t₂)     = cong₂ _∶⊑_ (⋯-right-id t₁) (⋯-right-id t₂)
  ⋯-right-id ★              = refl
  ⋯-right-id sat            = refl
  ⋯-right-id ✰              = refl 
  
  ⋯-var : ∀ {{K : Kit M}} → (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) →
                     (` x) ⋯ ϕ ≡ x `⋯ ϕ
  ⋯-var _ _ = refl

  instance traversal = mkTraversal _⋯_ ⋯-right-id ⋯-var
  open Traversal traversal hiding (_⋯_; ⋯-right-id; ⋯-var) public

  
  {-# REWRITE dist–↑–; dist–↑★–; #-} 
  ⋯-compositionality :
    ∀ {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{C : ComposeKit K₁ K₂ K₃}} →
      (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
      (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
  ⋯-compositionality (` x)          ϕ₁ ϕ₂ = `⋯-compositionality x ϕ₁ ϕ₂
  ⋯-compositionality (λx e)         ϕ₁ ϕ₂ = cong λx_ (⋯-compositionality e (ϕ₁ ↑★ _) (ϕ₂ ↑★ _)) 
  ⋯-compositionality (e₁ · e₂)      ϕ₁ ϕ₂ = cong₂ _·_  (⋯-compositionality e₁ ϕ₁ ϕ₂) (⋯-compositionality e₂ ϕ₁ ϕ₂)
  ⋯-compositionality (t₁ ⇒ t₂)      ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-compositionality t₁ ϕ₁ ϕ₂) (⋯-compositionality t₂ ϕ₁ ϕ₂)  
  ⋯-compositionality (Λα t)         ϕ₁ ϕ₂ = cong Λα_ (⋯-compositionality t (ϕ₁ ↑ type) (ϕ₂ ↑ type))
  ⋯-compositionality (∀[α⊑ t₁ ] t₂) ϕ₁ ϕ₂ = cong₂ ∀[α⊑_]_ (⋯-compositionality t₁ ϕ₁ ϕ₂) (⋯-compositionality t₂ (ϕ₁ ↑ type) (ϕ₂ ↑ type))
  ⋯-compositionality (e • t)        ϕ₁ ϕ₂ = cong₂ _•_ (⋯-compositionality e ϕ₁ ϕ₂) (⋯-compositionality t ϕ₁ ϕ₂)
  ⋯-compositionality `tt            ϕ₁ ϕ₂ = refl 
  ⋯-compositionality `⊤             ϕ₁ ϕ₂ = refl
  ⋯-compositionality (t₁ ∶⊑ t₂)     ϕ₁ ϕ₂ = cong₂ _∶⊑_ (⋯-compositionality t₁ ϕ₁ ϕ₂) (⋯-compositionality t₂ ϕ₁ ϕ₂)
  ⋯-compositionality ★              ϕ₁ ϕ₂ = refl
  ⋯-compositionality sat            ϕ₁ ϕ₂ = refl
  ⋯-compositionality ✰              ϕ₁ ϕ₂ = refl

  instance compose = mkCompose ⋯-compositionality 
  open Compose compose hiding (⋯-compositionality) public
 
opaque
  unfolding lib   
  &/⋯–`   : {{K : Kit M}}   {{C : ComposeKit K V K}}{ϕ : S₁ –[ K ]→ S₂} → 
    (`_ {s = s} x)  &/⋯ ϕ ≡ `/id (x &/⋯ ϕ)                     ; &/⋯–`  = refl
  &/⋯–λ   : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → 
    --!! LambdaExL
    (λx e) &/⋯ ϕ ≡ λx (e &/⋯ (ϕ ↑ expr))                
  
  &/⋯–λ  = refl
  &/⋯–·   : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → (e₁ · e₂)       &/⋯ ϕ ≡ (e₁ &/⋯ ϕ) · (e₂ &/⋯ ϕ)           ; &/⋯–·  = refl
  &/⋯–⇒   : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → (t₁ ⇒ t₂)       &/⋯ ϕ ≡ (t₁ &/⋯ ϕ) ⇒ (t₂ &/⋯ ϕ)           ; &/⋯–⇒  = refl
  &/⋯–Λ   : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → (Λα e)          &/⋯ ϕ ≡ Λα (e &/⋯ (ϕ ↑ _))                ; &/⋯–Λ = refl
  &/⋯–∀   : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → (∀[α⊑ t₁ ] t₂)  &/⋯ ϕ ≡ ∀[α⊑ t₁ &/⋯ ϕ ] (t₂ &/⋯ (ϕ ↑ _))  ; &/⋯–∀  = refl
  &/⋯–•   : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → (e • t)         &/⋯ ϕ ≡ (e &/⋯ ϕ) • (t &/⋯ ϕ)             ; &/⋯–• = refl 
  &/⋯–tt  : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → `tt             &/⋯ ϕ ≡ `tt                               ; &/⋯–tt  = refl
  &/⋯–`⊤  : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → `⊤              &/⋯ ϕ ≡ `⊤                                ; &/⋯–`⊤ = refl
  &/⋯–∶⊑  : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → (t₁ ∶⊑ t₂)      &/⋯ ϕ ≡ (t₁ &/⋯ ϕ) ∶⊑ (t₂ &/⋯ ϕ)          ; &/⋯–∶⊑ = refl
  &/⋯–★   : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → ★               &/⋯ ϕ ≡ ★                                 ; &/⋯–★ = refl 
  &/⋯–sat : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → sat             &/⋯ ϕ ≡ sat                               ; &/⋯–sat = refl 
  &/⋯–✰   : {{K : Kit M}} {{C : ComposeKit K V K}} {ϕ : S₁ –[ K ]→ S₂} → ✰               &/⋯ ϕ ≡ ✰                                 ; &/⋯–✰  = refl 

_&_ : {{K : Kit M}} → S₁ ∋ s → S₁ –[ K ]→ S₂ → S₂ ∋/⊢[ K ] s
_&_ = _&/⋯_ 

_⋯_ : {{K : Kit M}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
_⋯_ {{K}} = let instance _ = K ;ᴷ V in _&/⋯_ 

{-# REWRITE 
  id`–def `id–def ;wk–def
  idˢ–def  compₗ–idˢ–def compᵣ–idˢ–def 
  wk–def   compₗ–wk–def 
  ext₀–def compₗ–ext₀–def 
  extₛ–def compₗ–extₛ–def
  comp–def–safe

  compᵣ–id compₗ–id 
  associativity distributivity interact
  η–id η–law

  compositionality–safe
  right–id
  &/⋯–` &/⋯–λ &/⋯–· &/⋯–⇒ &/⋯–Λ &/⋯–∀ &/⋯–• &/⋯–tt &/⋯–`⊤ &/⋯–∶⊑ &/⋯–★ &/⋯–sat &/⋯–✰ 
  coincidence coincidence–foldᴷ coincidence–foldᵀ
#-}  

-- {-# REWRITE  id`–def `id–def ;wk–def idˢ–def #-}
-- 
-- ex : ?
-- ex = 
--   --!! ExTerm
--   ((` zero) ∙ˢ ((t₁ ∙ˢ idˢ) ; wk)) ; (t₂ ∙ˢ idˢ)          
-- 
-- ≡⟨ distributivity (` zero) ((t₁ ∙ˢ idˢ) ; wk) (t₂ ∙ˢ idˢ) ⟩
--     (((` zero) ⋯ (t₂ ∙ˢ idˢ)) ∙ˢ (((t₁ ∙ˢ idˢ) ; wk) ; (t₂ ∙ˢ idˢ))) ≡⟨ cong (_ ∙ˢ_) (associativity (t₁ ∙ˢ idˢ) wk (t₂ ∙ˢ idˢ)) ⟩
--     (((` zero) ⋯ (t₂ ∙ˢ idˢ)) ∙ˢ ((t₁ ∙ˢ idˢ) ; (wk ; (t₂ ∙ˢ idˢ)))) ≡⟨ {! interact  !} ⟩
--     ((((` zero) ⋯ (t₂ ∙ˢ idˢ)) ∙ˢ ((t₁ ∙ˢ idˢ) ; idˢ)))              ≡⟨ {!   !} ⟩ 
--     {!   !}
--   ∎ 
-- 
-- {-# REWRITE 
--   id`–def `id–def ;wk–def
--   associativity distributivity interact
--   norm–idˢ
-- #-}  
-- 
-- foo : (e : (s ∷ S) ⊢ s) (t₂ : S ⊢ s) (t₁ : S ⊢ s) {{K : Kit M}} 
--     (ϕ : S₁ –[ K ]→ S₂) → {!   !} 
-- 
-- foo {s = s} e t₂ t₁ ϕ  = {! (⦅ t₁ ⦆ˢ ↑ s) ; ⦅ t₂ ⦆ˢ  !}
-- 
