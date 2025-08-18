-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemF.Substitution where

open import Agdasubst.Examples.SystemF.Definitions.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

module _ where
  private _⋯_ : ∀ {{K : Kit k}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
  (` x)           ⋯ ϕ = x `⋯ ϕ
  (λx e)          ⋯ ϕ = λx (e ⋯ (ϕ ↑ _))
  (e₁ · e₂)       ⋯ ϕ = (e₁ ⋯ ϕ) · (e₂ ⋯ ϕ)
  (t₁ ⇒ t₂)       ⋯ ϕ = (t₁ ⋯ ϕ) ⇒ (t₂ ⋯ ϕ)
  (Λα e)          ⋯ ϕ = Λα (e ⋯ (ϕ ↑ _))
  (∀[α∶ k ] t)    ⋯ ϕ = ∀[α∶ (k ⋯ ϕ) ] (t ⋯ (ϕ ↑ _))
  (e • t)         ⋯ ϕ = (e ⋯ ϕ) • (t ⋯ ϕ)
  ★               ⋯ ϕ = ★

  opaque 
    {-# REWRITE id↑≡id id↑★≡id #-} 
    ⋯-id : ∀ {{K : Kit k}} (t : S ⊢ s) → t ⋯ id ≡ t
    ⋯-id (` x)           = `⋯-id x
    ⋯-id (λx e)          = cong λx_ (⋯-id e)
    ⋯-id (e₁ · e₂)       = cong₂ _·_ (⋯-id e₁) (⋯-id e₂)
    ⋯-id (t₁ ⇒ t₂)       = cong₂ _⇒_ (⋯-id t₁) (⋯-id t₂)
    ⋯-id (Λα t)          = cong Λα_ (⋯-id t)
    ⋯-id (∀[α∶ k ] t)    = cong₂ ∀[α∶_]_ (⋯-id k) (⋯-id t)
    ⋯-id (e • t)         = cong₂ _•_ (⋯-id e) (⋯-id t)
    ⋯-id ★               = refl

    ⋯-var : {{K : Kit k}} (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) →
        (` x) ⋯ ϕ ≡ x  `⋯ ϕ
    ⋯-var _ _ = refl 

  instance traversal = mkTraversal _⋯_ ⋯-id ⋯-var
  open Traversal traversal hiding (_⋯_; ⋯-id; ⋯-var) public

  opaque 
    {-# REWRITE dist–↑–; dist–↑★–; #-} 
    ⋯-compositionality :
      ∀ {{K₁ : Kit k₁}} {{K₂ : Kit k₂}} {{K₃ : Kit k₃}} {{C : ComposeKit K₁ K₂ K₃}} →
        (t : S₁ ⊢ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃) →
        (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
    ⋯-compositionality (` x)        ϕ₁ ϕ₂ = `⋯-compositionality x ϕ₁ ϕ₂
    ⋯-compositionality (λx e)       ϕ₁ ϕ₂ = cong λx_ (⋯-compositionality e (ϕ₁ ↑★ _) (ϕ₂ ↑★ _)) 
    ⋯-compositionality (e₁ · e₂)    ϕ₁ ϕ₂ = cong₂ _·_  (⋯-compositionality e₁ ϕ₁ ϕ₂) (⋯-compositionality e₂ ϕ₁ ϕ₂)
    ⋯-compositionality (t₁ ⇒ t₂)    ϕ₁ ϕ₂ = cong₂ _⇒_ (⋯-compositionality t₁ ϕ₁ ϕ₂) (⋯-compositionality t₂ ϕ₁ ϕ₂)  
    ⋯-compositionality (Λα t)       ϕ₁ ϕ₂ = cong Λα_ (⋯-compositionality t (ϕ₁ ↑ type) (ϕ₂ ↑ type))
    ⋯-compositionality (∀[α∶ k ] t) ϕ₁ ϕ₂ = cong₂ ∀[α∶_]_ (⋯-compositionality k ϕ₁ ϕ₂) (⋯-compositionality t (ϕ₁ ↑ type) (ϕ₂ ↑ type))
    ⋯-compositionality (e • t)      ϕ₁ ϕ₂ = cong₂ _•_ (⋯-compositionality e ϕ₁ ϕ₂) (⋯-compositionality t ϕ₁ ϕ₂)
    ⋯-compositionality ★            ϕ₁ ϕ₂ = refl

  instance opaque compose : Compose; compose = mkCompose ⋯-compositionality 
  open Compose compose hiding (⋯-compositionality) public 

opaque 
  unfolding lib  
  &/⋯–`  : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} {ϕ : S₁ –[ K ]→ S₂} → (`_ {s = s} x)  &/⋯ ϕ ≡ `/id (x &/⋯ ϕ)                   ; &/⋯–` = refl
  &/⋯–λ  : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} {ϕ : S₁ –[ K ]→ S₂} → (λx e)          &/⋯ ϕ ≡ λx (e &/⋯ (ϕ ↑ _))               ; &/⋯–λ = refl
  &/⋯–·  : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} {ϕ : S₁ –[ K ]→ S₂} → (e₁ · e₂)       &/⋯ ϕ ≡ (e₁ &/⋯ ϕ) · (e₂ &/⋯ ϕ)          ; &/⋯–· = refl
  &/⋯–⇒  : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} {ϕ : S₁ –[ K ]→ S₂} → (t₁ ⇒ t₂)       &/⋯ ϕ ≡ (t₁ &/⋯ ϕ) ⇒ (t₂ &/⋯ ϕ)          ; &/⋯–⇒ = refl
  &/⋯–Λ  : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} {ϕ : S₁ –[ K ]→ S₂} → (Λα e)          &/⋯ ϕ ≡ Λα (e &/⋯ (ϕ ↑ _))               ; &/⋯–Λ = refl
  &/⋯–•  : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} {ϕ : S₁ –[ K ]→ S₂} → (e • t)         &/⋯ ϕ ≡ (e &/⋯ ϕ) • (t &/⋯ ϕ)            ; &/⋯–• = refl 
  &/⋯–∀  : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} {ϕ : S₁ –[ K ]→ S₂} → (∀[α∶ ★ᴷ ] t)   &/⋯ ϕ ≡ ∀[α∶ ★ᴷ &/⋯ ϕ ] (t &/⋯ (ϕ ↑ _))  ; &/⋯–∀ = refl
  &/⋯–★  : {{K : Kit k}} {{C : ComposeKit K Kᴿ K}} {ϕ : S₁ –[ K ]→ S₂} → ★               &/⋯ ϕ ≡ ★                                ; &/⋯–★ = refl 

_&_ : {{K : Kit k}} → S₁ ∋ s → S₁ –[ K ]→ S₂ → S₂ ∋/⊢[ K ] s
_&_ = _&/⋯_ 

_⋯_ : {{K : Kit k}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
_⋯_ {{K}} = let instance _ = K , Kᴿ , K in _&/⋯_ 

{-# REWRITE 
  id`–def `id–def ;wk–def
  idˢ–def  compₗ–idˢ–def 
  wk–def   compₗ–wk–def 
  ext₀–def compₗ–ext₀–def 
  extₛ–def compₗ–extₛ–def
  comp–def–safe
  coincidenceₓ

  compₗ–id compᵣ–id
  associativity distributivity interact
  η–id η–law

  compositionality–safe right–id
  &/⋯–` &/⋯–λ &/⋯–· &/⋯–⇒ &/⋯–Λ &/⋯–• &/⋯–∀ &/⋯–★
  coincidenceₜ  
#-}