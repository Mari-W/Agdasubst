-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemFSub.Injectivity where

open import Agdasubst.Examples.SystemFSub.Definitions.Syntax
open import Agdasubst.Examples.SystemFSub.Definitions.Typing
open import Agdasubst.Examples.SystemFSub.Definitions.Semantics
open import Agdasubst.Examples.SystemFSub.Substitution

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Function using () renaming (_∋_ to _by_)

variable 
  t₁₁ t₁₂ t₂₁ t₂₂ : S ⊢ type
  e₁₁ e₁₂ e₂₁ e₂₂ : S ⊢ expr 

Injective-Map : ∀ {{K : Kit k}} → S₁ –[ K ]→ S₂ → Set
Injective-Map ϕ = ∀ s (x x′ : _ ∋ s) → x & ϕ ≡ x′ & ϕ → x ≡ x′

suc-injective : suc {s′ = s′} x ≡ suc x′ → x ≡ x′ 
suc-injective refl = refl 

wk-injective : Injective-Map (wk {S = S} {s = s′})
wk-injective _ _ _ refl = refl

↑-injective : ∀ {ρ : S₁ →ᴿ S₂} →
  Injective-Map ρ →
  Injective-Map (ρ ↑ s)
↑-injective inj-ρ s zero    zero     eq = refl
↑-injective inj-ρ s zero  (suc x′)   ()
↑-injective inj-ρ s (suc x) zero     ()  
↑-injective inj-ρ s (suc x) (suc x′) eq = cong suc (inj-ρ s x x′ (suc-injective eq))

λx-injective : ∀ {e₁ e₂ : (expr ∷ S) ⊢ expr} → (S ⊢ expr by λx e₁) ≡ λx e₂ → e₁ ≡ e₂
λx-injective refl = refl 

Λα-injective : ∀ {e₁ e₂ : (type ∷ S) ⊢ expr} → (S ⊢ expr by Λα e₁) ≡ Λα e₂ → e₁ ≡ e₂
Λα-injective refl = refl 

∀α-injective : ∀[α⊑ t₁₁ ] t₁₂ ≡ ∀[α⊑ t₂₁ ] t₂₂ → t₁₁ ≡ t₂₁ × t₁₂ ≡ t₂₂
∀α-injective refl = refl , refl

·-injective : e₁₁ · e₁₂ ≡ e₂₁ · e₂₂ → e₁₁ ≡ e₂₁ × e₁₂ ≡ e₂₂
·-injective refl = refl , refl

•-injective : e₁₁ • t₁₂ ≡ e₂₁ • t₂₂ → e₁₁ ≡ e₂₁ × t₁₂ ≡ t₂₂
•-injective refl = refl , refl

⇒-injective : t₁₁ ⇒ t₁₂ ≡ t₂₁ ⇒ t₂₂ → t₁₁ ≡ t₂₁ × t₁₂ ≡ t₂₂
⇒-injective refl = refl , refl

∶⊑-injective : t₁₁ ∶⊑ t₁₂ ≡ t₂₁ ∶⊑ t₂₂ → t₁₁ ≡ t₂₁ × t₁₂ ≡ t₂₂
∶⊑-injective refl = refl , refl

⋯-injective : ∀ {ρ : S₁ →ᴿ S₂} →
  Injective-Map ρ → 
  ∀ (t₁ t₂ : S₁ ⊢ s) →
  t₁ ⋯ ρ ≡ t₂ ⋯ ρ →
  t₁ ≡ t₂ 
⋯-injective inj-ρ (` x₁) (` x₂) eq = cong `_ (inj-ρ _ x₁ x₂ (`-injective eq)) 
⋯-injective {ρ = ρ} inj-ρ (λx e₁)          (λx e₂)          eq = cong λx_ (⋯-injective (↑-injective {ρ = ρ} inj-ρ) e₁ e₂ (λx-injective eq))
⋯-injective {ρ = ρ} inj-ρ (Λα e₁)          (Λα e₂)          eq = cong Λα_ (⋯-injective (↑-injective {ρ = ρ} inj-ρ) e₁ e₂ (Λα-injective eq))
⋯-injective {ρ = ρ} inj-ρ (∀[α⊑ t₁₁ ] t₁₂) (∀[α⊑ t₂₁ ] t₂₂) eq = cong₂ ∀[α⊑_]_
                                                                     (⋯-injective inj-ρ t₁₁ t₂₁ (proj₁ (∀α-injective eq)))
                                                                     (⋯-injective (↑-injective {ρ = ρ} inj-ρ) t₁₂ t₂₂ (proj₂ (∀α-injective eq)))
⋯-injective inj-ρ (e₁₁ · e₁₂)              (e₂₁ · e₂₂)      eq = cong₂ _·_ 
                                                                     (⋯-injective inj-ρ e₁₁ e₂₁ (proj₁ (·-injective eq)))
                                                                     (⋯-injective inj-ρ e₁₂ e₂₂ (proj₂ (·-injective eq)))
⋯-injective inj-ρ (e₁₁ • t₁₂)              (e₂₁ • t₂₂)      eq = cong₂ _•_ 
                                                                     (⋯-injective inj-ρ e₁₁ e₂₁ (proj₁ (•-injective eq)))
                                                                     (⋯-injective inj-ρ t₁₂ t₂₂ (proj₂ (•-injective eq)))
⋯-injective inj-ρ (t₁₁ ⇒ t₁₂)              (t₂₁ ⇒ t₂₂)      eq = cong₂ _⇒_ 
                                                                     (⋯-injective inj-ρ t₁₁ t₂₁ (proj₁ (⇒-injective eq)))
                                                                     (⋯-injective inj-ρ t₁₂ t₂₂ (proj₂ (⇒-injective eq)))
⋯-injective inj-ρ `tt                      `tt              eq = refl
⋯-injective inj-ρ `⊤                       `⊤               eq = refl
⋯-injective inj-ρ (t₁₁ ∶⊑ t₁₂)             (t₂₁ ∶⊑ t₂₂)     eq = cong₂ _∶⊑_ 
                                                                     (⋯-injective inj-ρ t₁₁ t₂₁ (proj₁ (∶⊑-injective eq)))
                                                                     (⋯-injective inj-ρ t₁₂ t₂₂ (proj₂ (∶⊑-injective eq)))
⋯-injective inj-ρ ★                        ★                eq = refl
⋯-injective inj-ρ sat                      sat              eq = refl
⋯-injective inj-ρ ✰                        ✰                eq = refl  
-- Agda does NOT apply rewrite rules to automatically refute cases
-- based on obvious inequalites sometimes
⋯-injective inj-ρ (` x₁) (λx t₂) ()
⋯-injective inj-ρ (` x₁) (Λα t₂) ()
⋯-injective inj-ρ (` x₁) (∀[α⊑ t₂ ] t₃) ()
⋯-injective inj-ρ (` x₁) (t₂ · t₃) ()
⋯-injective inj-ρ (` x₁) (t₂ • t₃) ()
⋯-injective inj-ρ (` x₁) (t₂ ⇒ t₃) ()
⋯-injective inj-ρ (` x₁) `tt ()
⋯-injective inj-ρ (` x₁) `⊤ ()
⋯-injective inj-ρ (` x₁) (t₂ ∶⊑ t₃) ()
⋯-injective inj-ρ (` x₁) ★ ()
⋯-injective inj-ρ (` x₁) sat ()
⋯-injective inj-ρ (` x₁) ✰ ()
⋯-injective inj-ρ (λx t₁) (` x₂) ()
⋯-injective inj-ρ (λx t₁) (Λα t₂) ()
⋯-injective inj-ρ (λx t₁) (t₂ · t₃) ()
⋯-injective inj-ρ (λx t₁) (t₂ • t₃) ()
⋯-injective inj-ρ (λx t₁) `tt ()
⋯-injective inj-ρ (Λα t₁) (` x₂) ()
⋯-injective inj-ρ (Λα t₁) (λx t₂) ()
⋯-injective inj-ρ (Λα t₁) (t₂ · t₃) ()
⋯-injective inj-ρ (Λα t₁) (t₂ • t₃) ()
⋯-injective inj-ρ (Λα t₁) `tt ()
⋯-injective inj-ρ (∀[α⊑ t₁ ] t₂) (` x₂) ()
⋯-injective inj-ρ (∀[α⊑ t₁ ] t₂) (t₃ ⇒ t₄) ()
⋯-injective inj-ρ (∀[α⊑ t₁ ] t₂) `⊤ ()
⋯-injective inj-ρ (t₁ · t₂) (` x₂) ()
⋯-injective inj-ρ (t₁ · t₂) (λx t₃) () 
⋯-injective inj-ρ (t₁ · t₂) (Λα t₃) ()
⋯-injective inj-ρ (t₁ · t₂) (t₃ • t₄) ()
⋯-injective inj-ρ (t₁ · t₂) `tt ()
⋯-injective inj-ρ (t₁ • t₂) (` x₂) ()
⋯-injective inj-ρ (t₁ • t₂) (λx t₃) ()
⋯-injective inj-ρ (t₁ • t₂) (Λα t₃) ()
⋯-injective inj-ρ (t₁ • t₂) (t₃ · t₄) ()
⋯-injective inj-ρ (t₁ • t₂) `tt ()
⋯-injective inj-ρ (t₁ ⇒ t₂) (` x₂) ()
⋯-injective inj-ρ (t₁ ⇒ t₂) (∀[α⊑ t₃ ] t₄) ()
⋯-injective inj-ρ (t₁ ⇒ t₂) `⊤ ()
⋯-injective inj-ρ `tt (` x₂) ()
⋯-injective inj-ρ `tt (λx t₂) ()
⋯-injective inj-ρ `tt (Λα t₂) ()
⋯-injective inj-ρ `tt (t₂ · t₃) ()
⋯-injective inj-ρ `tt (t₂ • t₃) ()
⋯-injective inj-ρ `⊤ (` x₂) ()
⋯-injective inj-ρ `⊤ (∀[α⊑ t₂ ] t₃) ()
⋯-injective inj-ρ `⊤ (t₂ ⇒ t₃) ()
⋯-injective inj-ρ (t₁ ∶⊑ t₂) (` x₂) ()
⋯-injective inj-ρ ★ (` x₂) ()
⋯-injective inj-ρ ★ ✰ ()
⋯-injective inj-ρ sat (` x₂) ()
⋯-injective inj-ρ ✰ (` x₂) ()
⋯-injective inj-ρ ✰ ★ () 