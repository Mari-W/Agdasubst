-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemFSub.Definitions.Typing where

open import Agdasubst.Extensions.StandardTyping public 

open import Agdasubst.Examples.SystemFSub.Definitions.Syntax
open import Agdasubst.Examples.SystemFSub.Substitution
open import Data.Product using (_,_)

instance types = mkTypes λ { expr → type ; type → kind ; cstr → cind ; cind → kind ; kind → kind } 
open Types types public 

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ′ Γ₁′ Γ₂′ Γ₃′ : Ctx S

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set
data _⊢_⊑_ : Ctx S → S ⊢ s → S ⊢ s → Set

data _⊢_⊑_ where
  ⊑-` : 
    Γ ⊢ t₁ ⊑ t₂ →
    Γ ⊢ c ∶ (t₂ ∶⊑ t₃) →
    Γ ⊢ t₃ ⊑ t₄ →
    Γ ⊢ t₁ ⊑ t₄
  ⊑-`⊤ :
    Γ ⊢ t ⊑ `⊤
  ⊑-⇒ :
    Γ ⊢ t₁′ ⊑ t₁ →
    Γ ⊢ t₂  ⊑ t₂′ →
    Γ ⊢ (t₁ ⇒ t₂) ⊑ (t₁′ ⇒ t₂′)
  ⊑-∀ : {Γ : Ctx S} →
    (★ ∷ₜ Γ) ⊢ t₂ ⊑ t₂′ →
    Γ ⊢ (∀[α⊑ t₁ ] t₂) ⊑ (∀[α⊑ t₁ ] t₂′)
  ⊑-refl-var : 
    Γ ⊢ (` x) ⊑ (` x)

⊑-refl : Γ ⊢ t ⊑ t
⊑-refl {S} {Γ} {` x}          = ⊑-refl-var
⊑-refl {S} {Γ} {∀[α⊑ t₁ ] t₂} = ⊑-∀ ⊑-refl
⊑-refl {S} {Γ} {t₁ ⇒ t₂}      = ⊑-⇒ ⊑-refl ⊑-refl
⊑-refl {S} {Γ} {`⊤}            = ⊑-`⊤

⊑-trans :
  Γ ⊢ t₁ ⊑ t₂ →
  Γ ⊢ t₂ ⊑ t₃ →
  Γ ⊢ t₁ ⊑ t₃
⊑-trans (⊑-` t₁⊑t₂ y t₁⊑t₃) t₂⊑t₃                   = ⊑-` t₁⊑t₂ y (⊑-trans t₁⊑t₃ t₂⊑t₃)
⊑-trans (⊑-⇒ t₁′⊑t₁ t₂⊑t₂′) (⊑-⇒ t₁′′⊑t₁′ t₂′⊑t₂′′) = ⊑-⇒ (⊑-trans t₁′′⊑t₁′ t₁′⊑t₁) (⊑-trans t₂⊑t₂′ t₂′⊑t₂′′)
⊑-trans (⊑-∀ t₁⊑t₂)         (⊑-∀ t₂⊑t₃)             = ⊑-∀ (⊑-trans t₁⊑t₂ t₂⊑t₃)
⊑-trans ⊑-refl-var          t₂⊑t₃                   = t₂⊑t₃
⊑-trans t₁⊑t₂               ⊑-`⊤                     = ⊑-`⊤
⊑-trans t₁⊑t₂               (⊑-` t₂⊑t₃ y t₄⊑t₅)     = ⊑-` (⊑-trans t₁⊑t₂ t₂⊑t₃) y t₄⊑t₅

data _⊢_∶_ where
  ⊢` : ∀ {x : S ∋ s} {t : S ∶⊢ s} →
    Γ ∋ x ∶ t →
    Γ ⊢ ` x ∶ t
  ⊢λ : ∀ {e : (expr ∷ S) ⊢ expr} →
    (t₁ ∷ₜ Γ) ⊢ e ∶ weaken t₂ →
    Γ ⊢ (λx e) ∶ (t₁ ⇒ t₂)
  ⊢Λ : {Γ : Ctx S} →
    (((` zero) ∶⊑ (weaken t₁)) ∷ₜ (★ ∷ₜ Γ)) ⊢ (weaken {s′ = cstr} e) ∶ (weaken t₂) →
    Γ ⊢ (Λα e) ∶ (∀[α⊑ t₁ ] t₂)
  ⊢· :
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ → 
    Γ ⊢ (e₁ · e₂) ∶ t₂ 
  ⊢• : {Γ : Ctx S} →
    ( ((`_ zero) ∶⊑ (weaken t)) ∷ₜ (★ ∷ₜ Γ)) ⊢ (weaken {s′ = cstr} t₁) ∶ ★ →
    Γ ⊢ t₂ ∶ ★ →
    Γ ⊢ t₂ ⊑ t →
    Γ ⊢ e₁ ∶ (∀[α⊑ t ] t₁) →
    Γ ⊢ (e₁ • t₂) ∶ (t₁ [ t₂ ])
  ⊢tt :
    Γ ⊢ `tt ∶ `⊤
  ⊢★ :
    Γ ⊢ t ∶ ★
  ⊢cstr :
    Γ ⊢ t₁ ⊑ t₂ →
    Γ ⊢ sat ∶ (t₁ ∶⊑ t₂)
  ⊢⊑ :
    Γ ⊢ e ∶ t₁ →
    Γ ⊢ t₁ ⊑ t₂ →
    Γ ⊢ e ∶ t₂

instance typing = mkTyping _⊢_∶_ ⊢` 
open Typing typing hiding (_⊢_∶_; ⊢`) public 