-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
module Agdasubst.Examples.SystemF.Definitions.Typing where

open import Agdasubst.Extensions.StandardTyping public 

open import Agdasubst.Examples.SystemF.Definitions.Syntax
open import Agdasubst.Examples.SystemF.Substitution
open import Data.Product using (_,_)

instance types = mkTypes λ { expr → _ , type ; type → _ , kind ; kind → _ , kind } 
open Types types public

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
 
instance typing = mkTyping _⊢_∶_ ⊢` 
open Typing typing hiding (_⊢_∶_; ⊢`) public