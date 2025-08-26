-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemF.Definitions.Typing where

open import Agdasubst.Extensions.StandardTyping public 

open import Agdasubst.Examples.SystemF.Definitions.Syntax
open import Agdasubst.Examples.SystemF.Substitution

instance types = mkTypes λ { expr → type ; type → kind ; kind →  kind }

open Types types public
open TypesMeta public

--! Typing
data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {Γ : Ctx S} {x : S ∋ s} {t : S ∶⊢ s} →
    Γ ∋ x ∶ t → 
    -------------
    Γ ⊢ (` x) ∶ t
  ⊢λ : 
    (t ∷ₜ Γ) ⊢ e ∶ weaken t′ → 
    --------------------------
    Γ ⊢ (λx e) ∶ (t ⇒ t′) 
  ⊢Λ :
    (★ᴷ ∷ₜ Γ) ⊢ e ∶ t → 
    --------------------------
    Γ ⊢ (Λα e) ∶ (∀[α∶ ★ᴷ ] t)
  ⊢· : 
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    --------------------
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢• : 
    Γ ⊢ e ∶ (∀[α∶ ★ᴷ ] t′) →
    Γ ⊢ t ∶ ★ᴷ →
    (★ᴷ ∷ₜ Γ) ⊢ t′ ∶ ★ᴷ′ →
    ------------------------
    Γ ⊢ (e • t) ∶ (t′ [ t ])
  ⊢★ : 
    ---------
    Γ ⊢ t ∶ ★

instance typing = mkTyping _⊢_∶_ ⊢` 
open Typing typing hiding (_⊢_∶_; ⊢`) renaming (⊢⦅_⦆ to ⊢[]) public