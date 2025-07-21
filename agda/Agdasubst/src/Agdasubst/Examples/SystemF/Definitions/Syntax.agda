-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Examples.SystemF.Definitions.Syntax where

open import Agdasubst.Prelude public

open import Relation.Binary.PropositionalEquality using (refl)

data Sort : ModeIndexed where
  expr : Sort Bind 
  type : Sort Bind
  kind : Sort NoBind

open WithSort Sort public 
open Meta public

--! E >
data _⊢_ : Scoped where
  `_      : S ∋ s → S ⊢ s     
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
  ★ᴷ ★ᴷ′                           : S ⊢ kind

instance syn = mkSyntax _⊢_  `_  λ { refl → refl }
open Syntax syn hiding (_⊢_; `_) public