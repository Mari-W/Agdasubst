-- Author(s): Hannes Saffrich (2024) and Marius Weidner (2025)
module Agdasubst.Examples.SystemFSub.Definitions.Syntax where

open import Agdasubst.Prelude public

open import Relation.Binary.PropositionalEquality using (refl)

data Sort : SORT where
  expr : Sort Bind 
  type : Sort Bind
  cstr : Sort Bind
  kind : Sort NoBind
  cind : Sort NoBind 

open WithSort Sort public 
open Meta public

data _⊢_ : SCOPED where
  `_        : S ∋ s → S ⊢ s     
  λx_       : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_       : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α⊑_]_   : S ⊢ type → (type ∷ S) ⊢ type → S ⊢ type
  _·_       : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_       : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_       : S ⊢ type → S ⊢ type → S ⊢ type
  `tt       : S ⊢ expr
  𝟙         : S ⊢ type
  _∶⊑_      : S ⊢ type → S ⊢ type → S ⊢ cind 
  ★         : S ⊢ kind
  sat       : S ⊢ cstr 
  ✰         : S ⊢ kind

variable
  e e₁ e₂ e₃ e₄ e′ e₁′ e₂′ e₃′ e₄′ : S ⊢ expr
  t t₁ t₂ t₃ t₄ t′ t₁′ t₂′ t₃′ t₄′ : S ⊢ type
  c c₁ c₂ c₃ c₄ c′ c₁′ c₂′ c₃′tc₄′ : S ⊢ cstr
  ★ₖ ★ₖ′                           : S ⊢ kind

instance syn = mkSyntax _⊢_  `_  λ { refl → refl }
open Syntax syn hiding (_⊢_; `_) public