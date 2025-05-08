
{-# OPTIONS --rewriting #-}
module Rewriting where

open import Agda.Builtin.Equality.Rewrite

open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong-app; module ≡-Reasoning)

open import Variables
open import Sorts using (module Sorted)
open import Generics using (module Generic)
open import Isomorphism using (module Iso) 
open import Substitution as _

module Rewrite (Sort : Mode → Set) where

  open Sorted Sort
  open Meta
  
  open Generic Sort
  open Iso Sort
  open Sub Sort
  
  record σ-Calculus : Set₁ where
    field
      syn : Syntax
      desc : Desc
      iso : Syntax._⊢_ syn ≃ (Tm desc)

      `var-is-`_ : {!  _≃_ !}

    open Syntax syn

    open import Level renaming (zero to lzero)
    module _ (T : Set) where
      bad : Setω
      bad = {! (λ (ℓ : T → Level) → ∀ t → Set (ℓ t)) (λ _ → lzero)    !}
    
    open Substitution desc renaming 
      ( Kit to Kit∙
      ; _→ₖ_ to _→ₖ∙_
      ; _–[_]→_ to _–[_]→∙_
      )

    open _≃_ iso

    to∙Kit : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} →  Kit _∋/⊢_ → Kit∙ _∋/⊢_
    to∙Kit record 
      { id/` = id/`
      ; `/id = `/id
      ; wk = wk
      ; `/`-is-` = `/`-is-`
      ; id/`-injective = id/`-injective 
      ; `/id-injective = `/id-injective 
      ; wk-id/` = wk-id/` 
      } = record 
      { id/` = id/`
      ; `/id = λ x → to ( `/id x)
      ; wk = wk
      ; `/`-is-` = λ x → {! cong to (`/`-is-` x)   !}
      }

    to∙ : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → S₁ –[ K ]→ S₂ → S₁ –[ {! K  !} ]→∙ S₂ 
    to∙ = {!   !}
    
    open _≃_ iso

    -- _⋯ₖ_ : ∀ {{K : Kit _∋/⊢_}} → S₁ ⊢ s → S₁ →ₖ S₂ → S₂ ⊢ s
    -- t ⋯ₖ ϕ = {! from ((to t) ⋯ ϕ)  !}
    
    -- ⋯ᵣ-id : {!   !}
  

  

  
 