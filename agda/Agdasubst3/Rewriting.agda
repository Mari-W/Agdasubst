
{-# OPTIONS --rewriting #-}
module Rewriting where

open import Agda.Builtin.Equality.Rewrite

open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong-app; subst; module ≡-Reasoning)

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

      -- Axiom
      `_-is-`var : ∀ (x : S ∋ s) → _≃_.to iso (Syntax.`_ syn x) ≡ `var x

    open Syntax syn hiding (_⊢_; `_) public
    open Syntax syn using (_⊢_; `_)

    open Substitution desc using () renaming 
      ( Kit to Kit∙
      ; _→ₖ_ to _→ₖ∙_
      ; _↑ₖ_ to _↑ₖ∙_
      ; _↑ₖ*_ to _↑ₖ*∙_
      ; idₖ to idₖ∙
      ; _–[_]→_ to _–[_]→∙_
      ; _⋯_ to _⋯∙_ 
      ; ⋯-var to ⋯∙-var
      ; ⋯-id to ⋯∙-id
      ; syn to syn∙
      )

    open _≃_ iso

    open KitIso (record {syn₁ = syn; syn₂ = syn∙; iso = iso; `_-is-`var = `_-is-`var})

    foo : ∀ (_∋/⊢_ : List (Sort Var) → Sort Var → Set) (K : Syntax.Kit syn₁ _∋/⊢_) → 
             Syntax.Kit._→ₖ_ K S₁ S₂ ≡ Syntax.Kit._→ₖ_ (to-Kit K) S₁ S₂
    foo {S₁ = S₁} {S₂ = S₂} _ K  = {!   refl  !}
      
    -- _⋯_ : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
    -- _⋯_ {S₁ = S₁} {S₂ = S₂} {{K}} t ϕ = from (_⋯∙_ {{K = to-Kit K}} (to t) (to∙ ϕ))

    -- opaque 
    --   unfolding KIT 
    --   ⋯-var : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) → 
    --           (` x) ⋯ ϕ ≡ `/id {{K}} (x &ₖ ϕ)
    --   ⋯-var {{K}} x ϕ rewrite `_-is-`var x = from∘to _         
-- 
    --   ⋯-id : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → 
    --         (t : S ⊢ s) →  t ⋯ idₖ {{K}} ≡ t
    --   ⋯-id {{K}} t = swap-to-from (⋯∙-id {{to-Kit∙ K}} (to t))
-- 
    -- traversal : Traversal
    -- traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var ; ⋯-id = ⋯-id }
-- 
    -- open Traversal traversal hiding (_⋯_; ⋯-var; ⋯-id) public

     