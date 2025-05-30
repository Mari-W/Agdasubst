-- Author: Marius Weidner
module SigmaCalculus where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DeBruijn
open import Sorts
open import Kits 

record Rules : Set₁ where
  field
    Sort : SORT
  open SortsWithSort Sort
  open SortsMeta
  open KitsWithSort Sort

  field
    syn : Syntax
  open Syntax syn

  field 
    traversal : Traversal
  open Traversal traversal
  open KitsMeta

  field 
    compose : ComposeTraversal
  open ComposeTraversal compose

  opaque 
    unfolding all_kit_and_compose_definitions

    -- Kit Definitions 
    &-def₁ : ⦃ K : Kit _∋/⊢_ ⦄ (x/t : S₂ ∋/⊢ s) (ϕ : S₁ –[ K ]→ S₂) → zero & (x/t ∙ ϕ) ≡ x/t
    &-def₁ _ _ = refl

    &-def₂ : ⦃ K : Kit _∋/⊢_ ⦄ (x/t : S₂ ∋/⊢ s) (ϕ : S₁ –[ K ]→ S₂) → (suc x′) & (x/t ∙ ϕ) ≡ x′ & ϕ  
    &-def₂ _ _  = refl

    id-def : ⦃ K : Kit _∋/⊢_ ⦄ (x : S ∋ s) → x & (id ⦃ K ⦄) ≡ id/` x
    id-def _ = refl

    ∷-def₁ : ⦃ K : Kit _∋/⊢_ ⦄ (x/t : S₂ ∋/⊢ s) (ϕ : S₁ –[ K ]→ S₂) → zero & (x/t ∙ ϕ) ≡ x/t
    ∷-def₁ _ _ = refl

    ∷-def₂ : ⦃ K : Kit _∋/⊢_ ⦄ (x/t : S₂ ∋/⊢ s) (x' : S₁ ∋ s′) (ϕ : S₁ –[ K ]→ S₂) → suc x′ & (x/t ∙ ϕ) ≡ x′ & ϕ
    ∷-def₂ _ _ _ = refl

    wkᵣ-def : (x : S ∋ s) → x & (wkᵣ {s = s′}) ≡ suc x
    wkᵣ-def _ = refl 

    -- Forward Composition Primitves
    ⨟ᵣᵣ-def : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (x : S₁ ∋ s) → x & (ρ₁ ⨟ ρ₂) ≡ (x & ρ₁) & ρ₂
    ⨟ᵣᵣ-def _ _ _ = refl

    ⨟ᵣₛ-def : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (x : S₁ ∋ s) → x & (ρ₁ ⨟ σ₂) ≡ (x & ρ₁) & σ₂
    ⨟ᵣₛ-def _ _ _ = refl

    ⨟ₛᵣ-def : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (x : S₁ ∋ s) → x & (σ₁ ⨟ ρ₂) ≡ (x & σ₁) ⋯ ρ₂
    ⨟ₛᵣ-def _ _ _ = refl

    ⨟ₛₛ-def : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (x : S₁ ∋ s) → x & (σ₁ ⨟ σ₂) ≡ (x & σ₁) ⋯ σ₂
    ⨟ₛₛ-def _ _ _ = refl
    
    -- Interaction Laws
    interact : ⦃ K : Kit _∋/⊢_ ⦄ (x/t : S₂ ∋/⊢ s) (ϕ : S₁ –[ K ]→ S₂) → wkᵣ ⨟ (x/t ∙ ϕ) ≡ ϕ 
    interact _ _ = refl

    -- Sequence Eta Laws
    η-id : ⦃ K : Kit _∋/⊢_ ⦄ → _∙_ {s = s} {S₁ = S} (id/` zero) wkᵣ ≡ id 
    η-id = ~-ext λ { _ zero → refl
                    ; _ (suc x) → refl } 
                
    η-law : ⦃ K : Kit _∋/⊢_ ⦄ (ϕ : (s ∷ S₁) –[ K ]→ S₂) → (zero & ϕ) ∙ (wkᵣ ⨟ ϕ) ≡ ϕ
    η-law _ = ~-ext λ { _ zero → refl
                       ; _ (suc x) → refl } 

    -- Distributivity Laws
    distributivityᵣᵣ : (x : S₂ ∋ s) (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) → (x ∙ ρ₁) ⨟ ρ₂ ≡ (x & ρ₂) ∙ (ρ₁ ⨟ ρ₂)
    distributivityᵣᵣ _ _ _ = ~-ext λ { _ zero → refl
                                     ; _ (suc x) → refl } 
    distributivityᵣₛ : (x : S₂ ∋ s) (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) → (x ∙ ρ₁) ⨟ σ₂ ≡ (x & σ₂) ∙ (ρ₁ ⨟ σ₂)
    distributivityᵣₛ _ _ _ = ~-ext λ { _ zero → refl
                                     ; _ (suc x) → refl } 
    distributivityₛᵣ : (T : S₂ ⊢ s) (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) → (T ∙ σ₁) ⨟ ρ₂ ≡ (T ⋯ ρ₂) ∙ (σ₁ ⨟ ρ₂)
    distributivityₛᵣ _ _ _ = ~-ext λ { _ zero → refl
                                     ; _ (suc x) → refl } 
    distributivityₛₛ : (T : S₂ ⊢ s) (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) → (T ∙ σ₁) ⨟ σ₂ ≡ (T ⋯ σ₂) ∙ (σ₁ ⨟ σ₂)
    distributivityₛₛ _ _ _ = ~-ext λ { _ zero → refl
                                     ; _ (suc x) → refl }    

    -- Identity Application Laws
    -- needs to be derived for syntax 

    -- Identity Composition Laws  
    left-idᵣᵣ : (ρ : S₁ →ᵣ S₂) → idᵣ ⨟ ρ ≡ ρ 
    left-idᵣᵣ _ = refl

    right-idᵣᵣ : (ρ : S₁ →ᵣ S₂) → ρ ⨟ idᵣ ≡ ρ
    right-idᵣᵣ _ = refl

    left-idᵣₛ : (σ : S₁ →ₛ S₂) → idᵣ ⨟ σ ≡ σ
    left-idᵣₛ _ = refl

    left-idₛᵣ : (ρ : S₁ →ᵣ S₂) → idₛ ⨟ ρ ≡ ρ ⨟ idₛ
    left-idₛᵣ _ = ~-ext λ s x → ⋯-var _ _ 

    left-idₛₛ : (σ : S₁ →ₛ S₂) → idₛ ⨟ σ ≡ σ   
    left-idₛₛ _ = ~-ext λ s x → ⋯-var _ _ 

    right-idₛᵣ : (σ : S₁ →ₛ S₂) → σ ⨟ idᵣ ≡ σ
    right-idₛᵣ _ = ~-ext λ _ _ → ⋯-id _

    right-idₛₛ : (σ : S₁ →ₛ S₂) → σ ⨟ idₛ ≡ σ 
    right-idₛₛ _ = ~-ext λ _ _ → ⋯-id _

    -- Compositionality Laws
    -- needs to be derived for syntax 
 
    -- Associativity Laws 
    associativityᵣᵣᵣ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (ρ₃ : S₃ →ᵣ S₄) → (ρ₁ ⨟ ρ₂) ⨟ ρ₃ ≡ ρ₁ ⨟ (ρ₂ ⨟ ρ₃)
    associativityᵣᵣᵣ _ _ _ = refl

    associativityᵣᵣₛ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (σ₃ : S₃ →ₛ S₄) → (ρ₁ ⨟ ρ₂) ⨟ σ₃ ≡ ρ₁ ⨟ (ρ₂ ⨟ σ₃)
    associativityᵣᵣₛ _ _ _ = refl

    associativityᵣₛᵣ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (ρ₃ : S₃ →ᵣ S₄) → (ρ₁ ⨟ σ₂) ⨟ ρ₃ ≡ ρ₁ ⨟ (σ₂ ⨟ ρ₃)
    associativityᵣₛᵣ _ _ _ = refl

    associativityᵣₛₛ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (σ₃ : S₃ →ₛ S₄) → (ρ₁ ⨟ σ₂) ⨟ σ₃ ≡ ρ₁ ⨟ (σ₂ ⨟ σ₃)
    associativityᵣₛₛ _ _ _ = refl 

    associativityₛᵣᵣ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (ρ₃ : S₃ →ᵣ S₄) → (σ₁ ⨟ ρ₂) ⨟ ρ₃ ≡ σ₁ ⨟ (ρ₂ ⨟ ρ₃)
    associativityₛᵣᵣ _ _ _ =  ~-ext λ _ _ → ⋯-fusion _ _ _

    associativityₛᵣₛ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (σ₃ : S₃ →ₛ S₄) → (σ₁ ⨟ ρ₂) ⨟ σ₃ ≡ σ₁ ⨟ (ρ₂ ⨟ σ₃)
    associativityₛᵣₛ σ₁ _ _ = ~-ext λ _ x → ⋯-fusion (σ₁ _ x) _ _ 

    associativityₛₛᵣ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (ρ₃ : S₃ →ᵣ S₄) → (σ₁ ⨟ σ₂) ⨟ ρ₃ ≡ σ₁ ⨟ (σ₂ ⨟ ρ₃)
    associativityₛₛᵣ σ₁ _ _ = ~-ext λ _ x → ⋯-fusion (σ₁ _ x) _ _

    associativityₛₛₛ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (σ₃ : S₃ →ₛ S₄) → (σ₁ ⨟ σ₂) ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)
    associativityₛₛₛ σ₁ _ _ = ~-ext λ _ x → ⋯-fusion (σ₁ _ x) _ _