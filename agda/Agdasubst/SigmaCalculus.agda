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

    ↑ᵣ-def : (ρ : S₁ →ᵣ S₂) → ρ ↑ s ≡ zero ∙ (ρ ⨟ wkᵣ)
    ↑ᵣ-def _ = refl

    ↑ₛ-def : (σ : S₁ →ₛ S₂) → σ ↑ s ≡ (` zero) ∙ (σ ⨟ wkᵣ)
    ↑ₛ-def _ = refl

    -- Renaming Definitions
    -- &ᵣ-def₁ : (ρ : S₁ →ᵣ S₂) → zero &ᵣ (x ∷ᵣ ρ)  ≡ x
    -- &ᵣ-def₁ _ = refl

    -- &ᵣ-def₂ : (ρ : S₁ →ᵣ S₂) → (suc x′) &ᵣ (x ∷ᵣ ρ) ≡ x′ &ᵣ ρ 
    -- &ᵣ-def₂ _ = refl

    -- idᵣ-def : (x : S ∋ s) → x &ᵣ idᵣ ≡ x
    -- idᵣ-def _ = refl

    wkᵣ-def : (x : S ∋ s) → x & (wkᵣ {s = s′}) ≡ suc x
    wkᵣ-def _ = refl 

    -- ∷ᵣ-def₁ : (x : S₂ ∋ s) (ρ : S₁ →ᵣ S₂) → zero &ᵣ (x ∷ᵣ ρ)  ≡ x
    -- ∷ᵣ-def₁ _ _ = refl

    -- ∷ᵣ-def₂ : (x : S₂ ∋ s) (x' : S₁ ∋ s′) (ρ : S₁ →ᵣ S₂) → suc x′ &ᵣ (x ∷ᵣ ρ) ≡ x′ &ᵣ ρ
    -- ∷ᵣ-def₂ _ _ _ = refl

    -- ↑ᵣ-def : (ρ : S₁ →ᵣ S₂) → ρ ↑ᵣ s ≡ zero ∷ᵣ (ρ ⨟ᵣᵣ wkᵣ s)
    -- ↑ᵣ-def _ = refl

    -- Substitution Primitives
    -- &ₛ-def₁ : (σ : S₁ →ₛ S₂) → zero &ₛ (T ∷ₛ σ) ≡ T
    -- &ₛ-def₁ _ = refl

    -- &ₛ-def₂ : (σ : S₁ →ₛ S₂) → suc x &ₛ (T ∷ₛ σ)  ≡ x &ₛ σ 
    -- &ₛ-def₂ _ = refl

    -- idₛ-def : (x : S ∋ s) → x &ₛ idₛ ≡ ` x
    -- idₛ-def _ = refl

    -- ∷ₛ-def₁ : (T : S₂ ⊢ s) (σ : S₁ →ₛ S₂) → zero &ₛ (T ∷ₛ σ) ≡ T
    -- ∷ₛ-def₁ _ _ = refl

    -- ∷ₛ-def₂ : (T : S₂ ⊢ s) (x : S₁ ∋ s′) (σ : S₁ →ₛ S₂) → suc x &ₛ (T ∷ₛ σ) ≡ x &ₛ σ 
    -- ∷ₛ-def₂ _ _ _ = refl

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
    interactᵣ : (x : S₂ ∋ s) (ρ : S₁ →ᵣ S₂) → wkᵣ ⨟ (x ∙ ρ) ≡ ρ 
    interactᵣ _ _ = refl
    
    interactₛ : (T : S₂ ⊢ s) (σ : S₁ →ₛ S₂) → wkᵣ ⨟ (T ∙ σ) ≡ σ
    interactₛ _ _ = refl


    -- Sequence Eta Laws
    η-idᵣ : _∙_ {s = s} {S₁ = S} zero wkᵣ ≡ id 
    η-idᵣ = ~-ext λ { _ zero → refl
                    ; _ (suc x) → refl } 

    η-idₛ : _∙_ {s = s} {S₁ = S} (` zero) (wkᵣ ⨟ id) ≡ id
    η-idₛ = ~-ext λ { _ zero → refl
                    ; _ (suc x) → refl } 
                    
    η-lawᵣ : (ρ : (s ∷ S₁) →ᵣ S₂) → (zero & ρ) ∙ (wkᵣ ⨟ ρ) ≡ ρ
    η-lawᵣ _ = ~-ext λ { _ zero → refl
                       ; _ (suc x) → refl } 

    η-lawₛ : (σ : (s ∷ S₁) →ₛ S₂) → (zero & σ) ∙ (wkᵣ ⨟ σ) ≡ σ
    η-lawₛ _ = ~-ext λ { _ zero → refl
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
    -- ⋯id : ⦃ K : Kit _∋/⊢_ ⦄ (T : S ⊢ s) → T ⋯ id ⦃ K ⦄ ≡ T 
    -- ⋯id _ = ⋯-id _  

    -- ⋯idᵣ : (T : S ⊢ s) → T ⋯ᵣ idᵣ ≡ T 
    -- ⋯idᵣ _ = ⋯-id _ 

    -- ⋯idₛ : (T : S ⊢ s) → T ⋯ₛ idₛ ≡ T 
    -- ⋯idₛ _ = ⋯-id _

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
    -- compositionalityᵣᵣ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ T ⋯ᵣ (ρ₁ ⨟ᵣᵣ ρ₂)
    -- compositionalityᵣᵣ _ _ _ = ⋯-fusion _ _ _

    -- compositionalityᵣₛ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (ρ₁ ⨟ᵣₛ σ₂)
    -- compositionalityᵣₛ _ _ _ = ⋯-fusion _ _ _

    -- compositionalityₛᵣ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ T ⋯ₛ (σ₁ ⨟ₛᵣ ρ₂)
    -- compositionalityₛᵣ _ _ _ = ⋯-fusion _ _ _

    -- compositionalityₛₛ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₁ ⨟ₛₛ σ₂)
    -- compositionalityₛₛ _ _ _ = ⋯-fusion _ _ _
 
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