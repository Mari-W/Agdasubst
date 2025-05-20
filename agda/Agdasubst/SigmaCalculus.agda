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
    unfolding all_kit_and_instantiated_compose_definitions

    -- Renaming Definitions
    &ᵣ-def₁ : (ρ : S₁ →ᵣ S₂) → zero &ᵣ (x ∷ᵣ ρ)  ≡ x
    &ᵣ-def₁ _ = refl

    &ᵣ-def₂ : (ρ : S₁ →ᵣ S₂) → (suc x′) &ᵣ (x ∷ᵣ ρ) ≡ x′ &ᵣ ρ 
    &ᵣ-def₂ _ = refl

    idᵣ-def : (x : S ∋ s) → x &ᵣ idᵣ ≡ x
    idᵣ-def _ = refl

    wkᵣ-def : (x : S ∋ s) → x &ᵣ (wkᵣ s′) ≡ suc x
    wkᵣ-def _ = refl 

    ∷ᵣ-def₁ : (x : S₂ ∋ s) (ρ : S₁ →ᵣ S₂) → zero &ᵣ (x ∷ᵣ ρ)  ≡ x
    ∷ᵣ-def₁ _ _ = refl

    ∷ᵣ-def₂ : (x : S₂ ∋ s) (x' : S₁ ∋ s′) (ρ : S₁ →ᵣ S₂) → suc x′ &ᵣ (x ∷ᵣ ρ) ≡ x′ &ᵣ ρ
    ∷ᵣ-def₂ _ _ _ = refl

    ↑ᵣ-def : (ρ : S₁ →ᵣ S₂) → ρ ↑ᵣ s ≡ zero ∷ᵣ (ρ ⨟ᵣᵣ wkᵣ s)
    ↑ᵣ-def _ = refl

    -- Substitution Primitives
    &ₛ-def₁ : (σ : S₁ →ₛ S₂) → zero &ₛ (T ∷ₛ σ) ≡ T
    &ₛ-def₁ _ = refl

    &ₛ-def₂ : (σ : S₁ →ₛ S₂) → suc x &ₛ (T ∷ₛ σ)  ≡ x &ₛ σ 
    &ₛ-def₂ _ = refl

    idₛ-def : (x : S ∋ s) → x &ₛ idₛ ≡ ` x
    idₛ-def _ = refl

    ∷ₛ-def₁ : (T : S₂ ⊢ s) (σ : S₁ →ₛ S₂) → zero &ₛ (T ∷ₛ σ) ≡ T
    ∷ₛ-def₁ _ _ = refl

    ∷ₛ-def₂ : (T : S₂ ⊢ s) (x : S₁ ∋ s′) (σ : S₁ →ₛ S₂) → suc x &ₛ (T ∷ₛ σ) ≡ x &ₛ σ 
    ∷ₛ-def₂ _ _ _ = refl

    -- Forward Composition Primitves
    ⨟ᵣᵣ-def : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (x : S₁ ∋ s) → x &ᵣ (ρ₁ ⨟ᵣᵣ ρ₂) ≡ (x &ᵣ ρ₁) &ᵣ ρ₂
    ⨟ᵣᵣ-def _ _ _ = refl

    ⨟ᵣₛ-def : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (x : S₁ ∋ s) → x &ₛ (ρ₁ ⨟ᵣₛ σ₂) ≡ (x &ᵣ ρ₁) &ₛ σ₂
    ⨟ᵣₛ-def _ _ _ = refl

    ⨟ₛᵣ-def : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (x : S₁ ∋ s) → x &ₛ (σ₁ ⨟ₛᵣ ρ₂) ≡ (x &ₛ σ₁) ⋯ᵣ ρ₂
    ⨟ₛᵣ-def _ _ _ = refl

    ⨟ₛₛ-def : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (x : S₁ ∋ s) → x &ₛ (σ₁ ⨟ₛₛ σ₂) ≡ (x &ₛ σ₁) ⋯ₛ σ₂
    ⨟ₛₛ-def _ _ _ = refl
    
    -- Interaction Laws
    interactᵣ : (x : S₂ ∋ s) (ρ : S₁ →ᵣ S₂) → wkᵣ _ ⨟ᵣᵣ (x ∷ᵣ ρ) ≡ ρ 
    interactᵣ _ _ = refl
    
    interactₛ : (T : S₂ ⊢ s) (σ : S₁ →ₛ S₂) → wkᵣ _ ⨟ᵣₛ (T ∷ₛ σ) ≡ σ
    interactₛ _ _ = refl


    -- Sequence Eta Laws
    η-idᵣ : _∷ᵣ_ {s = s} {S₁ = S} zero (wkᵣ _) ≡ idᵣ 
    η-idᵣ = ~-ext λ { _ zero → refl
                    ; _ (suc x) → refl } 

    η-idₛ : _∷ₛ_ {s = s} {S₁ = S} (` zero) (wkᵣ _ ⨟ᵣₛ idₛ) ≡ idₛ
    η-idₛ = ~-ext λ { _ zero → refl
                    ; _ (suc x) → refl } 
                    
    η-lawᵣ : (ρ : (s ∷ S₁) →ᵣ S₂) → (zero &ᵣ ρ) ∷ᵣ (wkᵣ _ ⨟ᵣᵣ ρ) ≡ ρ
    η-lawᵣ _ = ~-ext λ { _ zero → refl
                       ; _ (suc x) → refl } 

    η-lawₛ : (σ : (s ∷ S₁) →ₛ S₂) → (zero &ₛ σ) ∷ₛ (wkᵣ _ ⨟ᵣₛ σ) ≡ σ
    η-lawₛ _ = ~-ext λ { _ zero → refl
                       ; _ (suc x) → refl } 

    -- Distributivity Laws
    distributivityᵣᵣ : (x : S₂ ∋ s) (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) → (x ∷ᵣ ρ₁) ⨟ᵣᵣ ρ₂ ≡ (x &ᵣ ρ₂) ∷ᵣ (ρ₁ ⨟ᵣᵣ ρ₂)
    distributivityᵣᵣ _ _ _ = ~-ext λ { _ zero → refl
                                     ; _ (suc x) → refl } 
    distributivityᵣₛ : (x : S₂ ∋ s) (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) → (x ∷ᵣ ρ₁) ⨟ᵣₛ σ₂ ≡ (x &ₛ σ₂) ∷ₛ (ρ₁ ⨟ᵣₛ σ₂)
    distributivityᵣₛ _ _ _ = ~-ext λ { _ zero → refl
                                     ; _ (suc x) → refl } 
    distributivityₛᵣ : (T : S₂ ⊢ s) (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) → (T ∷ₛ σ₁) ⨟ₛᵣ ρ₂ ≡ (T ⋯ᵣ ρ₂) ∷ₛ (σ₁ ⨟ₛᵣ ρ₂)
    distributivityₛᵣ _ _ _ = ~-ext λ { _ zero → refl
                                     ; _ (suc x) → refl } 
    distributivityₛₛ : (T : S₂ ⊢ s) (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) → (T ∷ₛ σ₁) ⨟ₛₛ σ₂ ≡ (T ⋯ₛ σ₂) ∷ₛ (σ₁ ⨟ₛₛ σ₂)
    distributivityₛₛ _ _ _ = ~-ext λ { _ zero → refl
                                     ; _ (suc x) → refl }    

    -- Identity Application Laws
    ⋯idᵣ : (T : S ⊢ s) → T ⋯ᵣ idᵣ ≡ T 
    ⋯idᵣ _ = ⋯-id _ 

    ⋯idₛ : (T : S ⊢ s) → T ⋯ₛ idₛ ≡ T 
    ⋯idₛ _ = ⋯-id _

    -- Identity Composition Laws  
    left-idᵣᵣ : (ρ : S₁ →ᵣ S₂) → idᵣ ⨟ᵣᵣ ρ ≡ ρ 
    left-idᵣᵣ _ = refl

    right-idᵣᵣ : (ρ : S₁ →ᵣ S₂) → ρ ⨟ᵣᵣ idᵣ ≡ ρ
    right-idᵣᵣ _ = refl

    left-idᵣₛ : (σ : S₁ →ₛ S₂) → idᵣ ⨟ᵣₛ σ ≡ σ
    left-idᵣₛ _ = refl

    left-idₛᵣ : (ρ : S₁ →ᵣ S₂) → idₛ ⨟ₛᵣ ρ ≡ ρ ⨟ᵣₛ idₛ
    left-idₛᵣ _ = ~-ext λ s x → ⋯-var _ _ 

    left-idₛₛ : (σ : S₁ →ₛ S₂) → idₛ ⨟ₛₛ σ ≡ σ   
    left-idₛₛ _ = ~-ext λ s x → ⋯-var _ _ 

    right-idₛᵣ : (σ : S₁ →ₛ S₂) → σ ⨟ₛᵣ idᵣ ≡ σ
    right-idₛᵣ _ = ~-ext λ _ _ → ⋯idᵣ _

    right-idₛₛ : (σ : S₁ →ₛ S₂) → σ ⨟ₛₛ idₛ ≡ σ 
    right-idₛₛ _ = ~-ext λ _ _ → ⋯idₛ _

    -- Compositionality Laws
    compositionalityᵣᵣ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ T ⋯ᵣ (ρ₁ ⨟ᵣᵣ ρ₂)
    compositionalityᵣᵣ _ _ _ = ⋯-fusion _ _ _

    compositionalityᵣₛ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (ρ₁ ⨟ᵣₛ σ₂)
    compositionalityᵣₛ _ _ _ = ⋯-fusion _ _ _

    compositionalityₛᵣ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ T ⋯ₛ (σ₁ ⨟ₛᵣ ρ₂)
    compositionalityₛᵣ _ _ _ = ⋯-fusion _ _ _

    compositionalityₛₛ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₁ ⨟ₛₛ σ₂)
    compositionalityₛₛ _ _ _ = ⋯-fusion _ _ _

    -- Associativity Laws 
    associativityᵣᵣᵣ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (ρ₃ : S₃ →ᵣ S₄) → (ρ₁ ⨟ᵣᵣ ρ₂) ⨟ᵣᵣ ρ₃ ≡ ρ₁ ⨟ᵣᵣ (ρ₂ ⨟ᵣᵣ ρ₃)
    associativityᵣᵣᵣ _ _ _ = refl

    associativityᵣᵣₛ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (σ₃ : S₃ →ₛ S₄) → (ρ₁ ⨟ᵣᵣ ρ₂) ⨟ᵣₛ σ₃ ≡ ρ₁ ⨟ᵣₛ (ρ₂ ⨟ᵣₛ σ₃)
    associativityᵣᵣₛ _ _ _ = refl

    associativityᵣₛᵣ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (ρ₃ : S₃ →ᵣ S₄) → (ρ₁ ⨟ᵣₛ σ₂) ⨟ₛᵣ ρ₃ ≡ ρ₁ ⨟ᵣₛ (σ₂ ⨟ₛᵣ ρ₃)
    associativityᵣₛᵣ _ _ _ = refl

    associativityᵣₛₛ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (σ₃ : S₃ →ₛ S₄) → (ρ₁ ⨟ᵣₛ σ₂) ⨟ₛₛ σ₃ ≡ ρ₁ ⨟ᵣₛ (σ₂ ⨟ₛₛ σ₃)
    associativityᵣₛₛ _ _ _ = refl 

    associativityₛᵣᵣ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (ρ₃ : S₃ →ᵣ S₄) → (σ₁ ⨟ₛᵣ ρ₂) ⨟ₛᵣ ρ₃ ≡ σ₁ ⨟ₛᵣ (ρ₂ ⨟ᵣᵣ ρ₃)
    associativityₛᵣᵣ _ _ _ =  ~-ext λ _ _ → compositionalityᵣᵣ _ _ _

    associativityₛᵣₛ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (σ₃ : S₃ →ₛ S₄) → (σ₁ ⨟ₛᵣ ρ₂) ⨟ₛₛ σ₃ ≡ σ₁ ⨟ₛₛ (ρ₂ ⨟ᵣₛ σ₃)
    associativityₛᵣₛ σ₁ _ _ = ~-ext λ _ x → compositionalityᵣₛ _ _ (σ₁ _ x)

    associativityₛₛᵣ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (ρ₃ : S₃ →ᵣ S₄) → (σ₁ ⨟ₛₛ σ₂) ⨟ₛᵣ ρ₃ ≡ σ₁ ⨟ₛₛ (σ₂ ⨟ₛᵣ ρ₃)
    associativityₛₛᵣ σ₁ _ _ = ~-ext λ _ x → compositionalityₛᵣ _ _ (σ₁ _ x)

    associativityₛₛₛ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (σ₃ : S₃ →ₛ S₄) → (σ₁ ⨟ₛₛ σ₂) ⨟ₛₛ σ₃ ≡ σ₁ ⨟ₛₛ (σ₂ ⨟ₛₛ σ₃)
    associativityₛₛₛ σ₁ _ _ = ~-ext λ _ x → compositionalityₛₛ _ _ (σ₁ _ x) 