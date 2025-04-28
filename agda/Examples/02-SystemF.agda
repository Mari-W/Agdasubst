{-# OPTIONS --rewriting #-}
module Examples.02-SystemF where

open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open import Level
open import Data.Nat using (ℕ)
open import Data.Product.Base using (_,_; _×_; ∃-syntax; map₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional public using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Agda.Builtin.Equality.Rewrite

variable 
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' ℓ₁' ℓ₂' ℓ₃' : Level

postulate
  fun-ext : Extensionality ℓ₁ ℓ₂
    
dep-ext : {A : Set ℓ₁} {F G : (α : A) → Set ℓ₂} → ((α : A) → F α ≡ G α) → ((α : A) → F α) ≡ ((α : A) → G α) 
dep-ext = ∀-extensionality fun-ext _ _

Env = List Level

variable 
  Δ Δ₁ Δ₂ Δ₃ Δ₄ Δ' Δ₁' Δ₂' Δ₃' Δ₄' : Env

data Type (Δ : Env) : Level → Set where
  `_    : ℓ ∈ Δ → Type Δ ℓ
  _⇒_   : Type Δ ℓ → Type Δ ℓ' → Type Δ (ℓ ⊔ ℓ')
  ∀α_,_ : ∀ ℓ → Type (ℓ ∷ Δ) ℓ' → Type Δ (suc ℓ ⊔ ℓ')

variable
  T T₁ T₂ T₃ T₄ T' T₁' T₂' T₃' T₄' : Type Δ ℓ
  α α₁ α₂ α₃ α₄ α' α₁' α₂' α₃' α₄' : ℓ ∈ Δ

abstract 
  _T⇒ᵣ_ : Env → Env → Set
  Δ₁ T⇒ᵣ Δ₂ = ∀ ℓ → ℓ ∈ Δ₁ → ℓ ∈ Δ₂

  _T⍟ᵣ_ : Δ₁ T⇒ᵣ Δ₂ → ℓ ∈ Δ₁ → ℓ ∈ Δ₂ 
  ρ T⍟ᵣ α = ρ _ α

  Tidᵣ : Δ T⇒ᵣ Δ
  Tidᵣ _ α = α

  Twkᵣ : Δ T⇒ᵣ (ℓ ∷ Δ)
  Twkᵣ _ α = there α

  _T∷ᵣ_ : ℓ ∈ Δ₂ → Δ₁ T⇒ᵣ Δ₂ → (ℓ ∷ Δ₁) T⇒ᵣ Δ₂
  (α T∷ᵣ _) _ (here refl) = α
  (_ T∷ᵣ ρ) _ (there α)   = ρ _ α

  _T⨟ᵣᵣ_ : Δ₁ T⇒ᵣ Δ₂ → Δ₂ T⇒ᵣ Δ₃ → Δ₁ T⇒ᵣ Δ₃
  (ρ₁ T⨟ᵣᵣ ρ₂) _ α = ρ₂ _ (ρ₁ _ α)

_T⋯ᵣ_ : Type Δ₁ ℓ → Δ₁ T⇒ᵣ Δ₂ → Type Δ₂ ℓ
(` α)      T⋯ᵣ ρ = ` (ρ T⍟ᵣ α)
(T₁ ⇒ T₂)  T⋯ᵣ ρ = (T₁ T⋯ᵣ ρ) ⇒ (T₂ T⋯ᵣ ρ)
(∀α ℓ , T) T⋯ᵣ ρ = ∀α ℓ , (T T⋯ᵣ ((here refl) T∷ᵣ (ρ T⨟ᵣᵣ Twkᵣ)))

abstract
  _T⇒ₛ_ : Env → Env → Set
  Δ₁ T⇒ₛ Δ₂ = ∀ ℓ → ℓ ∈ Δ₁ → Type Δ₂ ℓ

  _T⍟ₛ_ : Δ₁ T⇒ₛ Δ₂ → ℓ ∈ Δ₁ → Type Δ₂ ℓ
  σ T⍟ₛ α = σ _ α

  Tidₛ : Δ T⇒ₛ Δ
  Tidₛ _ = `_

  _T∷ₛ_ : Type Δ₂ ℓ → Δ₁ T⇒ₛ Δ₂ → (ℓ ∷ Δ₁) T⇒ₛ Δ₂
  (T T∷ₛ _) _ (here refl) = T
  (_ T∷ₛ ρ) _ (there α) = ρ _ α

  _T⨟ᵣₛ_ : Δ₁ T⇒ᵣ Δ₂ → Δ₂ T⇒ₛ Δ₃ → Δ₁ T⇒ₛ Δ₃
  (ρ₁ T⨟ᵣₛ σ₂) _ α = σ₂ _ (ρ₁ _ α)

  _T⨟ₛᵣ_ : Δ₁ T⇒ₛ Δ₂ → Δ₂ T⇒ᵣ Δ₃ → Δ₁ T⇒ₛ Δ₃
  (σ₁ T⨟ₛᵣ ρ₂) _ α = (σ₁ _ α) T⋯ᵣ ρ₂

_T⋯ₛ_ : Type Δ₁ ℓ → Δ₁ T⇒ₛ Δ₂ → Type Δ₂ ℓ
(` α)      T⋯ₛ σ = (σ T⍟ₛ α)
(T₁ ⇒ T₂)  T⋯ₛ σ = (T₁ T⋯ₛ σ) ⇒ (T₂ T⋯ₛ σ)
(∀α ℓ , T) T⋯ₛ σ = ∀α ℓ , (T T⋯ₛ ((` (here refl)) T∷ₛ (σ T⨟ₛᵣ Twkᵣ)))

abstract
  _T⨟ₛₛ_ : Δ₁ T⇒ₛ Δ₂ → Δ₂ T⇒ₛ Δ₃ → Δ₁ T⇒ₛ Δ₃
  (σ₁ T⨟ₛₛ σ₂) _ α = (σ₁ _ α) T⋯ₛ σ₂

postulate
  -- Renaming Primitives
  T-⍟ᵣ-def₁            : (ρ : Δ₁ T⇒ᵣ Δ₂) → (α T∷ᵣ ρ) T⍟ᵣ (here refl) ≡ α
  T-⍟ᵣ-def₂            : (ρ : Δ₁ T⇒ᵣ Δ₂) → (α' T∷ᵣ ρ) T⍟ᵣ (there α) ≡ ρ T⍟ᵣ α

  T-idᵣ-def            : (α : ℓ ∈ Δ) → Tidᵣ T⍟ᵣ α ≡ α

  T-wkᵣ-def            : (α : ℓ ∈ Δ) → Twkᵣ {ℓ = ℓ'} T⍟ᵣ α ≡ there α


  T-∷ᵣ-def₁            : (α : ℓ ∈ Δ₂) (ρ : Δ₁ T⇒ᵣ Δ₂) → (α T∷ᵣ ρ) T⍟ᵣ (here refl) ≡ α
  T-∷ᵣ-def₂            : (α : ℓ ∈ Δ₂) (α' : ℓ' ∈ Δ₁) (ρ : Δ₁ T⇒ᵣ Δ₂) → (α T∷ᵣ ρ) T⍟ᵣ (there α') ≡ ρ T⍟ᵣ α'

  -- Substitution Primitives 
  T-⍟ₛ-def₁ : (σ : Δ₁ T⇒ₛ Δ₂) → (T T∷ₛ σ) T⍟ₛ (here refl) ≡ T
  T-⍟ₛ-def₂ : (σ : Δ₁ T⇒ₛ Δ₂) → (T T∷ₛ σ) T⍟ₛ (there α) ≡ σ T⍟ₛ α

  T-idₛ-def            : (α : ℓ ∈ Δ) → Tidₛ T⍟ₛ α ≡ ` α
  
  T-∷ₛ-def₁            : (T : Type Δ₂ ℓ) (σ : Δ₁ T⇒ₛ Δ₂) → (T T∷ₛ σ) T⍟ₛ (here refl) ≡ T
  T-∷ₛ-def₂            : (T : Type Δ₂ ℓ) (α : ℓ' ∈ Δ₁) (σ : Δ₁ T⇒ₛ Δ₂) → (T T∷ₛ σ) T⍟ₛ (there α) ≡ σ T⍟ₛ α


  -- Forward Composition Primitives
  T-⨟ᵣᵣ-def            : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (α : ℓ ∈ Δ₁) → (ρ₁ T⨟ᵣᵣ ρ₂) T⍟ᵣ α ≡ ρ₂ T⍟ᵣ (ρ₁ T⍟ᵣ α)
  T-⨟ᵣₛ-def            : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (α : ℓ ∈ Δ₁) → (ρ₁ T⨟ᵣₛ σ₂) T⍟ₛ α ≡ σ₂ T⍟ₛ (ρ₁ T⍟ᵣ α)
  T-⨟ₛᵣ-def            : (σ₁ : Δ₁ T⇒ₛ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (α : ℓ ∈ Δ₁) → (σ₁ T⨟ₛᵣ ρ₂) T⍟ₛ α ≡ (σ₁ T⍟ₛ α) T⋯ᵣ ρ₂
  T-⨟ₛₛ-def            : (σ₁ : Δ₁ T⇒ₛ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (α : ℓ ∈ Δ₁) → (σ₁ T⨟ₛₛ σ₂) T⍟ₛ α ≡ (σ₁ T⍟ₛ α) T⋯ₛ σ₂
  
  -- Identity Laws   
  T-left-idᵣᵣ          : (ρ : Δ₁ T⇒ᵣ Δ₂) → Tidᵣ T⨟ᵣᵣ ρ ≡ ρ 
  T-right-idᵣᵣ         : (ρ : Δ₁ T⇒ᵣ Δ₂) → ρ T⨟ᵣᵣ Tidᵣ ≡ ρ
  T-left-idᵣₛ          : (σ : Δ₁ T⇒ₛ Δ₂) → Tidᵣ T⨟ᵣₛ σ ≡ σ
  T-right-idᵣₛ         : (ρ : Δ₁ T⇒ᵣ Δ₂) → ρ T⨟ᵣₛ Tidₛ ≡ ρ T⨟ᵣₛ Tidₛ
  T-left-idₛᵣ          : (ρ : Δ₁ T⇒ᵣ Δ₂) → Tidₛ T⨟ₛᵣ ρ ≡ ρ T⨟ᵣₛ Tidₛ
  T-right-idₛᵣ         : (σ : Δ₁ T⇒ₛ Δ₂) → σ T⨟ₛᵣ Tidᵣ ≡ σ
  T-left-idₛₛ          : (σ : Δ₁ T⇒ₛ Δ₂) → Tidₛ T⨟ₛₛ σ ≡ σ   
  T-right-idₛₛ         : (σ : Δ₁ T⇒ₛ Δ₂) → σ T⨟ₛₛ Tidₛ ≡ σ 
  
  -- Associativity Laws 
  T-associativityᵣᵣᵣ   : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (ρ₃ : Δ₃ T⇒ᵣ Δ₄) → (ρ₁ T⨟ᵣᵣ ρ₂) T⨟ᵣᵣ ρ₃ ≡ ρ₁ T⨟ᵣᵣ (ρ₂ T⨟ᵣᵣ ρ₃)
  T-associativityᵣᵣₛ   : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (σ₃ : Δ₃ T⇒ₛ Δ₄) → (ρ₁ T⨟ᵣᵣ ρ₂) T⨟ᵣₛ σ₃ ≡ ρ₁ T⨟ᵣₛ (ρ₂ T⨟ᵣₛ σ₃)
  T-associativityᵣₛᵣ   : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (ρ₃ : Δ₃ T⇒ᵣ Δ₄) → (ρ₁ T⨟ᵣₛ σ₂) T⨟ₛᵣ ρ₃ ≡ ρ₁ T⨟ᵣₛ (σ₂ T⨟ₛᵣ ρ₃)
  T-associativityᵣₛₛ   : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (σ₃ : Δ₃ T⇒ₛ Δ₄) → (ρ₁ T⨟ᵣₛ σ₂) T⨟ₛₛ σ₃ ≡ ρ₁ T⨟ᵣₛ (σ₂ T⨟ₛₛ σ₃)
  T-associativityₛᵣᵣ   : (σ₁ : Δ₁ T⇒ₛ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (ρ₃ : Δ₃ T⇒ᵣ Δ₄) → (σ₁ T⨟ₛᵣ ρ₂) T⨟ₛᵣ ρ₃ ≡ σ₁ T⨟ₛᵣ (ρ₂ T⨟ᵣᵣ ρ₃)
  T-associativityₛᵣₛ   : (σ₁ : Δ₁ T⇒ₛ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (σ₃ : Δ₃ T⇒ₛ Δ₄) → (σ₁ T⨟ₛᵣ ρ₂) T⨟ₛₛ σ₃ ≡ σ₁ T⨟ₛₛ (ρ₂ T⨟ᵣₛ σ₃)
  T-associativityₛₛᵣ   : (σ₁ : Δ₁ T⇒ₛ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (ρ₃ : Δ₃ T⇒ᵣ Δ₄) → (σ₁ T⨟ₛₛ σ₂) T⨟ₛᵣ ρ₃ ≡ σ₁ T⨟ₛₛ (σ₂ T⨟ₛᵣ ρ₃)
  T-associativityₛₛₛ   : (σ₁ : Δ₁ T⇒ₛ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (σ₃ : Δ₃ T⇒ₛ Δ₄) → (σ₁ T⨟ₛₛ σ₂) T⨟ₛₛ σ₃ ≡ σ₁ T⨟ₛₛ (σ₂ T⨟ₛₛ σ₃)
  
  -- Eta Laws 
  T-η-idᵣ              : _T∷ᵣ_ {ℓ = ℓ} {Δ₁ = Δ₁} (here refl) Twkᵣ ≡ Tidᵣ  
  T-η-idₛ              : _T∷ₛ_ {ℓ = ℓ} {Δ₁ = Δ₁} (` here refl) (Twkᵣ T⨟ᵣₛ Tidₛ) ≡ Tidₛ 
  T-η-lawᵣ             : (ρ : (ℓ ∷ Δ₁) T⇒ᵣ Δ₂) → (ρ T⍟ᵣ (here refl)) T∷ᵣ (Twkᵣ T⨟ᵣᵣ ρ) ≡ ρ 
  T-η-lawₛ             : (σ : (ℓ ∷ Δ₁) T⇒ₛ Δ₂) → (σ T⍟ₛ (here refl)) T∷ₛ (Twkᵣ T⨟ᵣₛ σ) ≡ σ
  
  -- Interaction Laws
  T-interactᵣ          : (α : ℓ ∈ Δ₂) (ρ : Δ₁ T⇒ᵣ Δ₂) → Twkᵣ T⨟ᵣᵣ (α T∷ᵣ ρ) ≡ ρ 
  T-interactₛ          : (T : Type Δ₂ ℓ) (σ : Δ₁ T⇒ₛ Δ₂) → Twkᵣ T⨟ᵣₛ (T T∷ₛ σ) ≡ σ
     
  -- Distributivity Laws
  T-distributivityᵣᵣ   : (α : ℓ ∈ Δ₂) (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) → (α T∷ᵣ ρ₁) T⨟ᵣᵣ ρ₂ ≡ (ρ₂ T⍟ᵣ α) T∷ᵣ (ρ₁ T⨟ᵣᵣ ρ₂)  
  T-distributivityᵣₛ   : (α : ℓ ∈ Δ₂) (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) → (α T∷ᵣ ρ₁) T⨟ᵣₛ σ₂ ≡ (σ₂ T⍟ₛ α) T∷ₛ (ρ₁ T⨟ᵣₛ σ₂) 
  T-distributivityₛᵣ   : (T : Type Δ₂ ℓ) (σ₁ : Δ₁ T⇒ₛ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) → (T T∷ₛ σ₁) T⨟ₛᵣ ρ₂ ≡ (T T⋯ᵣ ρ₂) T∷ₛ (σ₁ T⨟ₛᵣ ρ₂) 
  T-distributivityₛₛ   : (T : Type Δ₂ ℓ) (σ₁ : Δ₁ T⇒ₛ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) → (T T∷ₛ σ₁) T⨟ₛₛ σ₂ ≡ (T T⋯ₛ σ₂) T∷ₛ (σ₁ T⨟ₛₛ σ₂)
  
  -- Identity Laws
  T-⋯idᵣ               : (T : Type Δ ℓ) → T T⋯ᵣ Tidᵣ ≡ T 
  T-⋯idₛ               : (T : Type Δ ℓ) → T T⋯ₛ Tidₛ ≡ T 
  
  -- Compositionality Laws
  T-compositionalityᵣᵣ : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (T : Type Δ₁ ℓ) → (T T⋯ᵣ ρ₁) T⋯ᵣ ρ₂ ≡ T T⋯ᵣ (ρ₁ T⨟ᵣᵣ ρ₂)
  T-compositionalityᵣₛ : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (T : Type Δ₁ ℓ) → (T T⋯ᵣ ρ₁) T⋯ₛ σ₂ ≡ T T⋯ₛ (ρ₁ T⨟ᵣₛ σ₂)
  T-compositionalityₛᵣ : (σ₁ : Δ₁ T⇒ₛ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (T : Type Δ₁ ℓ) → (T T⋯ₛ σ₁) T⋯ᵣ ρ₂ ≡ T T⋯ₛ (σ₁ T⨟ₛᵣ ρ₂)
  T-compositionalityₛₛ : (σ₁ : Δ₁ T⇒ₛ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (T : Type Δ₁ ℓ) → (T T⋯ₛ σ₁) T⋯ₛ σ₂ ≡ T T⋯ₛ (σ₁ T⨟ₛₛ σ₂)
      
  -- Coinicidence Law
  T-coincidence        : (ρ : Δ₁ T⇒ᵣ Δ₂) (T : Type Δ₁ ℓ) → T T⋯ₛ (ρ T⨟ᵣₛ Tidₛ) ≡ T T⋯ᵣ ρ

{-# REWRITE 
  T-⍟ᵣ-def₁ T-⍟ᵣ-def₂ T-idᵣ-def T-wkᵣ-def T-∷ᵣ-def₁ T-∷ᵣ-def₂ 
  T-⍟ₛ-def₁ T-⍟ₛ-def₂ T-idₛ-def T-∷ₛ-def₁ T-∷ₛ-def₂ 
  T-⨟ᵣᵣ-def T-⨟ᵣₛ-def T-⨟ₛᵣ-def T-⨟ₛₛ-def 

  T-left-idᵣᵣ T-right-idᵣᵣ T-left-idᵣₛ T-left-idₛᵣ T-right-idₛᵣ T-left-idₛₛ T-right-idₛₛ 
  T-interactᵣ T-interactₛ
  T-associativityᵣᵣᵣ T-associativityᵣᵣₛ T-associativityᵣₛᵣ T-associativityᵣₛₛ T-associativityₛᵣᵣ T-associativityₛᵣₛ  T-associativityₛₛᵣ T-associativityₛₛₛ
  T-η-idᵣ T-η-idₛ T-η-lawᵣ T-η-lawₛ
  T-distributivityᵣᵣ T-distributivityᵣₛ T-distributivityₛᵣ T-distributivityₛₛ
  T-⋯idᵣ T-⋯idₛ
  T-compositionalityᵣᵣ T-compositionalityᵣₛ T-compositionalityₛᵣ T-compositionalityₛₛ
  T-coincidence
#-}

_T↑ᵣ_ : Δ₁ T⇒ᵣ Δ₂ → (ℓ : Level) → (ℓ ∷ Δ₁) T⇒ᵣ (ℓ ∷ Δ₂)
ρ T↑ᵣ _ = (here refl) T∷ᵣ (ρ T⨟ᵣᵣ Twkᵣ)

Twk : Type Δ ℓ → Type (ℓ' ∷ Δ) ℓ
Twk T = T T⋯ᵣ Twkᵣ

_T↑ₛ_ : Δ₁ T⇒ₛ Δ₂ → (ℓ : Level) → (ℓ ∷ Δ₁) T⇒ₛ (ℓ ∷ Δ₂)
σ T↑ₛ _ = (` (here refl)) T∷ₛ (σ T⨟ₛᵣ Twkᵣ)

_T[_] : Type (ℓ' ∷ Δ) ℓ → Type Δ ℓ' → Type Δ ℓ
T T[ T' ] = T T⋯ₛ (T' T∷ₛ Tidₛ) 

variable
  ρ★ ρ★₁ ρ★₂ ρ★₃ ρ★₄ ρ★' ρ★₁' ρ★₂' ρ★₃' ρ★₄' : Δ₁ T⇒ᵣ Δ₂
  σ★ σ★₁ σ★₂ σ★₃ σ★₄ σ★' σ★₁' σ★₂' σ★₃' σ★₄' : Δ₁ T⇒ₛ Δ₂

data Ctx (Δ : Env) : Set where
  []   : Ctx Δ
  _∷_  : Type Δ ℓ → Ctx Δ → Ctx Δ          

_Γ⋯ᵣ_ : Ctx Δ₁ → (ρ : Δ₁ T⇒ᵣ Δ₂) → Ctx Δ₂
[]      Γ⋯ᵣ ρ = []
(T ∷ Γ) Γ⋯ᵣ ρ = T T⋯ᵣ ρ ∷ Γ Γ⋯ᵣ ρ
  
_Γ⋯ₛ_ : Ctx Δ₁ → (σ : Δ₁ T⇒ₛ Δ₂) → Ctx Δ₂
[]      Γ⋯ₛ σ = []
(T ∷ Γ) Γ⋯ₛ σ = T T⋯ₛ σ ∷ Γ Γ⋯ₛ σ

postulate
  Γ-⋯idᵣ : (Γ : Ctx Δ) → Γ Γ⋯ᵣ Tidᵣ ≡ Γ 
  Γ-⋯idₛ : (Γ : Ctx Δ) → Γ Γ⋯ₛ Tidₛ ≡ Γ 

  Γ-compositionalityᵣᵣ : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (Γ : Ctx Δ₁) → (Γ Γ⋯ᵣ ρ₁) Γ⋯ᵣ ρ₂ ≡ Γ Γ⋯ᵣ (ρ₁ T⨟ᵣᵣ ρ₂)
  Γ-compositionalityᵣₛ : (ρ₁ : Δ₁ T⇒ᵣ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (Γ : Ctx Δ₁) → (Γ Γ⋯ᵣ ρ₁) Γ⋯ₛ σ₂ ≡ Γ Γ⋯ₛ (ρ₁ T⨟ᵣₛ σ₂)
  Γ-compositionalityₛᵣ : (σ₁ : Δ₁ T⇒ₛ Δ₂) (ρ₂ : Δ₂ T⇒ᵣ Δ₃) (Γ : Ctx Δ₁) → (Γ Γ⋯ₛ σ₁) Γ⋯ᵣ ρ₂ ≡ Γ Γ⋯ₛ (σ₁ T⨟ₛᵣ ρ₂)
  Γ-compositionalityₛₛ : (σ₁ : Δ₁ T⇒ₛ Δ₂) (σ₂ : Δ₂ T⇒ₛ Δ₃) (Γ : Ctx Δ₁) → (Γ Γ⋯ₛ σ₁) Γ⋯ₛ σ₂ ≡ Γ Γ⋯ₛ (σ₁ T⨟ₛₛ σ₂)

  Γ-coincidence        : (ρ : Δ₁ T⇒ᵣ Δ₂) (Γ : Ctx Δ₁) → Γ Γ⋯ₛ (ρ T⨟ᵣₛ Tidₛ) ≡ Γ Γ⋯ᵣ ρ

{-# REWRITE 
  Γ-⋯idᵣ Γ-⋯idₛ 

  Γ-compositionalityᵣᵣ Γ-compositionalityᵣₛ Γ-compositionalityₛᵣ Γ-compositionalityₛₛ 
  Γ-coincidence
#-}

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ₄ Γ' Γ₁' Γ₂' Γ₃' Γ₄' : Ctx Δ

data _∊_ : Type Δ ℓ → Ctx Δ → Set where
  here   : T ∊ (T ∷ Γ)
  there  : T ∊ Γ → T ∊ (T' ∷ Γ)

_x⋯ᵣ_ : T ∊ Γ → (ρ★ : Δ₁ T⇒ᵣ Δ₂) → (T T⋯ᵣ ρ★) ∊ (Γ Γ⋯ᵣ ρ★)
here x⋯ᵣ ρ★ = here
there x x⋯ᵣ ρ★ = there (x x⋯ᵣ ρ★)

_x⋯ₛ_ : T ∊ Γ → (σ★ : Δ₁ T⇒ₛ Δ₂) → (T T⋯ₛ σ★) ∊ (Γ Γ⋯ₛ σ★)
here x⋯ₛ σ★ = here
there x x⋯ₛ σ★ = there (x x⋯ₛ σ★)

data Expr (Δ : Env) (Γ : Ctx Δ) : Type Δ ℓ → Set where
  `_    : T ∊ Γ → Expr Δ Γ T
  λx_   : Expr Δ (T₁ ∷ Γ) T₂ → Expr Δ Γ (T₁ ⇒ T₂) 
  Λα_,_ : (ℓ : Level) → {T : Type (ℓ ∷ Δ) ℓ'} → Expr (ℓ ∷ Δ) (Γ Γ⋯ᵣ Twkᵣ) T → Expr Δ Γ (∀α ℓ , T)
  _·_   : Expr Δ Γ (T₁ ⇒ T₂) → Expr Δ Γ T₁ → Expr Δ Γ T₂
  _∙_   : {T : Type (ℓ ∷ Δ) ℓ'} → Expr Δ Γ (∀α ℓ , T) → (T' : Type Δ ℓ) → Expr Δ Γ (T T[ T' ])

variable 
  x x₁ x₂ x₃ x₄ x' x₁' x₂' x₃' x₄' : T ∊ Γ
  e e₁ e₂ e₃ e₄ e' e₁' e₂' e₃' e₄' : Expr Δ Γ T 

abstract
  _E⇒ᵣ_ : Ctx Δ → Ctx Δ → Set
  _E⇒ᵣ_ {Δ = Δ} Γ₁ Γ₂ = ∀ ℓ (T : Type Δ ℓ) → T ∊ Γ₁ → T ∊ Γ₂

  _E⍟ᵣ_ : Γ₁ E⇒ᵣ Γ₂ → T ∊ Γ₁ → T ∊ Γ₂
  ρ E⍟ᵣ x = ρ _ _ x

  Eidᵣ : Γ E⇒ᵣ Γ
  Eidᵣ _ _ x = x 

  Ewkᵣ : Γ E⇒ᵣ (T ∷ Γ)
  Ewkᵣ _ _ = there

  _E∷ᵣ_ : T ∊ Γ₂ → Γ₁ E⇒ᵣ Γ₂ → (T ∷ Γ₁) E⇒ᵣ Γ₂
  (x E∷ᵣ _) _ _ here = x
  (_ E∷ᵣ ρ) _ _ (there x) = ρ _ _ x

  Edropᵣ : (T ∷ Γ₁) E⇒ᵣ Γ₂ → Γ₁ E⇒ᵣ Γ₂
  Edropᵣ ρ _ _ x = ρ _ _ (there x)

  _E⨟ᵣᵣ_ : Γ₁ E⇒ᵣ Γ₂ → Γ₂ E⇒ᵣ Γ₃ → Γ₁ E⇒ᵣ Γ₃
  (ρ₁ E⨟ᵣᵣ ρ₂) _ _ x = ρ₂ _ _ (ρ₁ _ _ x)

  _E⇒ᵣ⋯ᵣ_ : Γ₁ E⇒ᵣ Γ₂ → (ρ★ : Δ₁ T⇒ᵣ Δ₂) → (Γ₁ Γ⋯ᵣ ρ★) E⇒ᵣ (Γ₂ Γ⋯ᵣ ρ★)
  _E⇒ᵣ⋯ᵣ_ {Γ₁ = _ ∷ Γ₁} ρ ρ★ _ _ here = (ρ _ _ here) x⋯ᵣ ρ★
  _E⇒ᵣ⋯ᵣ_ {Γ₁ = _ ∷ Γ₁} ρ ρ★ _ _ (there x) = (Edropᵣ ρ E⇒ᵣ⋯ᵣ ρ★) _ _ x
  
_E⋯ᵣ_ : Expr Δ Γ₁ T → (ρ : Γ₁ E⇒ᵣ Γ₂) → Expr Δ Γ₂ T
(` x)      E⋯ᵣ ρ = ` (ρ E⍟ᵣ x)
(λx e)     E⋯ᵣ ρ = λx (e E⋯ᵣ (here E∷ᵣ (ρ E⨟ᵣᵣ Ewkᵣ)))
(Λα ℓ , e) E⋯ᵣ ρ = Λα ℓ , (e E⋯ᵣ (ρ E⇒ᵣ⋯ᵣ Twkᵣ))
(e₁ · e₂)  E⋯ᵣ ρ = (e₁ E⋯ᵣ ρ) · (e₂ E⋯ᵣ ρ)
(e ∙ T')   E⋯ᵣ ρ = (e E⋯ᵣ ρ) ∙ T'     

_ET⋯ᵣ_ : Expr Δ₁ Γ T → (ρ★ : Δ₁ T⇒ᵣ Δ₂) → Expr Δ₂ (Γ Γ⋯ᵣ ρ★) (T T⋯ᵣ ρ★)
(` x)      ET⋯ᵣ ρ★ = ` (x x⋯ᵣ ρ★)
(λx e)     ET⋯ᵣ ρ★ = λx (e ET⋯ᵣ ρ★)
(Λα ℓ , e) ET⋯ᵣ ρ★ = Λα ℓ , (e ET⋯ᵣ (ρ★ T↑ᵣ ℓ))
(e₁ · e₂)  ET⋯ᵣ ρ★ = (e₁ ET⋯ᵣ ρ★) · (e₂ ET⋯ᵣ ρ★)
(e ∙ T')   ET⋯ᵣ ρ★ = (e ET⋯ᵣ ρ★) ∙ (T' T⋯ᵣ ρ★)    

abstract
  _E⇒ₛ_ : Ctx Δ → Ctx Δ → Set
  _E⇒ₛ_ {Δ = Δ} Γ₁ Γ₂ = ∀ ℓ (T : Type Δ ℓ) → T ∊ Γ₁ → Expr Δ Γ₂ T

  _E⍟ₛ_ : Γ₁ E⇒ₛ Γ₂ → T ∊ Γ₁ → Expr Δ Γ₂ T
  σ E⍟ₛ x = σ _ _ x

  Eidₛ : Γ E⇒ₛ Γ
  Eidₛ _ _ = `_

  _E∷ₛ_ : Expr Δ Γ₂ T → Γ₁ E⇒ₛ Γ₂ → (T ∷ Γ₁) E⇒ₛ Γ₂
  (e E∷ₛ _) _ _ here = e
  (_ E∷ₛ σ) _ _ (there x) = σ _ _ x

  Edropₛ : (T ∷ Γ₁) E⇒ₛ Γ₂ → Γ₁ E⇒ₛ Γ₂
  Edropₛ σ _ _ x = σ _ _ (there x)

  _E⨟ᵣₛ_ : Γ₁ E⇒ᵣ Γ₂ → Γ₂ E⇒ₛ Γ₃ → Γ₁ E⇒ₛ Γ₃
  (ρ₁ E⨟ᵣₛ σ₂) _ _ x = σ₂ _ _ (ρ₁ _ _ x)

  _E⇒ᵣ⋯ₛ_ : Γ₁ E⇒ᵣ Γ₂ → (σ★ : Δ₁ T⇒ₛ Δ₂) → (Γ₁ Γ⋯ₛ σ★) E⇒ᵣ (Γ₂ Γ⋯ₛ σ★)
  _E⇒ᵣ⋯ₛ_ {Γ₁ = _ ∷ Γ₁} ρ σ★ _ _ here =  (ρ _ _ here) x⋯ₛ σ★
  _E⇒ᵣ⋯ₛ_ {Γ₁ = _ ∷ Γ₁} ρ σ★ _ _ (there x) = (Edropᵣ ρ E⇒ᵣ⋯ₛ σ★) _ _ x

  _E⨟ₛᵣ_ : Γ₁ E⇒ₛ Γ₂ → Γ₂ E⇒ᵣ Γ₃ → Γ₁ E⇒ₛ Γ₃
  (σ₁ E⨟ₛᵣ ρ₂) _ _ x = (σ₁ _ _ x) E⋯ᵣ ρ₂

  _E⇒ₛ⋯ᵣ_ : Γ₁ E⇒ₛ Γ₂ → (ρ★ : Δ₁ T⇒ᵣ Δ₂) → (Γ₁ Γ⋯ᵣ ρ★) E⇒ₛ (Γ₂ Γ⋯ᵣ ρ★)
  _E⇒ₛ⋯ᵣ_ {Γ₁ = _ ∷ Γ₁} σ ρ★ _ _ here = (σ _ _ here) ET⋯ᵣ ρ★
  _E⇒ₛ⋯ᵣ_ {Γ₁ = _ ∷ Γ₁} σ ρ★ _ _ (there x) = (Edropₛ σ E⇒ₛ⋯ᵣ ρ★) _ _ x
  
_E⋯ₛ_ : Expr Δ Γ₁ T → (σ : Γ₁ E⇒ₛ Γ₂) → Expr Δ Γ₂ T
(` x)      E⋯ₛ σ = (σ E⍟ₛ x)
(λx e)     E⋯ₛ σ = λx (e E⋯ₛ ((` here) E∷ₛ (σ E⨟ₛᵣ Ewkᵣ)))
(Λα ℓ , e) E⋯ₛ σ = Λα ℓ , (e E⋯ₛ (σ E⇒ₛ⋯ᵣ Twkᵣ))
(e₁ · e₂)  E⋯ₛ σ = (e₁ E⋯ₛ σ) · (e₂ E⋯ₛ σ)
(e ∙ T')   E⋯ₛ σ = (e E⋯ₛ σ) ∙ T'     

_ET⋯ₛ_ : Expr Δ₁ Γ T → (σ★ : Δ₁ T⇒ₛ Δ₂) → Expr Δ₂ (Γ Γ⋯ₛ σ★) (T T⋯ₛ σ★)
(` x)      ET⋯ₛ σ★ = ` (x x⋯ₛ σ★)
(λx e)     ET⋯ₛ σ★ = λx (e ET⋯ₛ σ★)
(Λα ℓ , e) ET⋯ₛ σ★ = Λα ℓ , (e ET⋯ₛ (σ★ T↑ₛ ℓ))
(e₁ · e₂)  ET⋯ₛ σ★ = (e₁ ET⋯ₛ σ★) · (e₂ ET⋯ₛ σ★)
(e ∙ T')   ET⋯ₛ σ★ = (e ET⋯ₛ σ★) ∙ (T' T⋯ₛ σ★)    

abstract 
  _E⨟ₛₛ_ : Γ₁ E⇒ₛ Γ₂ → Γ₂ E⇒ₛ Γ₃ → Γ₁ E⇒ₛ Γ₃
  (σ₁ E⨟ₛₛ σ₂) _ _ x = σ₁ _ _ x E⋯ₛ σ₂

  _E⇒ₛ⋯ₛ_ : Γ₁ E⇒ₛ Γ₂ → (σ★ : Δ₁ T⇒ₛ Δ₂) → (Γ₁ Γ⋯ₛ σ★) E⇒ₛ (Γ₂ Γ⋯ₛ σ★)
  _E⇒ₛ⋯ₛ_ {Γ₁ = _ ∷ Γ₁} σ σ★ _ _ here = (σ _ _ here) ET⋯ₛ σ★
  _E⇒ₛ⋯ₛ_ {Γ₁ = _ ∷ Γ₁} σ σ★ _ _ (there x) = (Edropₛ σ E⇒ₛ⋯ₛ σ★) _ _ x

postulate
  -- Renaming Primitives
  E-⍟ᵣ-def₁            : (ρ : Γ₁ E⇒ᵣ Γ₂) → (x E∷ᵣ ρ) E⍟ᵣ here ≡ x
  E-⍟ᵣ-def₂            : (ρ : Γ₁ E⇒ᵣ Γ₂) → (x' E∷ᵣ ρ) E⍟ᵣ (there x) ≡ ρ E⍟ᵣ x

  E-idᵣ-def            : (x : T ∊ Γ) → Eidᵣ E⍟ᵣ x ≡ x

  E-wkᵣ-def            : (x : T ∊ Γ) → Ewkᵣ {T = T'} E⍟ᵣ x ≡ there x

  E-∷ᵣ-def₁            : (x : T ∊ Γ₂) (ρ : Γ₁ E⇒ᵣ Γ₂) → (x E∷ᵣ ρ) E⍟ᵣ here ≡ x
  E-∷ᵣ-def₂            : (x : T ∊ Γ₂) (x' : T' ∊ Γ₁) (ρ : Γ₁ E⇒ᵣ Γ₂) → (x E∷ᵣ ρ) E⍟ᵣ (there x') ≡ ρ E⍟ᵣ x'
  
  E-dropᵣ-def          : (x : T ∊ Γ₁) (ρ : (T ∷ Γ₁) E⇒ᵣ Γ₂) → Edropᵣ ρ E⍟ᵣ x ≡ ρ E⍟ᵣ (there x)

  E-E⇒ᵣ⋯ᵣ-def₁         : (T : Type Δ₁ ℓ) (ρ : (T ∷ Γ₁) E⇒ᵣ Γ₂) (ρ★ : Δ₁ T⇒ᵣ Δ₂) → (ρ E⇒ᵣ⋯ᵣ ρ★) E⍟ᵣ here ≡ (ρ E⍟ᵣ here) x⋯ᵣ ρ★
  E-E⇒ᵣ⋯ᵣ-def₂         : (T : Type Δ₁ ℓ) (ρ : (T ∷ Γ₁) E⇒ᵣ Γ₂) (ρ★ : Δ₁ T⇒ᵣ Δ₂) (T' : Type Δ₂ ℓ') (x : T' ∊ (Γ₁ Γ⋯ᵣ ρ★)) → (ρ E⇒ᵣ⋯ᵣ ρ★) E⍟ᵣ (there x) ≡ (Edropᵣ ρ E⇒ᵣ⋯ᵣ ρ★) E⍟ᵣ x

  -- Substitution Primitives 
  E-⍟ₛ-def₁ : (σ : Γ₁ E⇒ₛ Γ₂) → (e E∷ₛ σ) E⍟ₛ here ≡ e
  E-⍟ₛ-def₂ : (σ : Γ₁ E⇒ₛ Γ₂) → (e E∷ₛ σ) E⍟ₛ (there x) ≡ σ E⍟ₛ x

  E-idₛ-def            : (x : T ∊ Γ) → Eidₛ E⍟ₛ x ≡ ` x
  
  E-∷ₛ-def₁            : (e : Expr Δ Γ₂ T) (σ : Γ₁ E⇒ₛ Γ₂) → (e E∷ₛ σ) E⍟ₛ here ≡ e
  E-∷ₛ-def₂            : (e : Expr Δ Γ₂ T) (x : T' ∊ Γ₁) (σ : Γ₁ E⇒ₛ Γ₂) → (e E∷ₛ σ) E⍟ₛ (there x) ≡ σ E⍟ₛ x

  E-dropₛ-def          : (x : T ∊ Γ₁) (σ : (T ∷ Γ₁) E⇒ₛ Γ₂) → Edropₛ σ E⍟ₛ x ≡ σ E⍟ₛ (there x)

  E-E⇒ₛ⋯ᵣ-def₁         : (T : Type Δ₁ ℓ) (σ : (T ∷ Γ₁) E⇒ₛ Γ₂) (ρ★ : Δ₁ T⇒ᵣ Δ₂) → (σ E⇒ₛ⋯ᵣ ρ★) E⍟ₛ here ≡ (σ E⍟ₛ here) ET⋯ᵣ ρ★
  E-E⇒ₛ⋯ᵣ-def₂         : (T : Type Δ₁ ℓ) (σ : (T ∷ Γ₁) E⇒ₛ Γ₂) (ρ★ : Δ₁ T⇒ᵣ Δ₂) (T' : Type Δ₂ ℓ') (x : T' ∊ (Γ₁ Γ⋯ᵣ ρ★)) → (σ E⇒ₛ⋯ᵣ ρ★) E⍟ₛ (there x) ≡ (Edropₛ σ E⇒ₛ⋯ᵣ ρ★) E⍟ₛ x

  -- Forward Composition Primitives
  E-⨟ᵣᵣ-def            : (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) (x : T ∊ Γ₁) → (ρ₁ E⨟ᵣᵣ ρ₂) E⍟ᵣ x ≡ ρ₂ E⍟ᵣ (ρ₁ E⍟ᵣ x)
  E-⨟ᵣₛ-def            : (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) (x : T ∊ Γ₁) → (ρ₁ E⨟ᵣₛ σ₂) E⍟ₛ x ≡ σ₂ E⍟ₛ (ρ₁ E⍟ᵣ x)
  E-⨟ₛᵣ-def            : (σ₁ : Γ₁ E⇒ₛ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) (x : T ∊ Γ₁) → (σ₁ E⨟ₛᵣ ρ₂) E⍟ₛ x ≡ (σ₁ E⍟ₛ x) E⋯ᵣ ρ₂
  E-⨟ₛₛ-def            : (σ₁ : Γ₁ E⇒ₛ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) (x : T ∊ Γ₁) → (σ₁ E⨟ₛₛ σ₂) E⍟ₛ x ≡ (σ₁ E⍟ₛ x) E⋯ₛ σ₂
  
  -- Identity Laws   
  E-left-idᵣᵣ          : (ρ : Γ₁ E⇒ᵣ Γ₂) → Eidᵣ E⨟ᵣᵣ ρ ≡ ρ 
  E-right-idᵣᵣ         : (ρ : Γ₁ E⇒ᵣ Γ₂) → ρ E⨟ᵣᵣ Eidᵣ ≡ ρ
  E-left-idᵣₛ          : (σ : Γ₁ E⇒ₛ Γ₂) → Eidᵣ E⨟ᵣₛ σ ≡ σ
  E-right-idᵣₛ         : (ρ : Γ₁ E⇒ᵣ Γ₂) → ρ E⨟ᵣₛ Eidₛ ≡ ρ E⨟ᵣₛ Eidₛ
  E-left-idₛᵣ          : (ρ : Γ₁ E⇒ᵣ Γ₂) → Eidₛ E⨟ₛᵣ ρ ≡ ρ E⨟ᵣₛ Eidₛ
  E-right-idₛᵣ         : (σ : Γ₁ E⇒ₛ Γ₂) → σ E⨟ₛᵣ Eidᵣ ≡ σ
  E-left-idₛₛ          : (σ : Γ₁ E⇒ₛ Γ₂) → Eidₛ E⨟ₛₛ σ ≡ σ   
  E-right-idₛₛ         : (σ : Γ₁ E⇒ₛ Γ₂) → σ E⨟ₛₛ Eidₛ ≡ σ 
  
  -- Associativity Laws 
  E-associativityᵣᵣᵣ   : (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) (ρ₃ : Γ₃ E⇒ᵣ Γ₄) → (ρ₁ E⨟ᵣᵣ ρ₂) E⨟ᵣᵣ ρ₃ ≡ ρ₁ E⨟ᵣᵣ (ρ₂ E⨟ᵣᵣ ρ₃)
  E-associativityᵣᵣₛ   : (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) (σ₃ : Γ₃ E⇒ₛ Γ₄) → (ρ₁ E⨟ᵣᵣ ρ₂) E⨟ᵣₛ σ₃ ≡ ρ₁ E⨟ᵣₛ (ρ₂ E⨟ᵣₛ σ₃)
  E-associativityᵣₛᵣ   : (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) (ρ₃ : Γ₃ E⇒ᵣ Γ₄) → (ρ₁ E⨟ᵣₛ σ₂) E⨟ₛᵣ ρ₃ ≡ ρ₁ E⨟ᵣₛ (σ₂ E⨟ₛᵣ ρ₃)
  E-associativityᵣₛₛ   : (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) (σ₃ : Γ₃ E⇒ₛ Γ₄) → (ρ₁ E⨟ᵣₛ σ₂) E⨟ₛₛ σ₃ ≡ ρ₁ E⨟ᵣₛ (σ₂ E⨟ₛₛ σ₃)
  E-associativityₛᵣᵣ   : (σ₁ : Γ₁ E⇒ₛ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) (ρ₃ : Γ₃ E⇒ᵣ Γ₄) → (σ₁ E⨟ₛᵣ ρ₂) E⨟ₛᵣ ρ₃ ≡ σ₁ E⨟ₛᵣ (ρ₂ E⨟ᵣᵣ ρ₃)
  E-associativityₛᵣₛ   : (σ₁ : Γ₁ E⇒ₛ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) (σ₃ : Γ₃ E⇒ₛ Γ₄) → (σ₁ E⨟ₛᵣ ρ₂) E⨟ₛₛ σ₃ ≡ σ₁ E⨟ₛₛ (ρ₂ E⨟ᵣₛ σ₃)
  E-associativityₛₛᵣ   : (σ₁ : Γ₁ E⇒ₛ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) (ρ₃ : Γ₃ E⇒ᵣ Γ₄) → (σ₁ E⨟ₛₛ σ₂) E⨟ₛᵣ ρ₃ ≡ σ₁ E⨟ₛₛ (σ₂ E⨟ₛᵣ ρ₃)
  E-associativityₛₛₛ   : (σ₁ : Γ₁ E⇒ₛ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) (σ₃ : Γ₃ E⇒ₛ Γ₄) → (σ₁ E⨟ₛₛ σ₂) E⨟ₛₛ σ₃ ≡ σ₁ E⨟ₛₛ (σ₂ E⨟ₛₛ σ₃)
  
  -- Eta Laws 
  E-η-idᵣ              : _E∷ᵣ_ {T = T} {Γ₁ = Γ₁} here Ewkᵣ ≡ Eidᵣ  
  E-η-idₛ              : _E∷ₛ_ {T = T} {Γ₁ = Γ₁} (` here) (Ewkᵣ E⨟ᵣₛ Eidₛ) ≡ Eidₛ 
  E-η-lawᵣ             : (ρ : (T ∷ Γ₁) E⇒ᵣ Γ₂) → (ρ E⍟ᵣ here) E∷ᵣ (Ewkᵣ E⨟ᵣᵣ ρ) ≡ ρ 
  E-η-lawₛ             : (σ : (T ∷ Γ₁) E⇒ₛ Γ₂) → (σ E⍟ₛ here) E∷ₛ (Ewkᵣ E⨟ᵣₛ σ) ≡ σ
  
  -- Interaction Laws
  E-interactᵣ          : (x : T ∊ Γ₂) (ρ : Γ₁ E⇒ᵣ Γ₂) → Ewkᵣ E⨟ᵣᵣ (x E∷ᵣ ρ) ≡ ρ 
  E-interactₛ          : (e : Expr Δ Γ₂ T) (σ : Γ₁ E⇒ₛ Γ₂) → Ewkᵣ E⨟ᵣₛ (e E∷ₛ σ) ≡ σ
     
  -- Distributivity Laws
  E-distributivityᵣᵣ   : (x : T ∊ Γ₂) (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) → (x E∷ᵣ ρ₁) E⨟ᵣᵣ ρ₂ ≡ (ρ₂ E⍟ᵣ x) E∷ᵣ (ρ₁ E⨟ᵣᵣ ρ₂)  
  E-distributivityᵣₛ   : (x : T ∊ Γ₂) (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) → (x E∷ᵣ ρ₁) E⨟ᵣₛ σ₂ ≡ (σ₂ E⍟ₛ x) E∷ₛ (ρ₁ E⨟ᵣₛ σ₂) 
  E-distributivityₛᵣ   : (e : Expr Δ Γ₂ T) (σ₁ : Γ₁ E⇒ₛ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) → (e E∷ₛ σ₁) E⨟ₛᵣ ρ₂ ≡ (e E⋯ᵣ ρ₂) E∷ₛ (σ₁ E⨟ₛᵣ ρ₂) 
  E-distributivityₛₛ   : (e : Expr Δ Γ₂ T) (σ₁ : Γ₁ E⇒ₛ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) → (e E∷ₛ σ₁) E⨟ₛₛ σ₂ ≡ (e E⋯ₛ σ₂) E∷ₛ (σ₁ E⨟ₛₛ σ₂)
  
  -- Identity Laws
  E-⋯Eidᵣ               : (e : Expr Δ Γ T) → e E⋯ᵣ Eidᵣ ≡ e 
  E-⋯Tidᵣ               : (e : Expr Δ Γ T) → e ET⋯ᵣ Tidᵣ ≡ e
  E-⋯Eidₛ               : (e : Expr Δ Γ T) → e E⋯ₛ Eidₛ ≡ e 
  E-⋯Tidₛ               : (e : Expr Δ Γ T) → e ET⋯ₛ Tidₛ ≡ e 
  
  -- Compositionality Laws
  E-compositionalityᵣᵣ : (e : Expr Δ Γ₁ T) (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) → (e E⋯ᵣ ρ₁) E⋯ᵣ ρ₂ ≡ e E⋯ᵣ (ρ₁ E⨟ᵣᵣ ρ₂)
  E-compositionalityᵣₛ : (e : Expr Δ Γ₁ T) (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) → (e E⋯ᵣ ρ₁) E⋯ₛ σ₂ ≡ e E⋯ₛ (ρ₁ E⨟ᵣₛ σ₂)
  E-compositionalityₛᵣ : (e : Expr Δ Γ₁ T) (σ₁ : Γ₁ E⇒ₛ Γ₂) (ρ₂ : Γ₂ E⇒ᵣ Γ₃) → (e E⋯ₛ σ₁) E⋯ᵣ ρ₂ ≡ e E⋯ₛ (σ₁ E⨟ₛᵣ ρ₂)
  E-compositionalityₛₛ : (e : Expr Δ Γ₁ T) (σ₁ : Γ₁ E⇒ₛ Γ₂) (σ₂ : Γ₂ E⇒ₛ Γ₃) → (e E⋯ₛ σ₁) E⋯ₛ σ₂ ≡ e E⋯ₛ (σ₁ E⨟ₛₛ σ₂)

  ET-compositionalityᵣᵣ : (e : Expr Δ₁ Γ₁ T) (ρ★₁ : Δ₁ T⇒ᵣ Δ₂) (ρ★₂ : Δ₂ T⇒ᵣ Δ₃) → (e ET⋯ᵣ ρ★₁) ET⋯ᵣ ρ★₂ ≡ e ET⋯ᵣ (ρ★₁ T⨟ᵣᵣ ρ★₂)
  ET-compositionalityᵣₛ : (e : Expr Δ₁ Γ₁ T) (ρ★₁ : Δ₁ T⇒ᵣ Δ₂) (σ★₂ : Δ₂ T⇒ₛ Δ₃) → (e ET⋯ᵣ ρ★₁) ET⋯ₛ σ★₂ ≡ e ET⋯ₛ (ρ★₁ T⨟ᵣₛ σ★₂)
  ET-compositionalityₛᵣ : (e : Expr Δ₁ Γ₁ T) (σ★₁ : Δ₁ T⇒ₛ Δ₂) (ρ★₂ : Δ₂ T⇒ᵣ Δ₃) → (e ET⋯ₛ σ★₁) ET⋯ᵣ ρ★₂ ≡ e ET⋯ₛ (σ★₁ T⨟ₛᵣ ρ★₂)
  ET-compositionalityₛₛ : (e : Expr Δ₁ Γ₁ T) (σ★₁ : Δ₁ T⇒ₛ Δ₂) (σ★₂ : Δ₂ T⇒ₛ Δ₃) → (e ET⋯ₛ σ★₁) ET⋯ₛ σ★₂ ≡ e ET⋯ₛ (σ★₁ T⨟ₛₛ σ★₂)

  -- Swap Laws (?)
  E-swapᵣᵣ : (e : Expr Δ₂ Γ₁ T) (ρ₁ : Γ₁ E⇒ᵣ Γ₂) (ρ★₂ : Δ₂ T⇒ᵣ Δ₃) → (e E⋯ᵣ ρ₁) ET⋯ᵣ ρ★₂ ≡ (e ET⋯ᵣ ρ★₂) E⋯ᵣ (ρ₁ E⇒ᵣ⋯ᵣ ρ★₂)
  -- .. 
      
  -- Coinicidence Law
  E-coincidence        : (ρ : Γ₁ E⇒ᵣ Γ₂) (e : Expr Δ Γ₁ T) → e E⋯ₛ (ρ E⨟ᵣₛ Eidₛ) ≡ e E⋯ᵣ ρ 
  ET-coincidence       : (ρ★ : Δ₁ T⇒ᵣ Δ₂) (e : Expr Δ₁ Γ T) → e ET⋯ₛ (ρ★ T⨟ᵣₛ Tidₛ) ≡ e ET⋯ᵣ ρ★ 
