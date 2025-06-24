{-# OPTIONS --rewriting #-}
module Examples.01-SystemF where

-- Imports ---------------------------------------------------------------------

open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; trans; sym; module ≡-Reasoning)
open ≡-Reasoning
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; ∃-syntax; proj₂)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookupWith)
open import Data.List.Membership.Propositional public using (_∈_)

open import Agda.Builtin.Equality.Rewrite

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

-- Sorts -----------------------------------------------------------------------

data SortTy : Set where
  Var : SortTy
  NoVar : SortTy

data Sort : SortTy → Set where 
  expr : Sort Var
  type : Sort Var 
  kind : Sort NoVar

variable
  st st₁ st₂ st₃ st₄ st' st₁' st₂' st₃' st₄' : SortTy
  s s₁ s₂ s₃ s₄ s' s₁' s₂' s₃' s₄' : Sort st
  S S₁ S₂ S₃ S₄ S' S₁' S₂' S₃' S₄' : List (Sort Var)
  
-- Syntax ----------------------------------------------------------------------

data _⊢_ : List (Sort Var) → Sort st → Set where
  `_       : s ∈ S → S ⊢ s    
  λx_     : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_     : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_ : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_     : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _∙_     : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_     : S ⊢ type → S ⊢ type → S ⊢ type
  ★       : S ⊢ kind

variable
  x x₁ x₂ x₃ x₄ x' x₁' x₂' x₃' x₄' : s ∈ S
  e e₁ e₂ e₃ e₄ e' e₁' e₂' e₃' e₄' : S ⊢ expr
  t t₁ t₂ t₃ t₄ t' t₁' t₂' t₃' t₄' : S ⊢ type
  k k₁ k₂ k₃ k₄ k' k₁' k₂' k₃' k₄' : S ⊢ kind

-- Substitution ----------------------------------------------------------------

opaque
  _→ᵣ_ : List (Sort Var) → List (Sort Var) → Set
  S₁ →ᵣ S₂ = ∀ s → s ∈ S₁ → s ∈ S₂ 

  _⍟ᵣ_ : (ρ : S₁ →ᵣ S₂) → s ∈ S₁ → s ∈ S₂
  ρ ⍟ᵣ x = ρ _ x
  
  idᵣ : S →ᵣ S
  idᵣ _ x = x 

  wkᵣ : S →ᵣ (s ∷ S)
  wkᵣ _ x = there x

  _∷ᵣ_ : s ∈ S₂ → S₁ →ᵣ S₂ → (s ∷ S₁) →ᵣ S₂
  (x ∷ᵣ _) _ (here refl) = x
  (_ ∷ᵣ ρ) _ (there x) = ρ _ x

  _；ᵣᵣ_ : S₁ →ᵣ S₂ → S₂ →ᵣ S₃ → S₁ →ᵣ S₃
  (ρ₁ ；ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_↑ₖᵣ_ : S₁ →ᵣ S₂ → (s : Sort Var) → (s ∷ S₁) →ᵣ (s ∷ S₂)
ρ ↑ₖᵣ _ = here refl ∷ᵣ (ρ ；ᵣᵣ wkᵣ)
  
_⋯ᵣ_ : S₁ ⊢ s → S₁ →ᵣ S₂ → S₂ ⊢ s
(` x)         ⋯ᵣ ρ = ` (ρ ⍟ᵣ x)
(λx e)        ⋯ᵣ ρ = λx (e ⋯ᵣ (ρ ↑ₖᵣ _))
(Λα e)        ⋯ᵣ ρ = Λα (e ⋯ᵣ (ρ ↑ₖᵣ _))
(∀[α∶ k ] t)  ⋯ᵣ ρ = ∀[α∶ k ⋯ᵣ ρ ] (t ⋯ᵣ (ρ ↑ₖᵣ _))
(e₁ · e₂)     ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
(e ∙ t)       ⋯ᵣ ρ = (e ⋯ᵣ ρ) ∙ (t ⋯ᵣ ρ)
(t₁ ⇒ t₂)     ⋯ᵣ ρ = (t₁ ⋯ᵣ ρ) ⇒ (t₂ ⋯ᵣ ρ)
★             ⋯ᵣ ρ = ★ 

wk : S ⊢ s → (s' ∷ S) ⊢ s
wk T = T ⋯ᵣ wkᵣ

opaque
  unfolding _→ᵣ_ _⍟ᵣ_ idᵣ wkᵣ _∷ᵣ_ _；ᵣᵣ_

  _→ₛ_ : List (Sort Var) → List (Sort Var) → Set
  S₁ →ₛ S₂ = ∀ s → s ∈ S₁ → S₂ ⊢ s

  _⍟ₛ_ : (σ : S₁ →ₛ S₂) → s ∈ S₁ → S₂ ⊢ s
  σ ⍟ₛ x = σ _ x

  idₛ : S →ₛ S
  idₛ _ = `_

  _∷ₛ_ : S₂ ⊢ s → S₁ →ₛ S₂ → (s ∷ S₁) →ₛ S₂
  (t ∷ₛ _) _ (here refl) = t
  (_ ∷ₛ σ) _ (there x) = σ _ x
  
  _；ᵣₛ_ : S₁ →ᵣ S₂ → S₂ →ₛ S₃ → S₁ →ₛ S₃
  (ρ₁ ；ᵣₛ σ₂) _ x = σ₂ _ (ρ₁ _ x)

  _；ₛᵣ_ : S₁ →ₛ S₂ → S₂ →ᵣ S₃ → S₁ →ₛ S₃
  (σ₁ ；ₛᵣ ρ₂) _ x = (σ₁ _ x) ⋯ᵣ ρ₂

_↑ₖₛ_ : S₁ →ₛ S₂ → (s : Sort Var) → (s ∷ S₁) →ₛ (s ∷ S₂)
(σ ↑ₖₛ _) = (` (here refl)) ∷ₛ (σ ；ₛᵣ wkᵣ)

_⋯ₛ_ : S₁ ⊢ s → S₁ →ₛ S₂ → S₂ ⊢ s
(` x)         ⋯ₛ σ = (σ ⍟ₛ x)
(λx e)        ⋯ₛ σ = λx (e ⋯ₛ (σ ↑ₖₛ _))
(Λα e)        ⋯ₛ σ = Λα (e ⋯ₛ (σ ↑ₖₛ _))
(∀[α∶ k ] t)  ⋯ₛ σ = ∀[α∶ k ⋯ₛ σ ] (t ⋯ₛ (σ ↑ₖₛ _))
(e₁ · e₂)     ⋯ₛ σ = (e₁ ⋯ₛ σ) · (e₂ ⋯ₛ σ)
(e ∙ t)       ⋯ₛ σ = (e ⋯ₛ σ) ∙ (t ⋯ₛ σ)
(t₁ ⇒ t₂)     ⋯ₛ σ = (t₁ ⋯ₛ σ) ⇒ (t₂ ⋯ₛ σ)
★             ⋯ₛ σ = ★ 

_[_] : (s' ∷ S) ⊢ s → S ⊢ s' → S ⊢ s
T [ T' ] = T ⋯ₛ (T' ∷ₛ idₛ) 


opaque
  unfolding _→ᵣ_ _⍟ᵣ_ idᵣ wkᵣ _∷ᵣ_ _；ᵣᵣ_ _→ₛ_ _⍟ₛ_ idₛ _∷ₛ_ _；ᵣₛ_ _；ₛᵣ_

  _；ₛₛ_ :  S₁ →ₛ S₂ → S₂ →ₛ S₃ → S₁ →ₛ S₃
  (σ₁ ；ₛₛ σ₂) _ x = (σ₁ _ x) ⋯ₛ σ₂

opaque
  unfolding _→ᵣ_ _⍟ᵣ_ idᵣ wkᵣ _∷ᵣ_ _；ᵣᵣ_ _→ₛ_ _⍟ₛ_ idₛ _∷ₛ_ _；ᵣₛ_ _；ₛᵣ_ _；ₛₛ_
  
  -- Renaming Primitives
  ⍟ᵣ-def₁ : (ρ : S₁ →ᵣ S₂) → (x ∷ᵣ ρ) ⍟ᵣ (here refl) ≡ x
  ⍟ᵣ-def₁ _ = refl

  ⍟ᵣ-def₂ : (ρ : S₁ →ᵣ S₂) → (x ∷ᵣ ρ) ⍟ᵣ (there x') ≡ ρ ⍟ᵣ x'
  ⍟ᵣ-def₂ _ = refl

  idᵣ-def : (x : s ∈ S) → idᵣ ⍟ᵣ x ≡ x
  idᵣ-def _ = refl

  wkᵣ-def : (x : s ∈ S) → (wkᵣ {s = s'}) ⍟ᵣ x ≡ there x
  wkᵣ-def _ = refl 

  ∷ᵣ-def₁ : (x : s ∈ S₂) (ρ : S₁ →ᵣ S₂) → (x ∷ᵣ ρ) ⍟ᵣ (here refl) ≡ x
  ∷ᵣ-def₁ _ _ = refl
  
  ∷ᵣ-def₂ : (x : s ∈ S₂) (x' : s' ∈ S₁) (ρ : S₁ →ᵣ S₂) → (x ∷ᵣ ρ) ⍟ᵣ (there x') ≡ ρ ⍟ᵣ x'
  ∷ᵣ-def₂ _ _ _ = refl

  -- Substitution Primitives
  ⍟ₛ-def₁ : (σ : S₁ →ₛ S₂) → (t ∷ₛ σ) ⍟ₛ (here refl) ≡ t
  ⍟ₛ-def₁ _ = refl

  ⍟ₛ-def₂ : (σ : S₁ →ₛ S₂) → (t ∷ₛ σ) ⍟ₛ (there x) ≡ σ ⍟ₛ x
  ⍟ₛ-def₂ _ = refl

  idₛ-def : (x : s ∈ S) → idₛ ⍟ₛ x ≡ ` x
  idₛ-def _ = refl

  ∷ₛ-def₁ : (T : S₂ ⊢ s) (σ : S₁ →ₛ S₂) → (T ∷ₛ σ) ⍟ₛ (here refl) ≡ T
  ∷ₛ-def₁ _ _ = refl

  ∷ₛ-def₂ : (T : S₂ ⊢ s) (x : s' ∈ S₁) (σ : S₁ →ₛ S₂) → (T ∷ₛ σ) ⍟ₛ (there x) ≡ σ ⍟ₛ x
  ∷ₛ-def₂ _ _ _ = refl

  -- Forward Composition Primitves
  ；ᵣᵣ-def : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (x : s ∈ S₁) → (ρ₁ ；ᵣᵣ ρ₂) ⍟ᵣ x ≡ ρ₂ ⍟ᵣ (ρ₁ ⍟ᵣ x)
  ；ᵣᵣ-def _ _ _ = refl

  ；ᵣₛ-def : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (x : s ∈ S₁) → (ρ₁ ；ᵣₛ σ₂) ⍟ₛ x ≡ σ₂ ⍟ₛ (ρ₁ ⍟ᵣ x)
  ；ᵣₛ-def _ _ _ = refl

  ；ₛᵣ-def : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (x : s ∈ S₁) → (σ₁ ；ₛᵣ ρ₂) ⍟ₛ x ≡ (σ₁ ⍟ₛ x) ⋯ᵣ ρ₂
  ；ₛᵣ-def _ _ _ = refl

  ；ₛₛ-def : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (x : s ∈ S₁) → (σ₁ ；ₛₛ σ₂) ⍟ₛ x ≡ (σ₁ ⍟ₛ x) ⋯ₛ σ₂
  ；ₛₛ-def _ _ _ = refl

    -- Interaction Laws
  interactᵣ : (x : s ∈ S₂) (ρ : S₁ →ᵣ S₂) → wkᵣ ；ᵣᵣ (x ∷ᵣ ρ) ≡ ρ 
  interactᵣ _ _ = refl
  interactₛ : (T : S₂ ⊢ s) (σ : S₁ →ₛ S₂) → wkᵣ ；ᵣₛ (T ∷ₛ σ) ≡ σ
  interactₛ _ _ = refl

  -- Eta Laws
  η-idᵣ : _∷ᵣ_ {s = s} {S₁ = S} (here refl) wkᵣ ≡ idᵣ 
  η-idᵣ = fun-ext (λ _ → fun-ext (λ { (here refl) → refl
                                    ; (there x) → refl }))
                                    
  η-idₛ : _∷ₛ_ {s = s} {S₁ = S} (` here refl) (wkᵣ ；ᵣₛ idₛ) ≡ idₛ
  η-idₛ = fun-ext (λ _ → fun-ext (λ { (here refl) → refl
                                    ; (there x) → refl }))

  η-lawᵣ : (ρ : (s ∷ S₁) →ᵣ S₂) → (ρ ⍟ᵣ (here refl)) ∷ᵣ (wkᵣ ；ᵣᵣ ρ) ≡ ρ
  η-lawᵣ _ = fun-ext (λ _ → fun-ext (λ { (here refl) → refl
                                       ; (there x) → refl }))

  η-lawₛ : (σ : (s ∷ S₁) →ₛ S₂) → (σ ⍟ₛ (here refl)) ∷ₛ (wkᵣ ；ᵣₛ σ) ≡ σ
  η-lawₛ _ = fun-ext (λ _ → fun-ext (λ { (here refl) → refl
                                       ; (there x) → refl }))

  -- Distributivity Laws
  distributivityᵣᵣ : (x : s ∈ S₂) (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) → (x ∷ᵣ ρ₁) ；ᵣᵣ ρ₂ ≡ (ρ₂ ⍟ᵣ x) ∷ᵣ (ρ₁ ；ᵣᵣ ρ₂)
  distributivityᵣᵣ _ _ _ = fun-ext λ _ → fun-ext λ { (here refl) → refl
                                                   ; (there x) → refl }
  distributivityᵣₛ : (x : s ∈ S₂) (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) → (x ∷ᵣ ρ₁) ；ᵣₛ σ₂ ≡ (σ₂ ⍟ₛ x) ∷ₛ (ρ₁ ；ᵣₛ σ₂)
  distributivityᵣₛ _ _ _ = fun-ext λ _ → fun-ext λ { (here refl) → refl
                                                   ; (there x) → refl }
  distributivityₛᵣ : (T : S₂ ⊢ s) (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) → (T ∷ₛ σ₁) ；ₛᵣ ρ₂ ≡ (T ⋯ᵣ ρ₂) ∷ₛ (σ₁ ；ₛᵣ ρ₂)
  distributivityₛᵣ _ _ _ = fun-ext λ _ → fun-ext λ { (here refl) → refl
                                                   ; (there x) → refl }
  distributivityₛₛ : (T : S₂ ⊢ s) (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) → (T ∷ₛ σ₁) ；ₛₛ σ₂ ≡ (T ⋯ₛ σ₂) ∷ₛ (σ₁ ；ₛₛ σ₂)
  distributivityₛₛ _ _ _ = fun-ext λ _ → fun-ext λ { (here refl) → refl
                                                   ; (there x) → refl }                        

  -- Identity Application Laws
  ⋯idᵣ : (T : S ⊢ s) → T ⋯ᵣ idᵣ ≡ T 
  ⋯idᵣ (` x)        = refl
  ⋯idᵣ (λx e)       = cong λx_ (trans (cong (e ⋯ᵣ_) η-idᵣ) (⋯idᵣ e))
  ⋯idᵣ (Λα e)       = cong Λα_ (trans (cong (e ⋯ᵣ_) η-idᵣ) (⋯idᵣ e))
  ⋯idᵣ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (⋯idᵣ k) (trans (cong (t ⋯ᵣ_) η-idᵣ) (⋯idᵣ t))
  ⋯idᵣ (e₁ · e₂)    = cong₂ _·_ (⋯idᵣ e₁) (⋯idᵣ e₂)
  ⋯idᵣ (e ∙ t)      = cong₂ _∙_ (⋯idᵣ e) (⋯idᵣ t)
  ⋯idᵣ (t₁ ⇒ t₂)    = cong₂ _⇒_ (⋯idᵣ t₁) (⋯idᵣ t₂)
  ⋯idᵣ ★            = refl

  ⋯idₛ : (T : S ⊢ s) → T ⋯ₛ idₛ ≡ T 
  ⋯idₛ (` x)        = refl
  ⋯idₛ (λx e)       = cong λx_ (trans (cong (e ⋯ₛ_) η-idₛ) (⋯idₛ e))
  ⋯idₛ (Λα e)       = cong Λα_ (trans (cong (e ⋯ₛ_) η-idₛ) (⋯idₛ e))
  ⋯idₛ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (⋯idₛ k) (trans (cong (t ⋯ₛ_) η-idₛ) (⋯idₛ t))
  ⋯idₛ (e₁ · e₂)    = cong₂ _·_ (⋯idₛ e₁) (⋯idₛ e₂)
  ⋯idₛ (e ∙ t)      = cong₂ _∙_ (⋯idₛ e) (⋯idₛ t)
  ⋯idₛ (t₁ ⇒ t₂)    = cong₂ _⇒_ (⋯idₛ t₁) (⋯idₛ t₂)
  ⋯idₛ ★            = refl

   -- Identity Composition Laws  
  left-idᵣᵣ : (ρ : S₁ →ᵣ S₂) → idᵣ ；ᵣᵣ ρ ≡ ρ 
  left-idᵣᵣ _ = refl

  right-idᵣᵣ : (ρ : S₁ →ᵣ S₂) → ρ ；ᵣᵣ idᵣ ≡ ρ
  right-idᵣᵣ _ = refl

  left-idᵣₛ : (σ : S₁ →ₛ S₂) → idᵣ ；ᵣₛ σ ≡ σ
  left-idᵣₛ _ = refl

  left-idₛᵣ : (ρ : S₁ →ᵣ S₂) → idₛ ；ₛᵣ ρ ≡ ρ ；ᵣₛ idₛ
  left-idₛᵣ _ = refl 

  left-idₛₛ : (σ : S₁ →ₛ S₂) → idₛ ；ₛₛ σ ≡ σ   
  left-idₛₛ _ = refl

  right-idₛᵣ : (σ : S₁ →ₛ S₂) → σ ；ₛᵣ idᵣ ≡ σ
  right-idₛᵣ _ = fun-ext λ _ → fun-ext λ x → ⋯idᵣ _

  right-idₛₛ : (σ : S₁ →ₛ S₂) → σ ；ₛₛ idₛ ≡ σ 
  right-idₛₛ _ = fun-ext λ _ → fun-ext λ x → ⋯idₛ _

  -- Compositionality Laws
  compositionalityᵣᵣ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ T ⋯ᵣ (ρ₁ ；ᵣᵣ ρ₂)
  compositionalityᵣᵣ ρ₁ ρ₂ (` x)        = refl
  compositionalityᵣᵣ ρ₁ ρ₂ (λx e)       = cong λx_ (trans (compositionalityᵣᵣ (ρ₁ ↑ₖᵣ _) (ρ₂ ↑ₖᵣ _) e) (cong (e ⋯ᵣ_) (distributivityᵣᵣ _ _ (ρ₂ ↑ₖᵣ _))))
  compositionalityᵣᵣ ρ₁ ρ₂ (Λα e)       = cong Λα_ (trans (compositionalityᵣᵣ (ρ₁ ↑ₖᵣ _) (ρ₂ ↑ₖᵣ _) e) (cong (e ⋯ᵣ_) (distributivityᵣᵣ _ _ (ρ₂ ↑ₖᵣ _))))
  compositionalityᵣᵣ ρ₁ ρ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᵣᵣ _ _ k) (trans (compositionalityᵣᵣ (ρ₁ ↑ₖᵣ _) (ρ₂ ↑ₖᵣ _) t) (cong (t ⋯ᵣ_) (distributivityᵣᵣ _ _ (ρ₂ ↑ₖᵣ _))))
  compositionalityᵣᵣ ρ₁ ρ₂ (e₁ · e₂)    = cong₂ _·_ (compositionalityᵣᵣ _ _ e₁)  (compositionalityᵣᵣ _ _ e₂)
  compositionalityᵣᵣ ρ₁ ρ₂ (e ∙ t)      = cong₂ _∙_ (compositionalityᵣᵣ _ _ e)  (compositionalityᵣᵣ _ _ t)
  compositionalityᵣᵣ ρ₁ ρ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᵣᵣ _ _ t₁)  (compositionalityᵣᵣ _ _ t₂)
  compositionalityᵣᵣ ρ₁ ρ₂ ★            = refl
  
  compositionalityᵣₛ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (ρ₁ ；ᵣₛ σ₂)
  compositionalityᵣₛ ρ₁ σ₂ (` x)        = refl
  compositionalityᵣₛ ρ₁ σ₂ (λx e)       = cong λx_ (trans (compositionalityᵣₛ (ρ₁ ↑ₖᵣ _) (σ₂ ↑ₖₛ _) e) (cong (e ⋯ₛ_) (distributivityᵣₛ _ _ (σ₂ ↑ₖₛ _))))
  compositionalityᵣₛ ρ₁ σ₂ (Λα e)       = cong Λα_ (trans (compositionalityᵣₛ (ρ₁ ↑ₖᵣ _) (σ₂ ↑ₖₛ _) e) (cong (e ⋯ₛ_) (distributivityᵣₛ _ _ (σ₂ ↑ₖₛ _))))
  compositionalityᵣₛ ρ₁ σ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᵣₛ _ _ k) (trans (compositionalityᵣₛ (ρ₁ ↑ₖᵣ _) (σ₂ ↑ₖₛ _) t) (cong (t ⋯ₛ_) (distributivityᵣₛ _ _ (σ₂ ↑ₖₛ _))))
  compositionalityᵣₛ ρ₁ σ₂ (e₁ · e₂)    = cong₂ _·_ (compositionalityᵣₛ _ _ e₁)  (compositionalityᵣₛ _ _ e₂)
  compositionalityᵣₛ ρ₁ σ₂ (e ∙ t)      = cong₂ _∙_ (compositionalityᵣₛ _ _ e)  (compositionalityᵣₛ _ _ t)
  compositionalityᵣₛ ρ₁ σ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᵣₛ _ _ t₁)  (compositionalityᵣₛ _ _ t₂)
  compositionalityᵣₛ ρ₁ σ₂ ★            = refl
  
  compositionalityₛᵣ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ T ⋯ₛ (σ₁ ；ₛᵣ ρ₂)
  compositionalityₛᵣ σ₁ ρ₂ (` x)        = refl
  compositionalityₛᵣ σ₁ ρ₂ (λx e)       = cong λx_ (trans (compositionalityₛᵣ (σ₁ ↑ₖₛ _) (ρ₂ ↑ₖᵣ _) e) (cong (e ⋯ₛ_) (fun-ext λ _ → fun-ext λ { (here refl) → refl; (there x) → trans (compositionalityᵣᵣ _ _ _) (sym (compositionalityᵣᵣ _ _ _)) })))
  compositionalityₛᵣ σ₁ ρ₂ (Λα e)       = cong Λα_ (trans (compositionalityₛᵣ (σ₁ ↑ₖₛ _) (ρ₂ ↑ₖᵣ _) e) (cong (e ⋯ₛ_) (fun-ext λ _ → fun-ext λ { (here refl) → refl; (there x) → trans (compositionalityᵣᵣ _ _ _) (sym (compositionalityᵣᵣ _ _ _)) })))
  compositionalityₛᵣ σ₁ ρ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityₛᵣ _ _ k) (trans (compositionalityₛᵣ (σ₁ ↑ₖₛ _) (ρ₂ ↑ₖᵣ _) t) (cong (t ⋯ₛ_) (fun-ext λ _ → fun-ext λ { (here refl) → refl; (there x) → trans (compositionalityᵣᵣ _ _ _) (sym (compositionalityᵣᵣ _ _ _)) })))
  compositionalityₛᵣ σ₁ ρ₂ (e₁ · e₂)    = cong₂ _·_ (compositionalityₛᵣ _ _ e₁)  (compositionalityₛᵣ _ _ e₂)
  compositionalityₛᵣ σ₁ ρ₂ (e ∙ t)      = cong₂ _∙_ (compositionalityₛᵣ _ _ e)  (compositionalityₛᵣ _ _ t)
  compositionalityₛᵣ σ₁ ρ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityₛᵣ _ _ t₁)  (compositionalityₛᵣ _ _ t₂)
  compositionalityₛᵣ σ₁ ρ₂ ★            = refl
  
  compositionalityₛₛ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (T : S₁ ⊢ s) → (T ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ T ⋯ₛ (σ₁ ；ₛₛ σ₂)
  compositionalityₛₛ σ₁ σ₂ (` x)        = refl
  compositionalityₛₛ σ₁ σ₂ (λx e)       = cong λx_ (trans (compositionalityₛₛ (σ₁ ↑ₖₛ _) (σ₂ ↑ₖₛ _) e) (cong (e ⋯ₛ_) (fun-ext λ _ → fun-ext λ { (here refl) → refl; (there x) → trans (compositionalityᵣₛ _ _ (σ₁ _ x)) (sym (compositionalityₛᵣ _ _ (σ₁ _ x))) })))
  compositionalityₛₛ σ₁ σ₂ (Λα e)       = cong Λα_ (trans (compositionalityₛₛ (σ₁ ↑ₖₛ _) (σ₂ ↑ₖₛ _) e) (cong (e ⋯ₛ_) (fun-ext λ _ → fun-ext λ { (here refl) → refl; (there x) → trans (compositionalityᵣₛ _ _ (σ₁ _ x)) (sym (compositionalityₛᵣ _ _ (σ₁ _ x))) })))
  compositionalityₛₛ σ₁ σ₂ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityₛₛ _ _ k) (trans (compositionalityₛₛ (σ₁ ↑ₖₛ _) (σ₂ ↑ₖₛ _) t) (cong (t ⋯ₛ_) (fun-ext λ _ → fun-ext λ { (here refl) → refl; (there x) → trans (compositionalityᵣₛ _ _ (σ₁ _ x)) (sym (compositionalityₛᵣ _ _ (σ₁ _ x))) })))
  compositionalityₛₛ σ₁ σ₂ (e₁ · e₂)    = cong₂ _·_ (compositionalityₛₛ _ _ e₁)  (compositionalityₛₛ _ _ e₂)
  compositionalityₛₛ σ₁ σ₂ (e ∙ t)      = cong₂ _∙_ (compositionalityₛₛ _ _ e)  (compositionalityₛₛ _ _ t)
  compositionalityₛₛ σ₁ σ₂ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityₛₛ _ _ t₁)  (compositionalityₛₛ _ _ t₂)
  compositionalityₛₛ σ₁ σ₂ ★            = refl
  
  -- Associativity Laws 
  associativityᵣᵣᵣ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (ρ₃ : S₃ →ᵣ S₄) → (ρ₁ ；ᵣᵣ ρ₂) ；ᵣᵣ ρ₃ ≡ ρ₁ ；ᵣᵣ (ρ₂ ；ᵣᵣ ρ₃)
  associativityᵣᵣᵣ _ _ _ = refl

  associativityᵣᵣₛ : (ρ₁ : S₁ →ᵣ S₂) (ρ₂ : S₂ →ᵣ S₃) (σ₃ : S₃ →ₛ S₄) → (ρ₁ ；ᵣᵣ ρ₂) ；ᵣₛ σ₃ ≡ ρ₁ ；ᵣₛ (ρ₂ ；ᵣₛ σ₃)
  associativityᵣᵣₛ _ _ _ = refl

  associativityᵣₛᵣ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (ρ₃ : S₃ →ᵣ S₄) → (ρ₁ ；ᵣₛ σ₂) ；ₛᵣ ρ₃ ≡ ρ₁ ；ᵣₛ (σ₂ ；ₛᵣ ρ₃)
  associativityᵣₛᵣ _ _ _ = refl

  associativityᵣₛₛ : (ρ₁ : S₁ →ᵣ S₂) (σ₂ : S₂ →ₛ S₃) (σ₃ : S₃ →ₛ S₄) → (ρ₁ ；ᵣₛ σ₂) ；ₛₛ σ₃ ≡ ρ₁ ；ᵣₛ (σ₂ ；ₛₛ σ₃)
  associativityᵣₛₛ _ _ _ = refl 
  
  associativityₛᵣᵣ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (ρ₃ : S₃ →ᵣ S₄) → (σ₁ ；ₛᵣ ρ₂) ；ₛᵣ ρ₃ ≡ σ₁ ；ₛᵣ (ρ₂ ；ᵣᵣ ρ₃)
  associativityₛᵣᵣ _ _ _ = fun-ext λ _ → fun-ext λ _ → compositionalityᵣᵣ _ _ _

  associativityₛᵣₛ : (σ₁ : S₁ →ₛ S₂) (ρ₂ : S₂ →ᵣ S₃) (σ₃ : S₃ →ₛ S₄) → (σ₁ ；ₛᵣ ρ₂) ；ₛₛ σ₃ ≡ σ₁ ；ₛₛ (ρ₂ ；ᵣₛ σ₃)
  associativityₛᵣₛ σ₁ _ _ = fun-ext λ _ → fun-ext λ x → compositionalityᵣₛ _ _ (σ₁ _ x)

  associativityₛₛᵣ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (ρ₃ : S₃ →ᵣ S₄) → (σ₁ ；ₛₛ σ₂) ；ₛᵣ ρ₃ ≡ σ₁ ；ₛₛ (σ₂ ；ₛᵣ ρ₃)
  associativityₛₛᵣ σ₁ _ _ = fun-ext λ _ → fun-ext λ x → compositionalityₛᵣ _ _ (σ₁ _ x)

  associativityₛₛₛ : (σ₁ : S₁ →ₛ S₂) (σ₂ : S₂ →ₛ S₃) (σ₃ : S₃ →ₛ S₄) → (σ₁ ；ₛₛ σ₂) ；ₛₛ σ₃ ≡ σ₁ ；ₛₛ (σ₂ ；ₛₛ σ₃)
  associativityₛₛₛ σ₁ _ _ = fun-ext λ _ → fun-ext λ x → compositionalityₛₛ _ _ (σ₁ _ x)

{-# REWRITE 
  ⍟ᵣ-def₁ ⍟ᵣ-def₂ idᵣ-def wkᵣ-def ∷ᵣ-def₁ ∷ᵣ-def₂ 
  ⍟ₛ-def₁ ⍟ₛ-def₂ idₛ-def ∷ₛ-def₁ ∷ₛ-def₂
  ；ᵣᵣ-def ；ᵣₛ-def ；ₛᵣ-def ；ₛₛ-def

  left-idᵣᵣ right-idᵣᵣ left-idᵣₛ left-idₛᵣ right-idₛᵣ left-idₛₛ right-idₛₛ
  interactᵣ interactₛ
  associativityᵣᵣᵣ associativityᵣᵣₛ associativityᵣₛᵣ associativityᵣₛₛ associativityₛᵣᵣ associativityₛᵣₛ  associativityₛₛᵣ associativityₛₛₛ
  η-idᵣ η-idₛ η-lawᵣ η-lawₛ
  distributivityᵣᵣ distributivityᵣₛ distributivityₛᵣ distributivityₛₛ
  ⋯idᵣ ⋯idₛ
  compositionalityᵣᵣ compositionalityᵣₛ compositionalityₛᵣ compositionalityₛₛ  
#-}


variable
  ρ ρ₁ ρ₂ ρ₃ ρ₄ ρ' ρ₁' ρ₂' ρ₃' ρ₄' : S₁ →ᵣ S₂
  σ σ₁ σ₂ σ₃ σ₄ σ' σ₁' σ₂' σ₃' σ₄' : S₁ →ₛ S₂

-- Typing ----------------------------------------------------------------------

⤊_ : Sort st → ∃[ st' ] Sort st'
⤊ expr = _ , type
⤊ type = _ , kind
⤊ kind = _ , kind

_∶⊢_ : List (Sort Var) → Sort st → Set
S ∶⊢ s = S ⊢ (proj₂ (⤊ s))

depth : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} → x ∈ xs → ℕ
depth (here refl) = zero
depth (there x)   = suc (depth x)

drop-∈ :  ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} →
          x ∈ xs → List A → List A
drop-∈ e xs = drop (suc (depth e)) xs

Ctx : List (Sort Var) → Set
Ctx S = ∀ s → (x : s ∈ S) → drop-∈ x S ∶⊢ s

∅ : Ctx []
∅ _ ()

_،_ : Ctx S → S ∶⊢ s → Ctx (s ∷ S)
(Γ ، t) _ (here refl) = t
(Γ ، t) _ (there x)   = Γ _ x

wk-drop-∈ : (x : s ∈ S) → drop-∈ x S ⊢ s' → S ⊢ s'
wk-drop-∈ (here refl) t = wk t 
wk-drop-∈ (there x)   t = wk (wk-drop-∈ x t) 

wk-telescope : Ctx S → s ∈ S → S ∶⊢ s
wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

_∶_∈_ : s ∈ S → S ∶⊢ s → Ctx S → Set
x ∶ t ∈ Γ = wk-telescope Γ x ≡ t

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx S

data _⊢_∶_ : {s : Sort st} → Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {s : Sort Var} {x : s ∈ S} {T} → 
    x ∶ T ∈ Γ →
    -------------
    Γ ⊢ (` x) ∶ T
  ⊢λ : 
    (Γ ، t) ⊢ e ∶ (wk t') → 
    ------------------------
    Γ ⊢ (λx e) ∶ (t ⇒ t')
  ⊢Λ :
    (Γ ، k) ⊢ e ∶ t →  
    -------------------------
    Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
  ⊢· : 
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    --------------------
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢∙ : 
    Γ ⊢ e ∶ (∀[α∶ k ] t') →
    Γ ⊢ t ∶ k →
    (Γ ، k) ⊢ t' ∶ k' →
    ------------------------
    Γ ⊢ (e ∙ t) ∶ (t' [ t ])
  ⊢★ : 
    ---------
    Γ ⊢ t ∶ ★

_∶_→ᵣ_ : S₁ →ᵣ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ᵣ_ {S₁} {S₂} ρ Γ₁ Γ₂ = ∀ (s : Sort Var) (x : s ∈ S₁) (T : S₁ ∶⊢ s) → x ∶ T ∈ Γ₁ → (ρ ⍟ᵣ x) ∶ T ⋯ᵣ ρ ∈ Γ₂ 

_∶_→ₛ_ : S₁ →ₛ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ₛ_ {S₁} {S₂} σ Γ₁ Γ₂ = ∀ (s : Sort Var) (x : s ∈ S₁) (T : S₁ ∶⊢ s) → x ∶ T ∈ Γ₁ → Γ₂ ⊢ (σ ⍟ₛ x) ∶ (T ⋯ₛ σ)

-- Semantics -------------------------------------------------------------------

data Val : S ⊢ expr → Set where
  vλ : Val (λx e)
  vΛ : Val (Λα e)

data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  β-λ :
    Val e₂ →
    ----------------------------
    ((λx e₁) · e₂) ↪ (e₁ [ e₂ ])
  β-Λ :
    ------------------------
    ((Λα e) ∙ t) ↪ (e [ t ])
  ξ-·₁ :
    e₁ ↪ e →
    --------------------
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    --------------------
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-∙ :
    e ↪ e' →
    ------------------
    (e ∙ t) ↪ (e' ∙ t)

-- Subject Reduction ----------------------------------------------------------- 

⊢wkᵣ : ∀ {s' : Sort st} {s : Sort Var} (Γ : Ctx S) (x : s ∈ S) T (T' : S ∶⊢ s') → x ∶ T ∈ Γ → (there x) ∶ (wk T) ∈ (Γ ، T')
⊢wkᵣ _ _ _ _ refl = refl

⊢↑ₖᵣ : ρ ∶ Γ₁ →ᵣ Γ₂ → (T : S₁ ∶⊢ s) → (ρ ↑ₖᵣ s) ∶ Γ₁ ، T →ᵣ (Γ₂ ، (T ⋯ᵣ ρ))
⊢↑ₖᵣ ⊢ρ T _ (here refl) _ refl = refl
⊢↑ₖᵣ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ T _ (there x) _ refl =  ⊢wkᵣ Γ₂ (ρ ⍟ᵣ x) (wk-drop-∈ x (Γ₁ _ x) ⋯ᵣ ρ) (T ⋯ᵣ ρ) (⊢ρ _ x _ refl)

⊢ρ-preserves : ∀ {t : S₁ ⊢ s} {T : S₁ ∶⊢ s} →
  ρ ∶ Γ₁ →ᵣ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (t ⋯ᵣ ρ) ∶ (T ⋯ᵣ ρ)
⊢ρ-preserves ⊢ρ (⊢` ⊢x)        = ⊢` (⊢ρ _ _ _ ⊢x) 
⊢ρ-preserves ⊢ρ (⊢λ ⊢e)        = ⊢λ (⊢ρ-preserves (⊢↑ₖᵣ ⊢ρ _) ⊢e)
⊢ρ-preserves ⊢ρ (⊢Λ ⊢e)        = ⊢Λ ((⊢ρ-preserves (⊢↑ₖᵣ ⊢ρ _) ⊢e))
⊢ρ-preserves ⊢ρ (⊢· ⊢e₁ ⊢e₂)   = ⊢· (⊢ρ-preserves ⊢ρ ⊢e₁) (⊢ρ-preserves ⊢ρ ⊢e₂)
⊢ρ-preserves ⊢ρ (⊢∙ ⊢e ⊢t ⊢t') = ⊢∙ (⊢ρ-preserves ⊢ρ ⊢e) (⊢ρ-preserves ⊢ρ ⊢t) ((⊢ρ-preserves (⊢↑ₖᵣ ⊢ρ _) ⊢t'))
⊢ρ-preserves ⊢ρ ⊢★             = ⊢★

⊢wkₛ : ∀ (Γ : Ctx S) (t : S ⊢ s) (T : S ∶⊢ s) (T' : S ∶⊢ s') → Γ ⊢ t ∶ T → (Γ ، T') ⊢ wk t ∶ wk T 
⊢wkₛ Γ _ _ T' ⊢T = ⊢ρ-preserves (λ s x T ⊢x → ⊢wkᵣ Γ x T T' ⊢x) ⊢T

⊢↑ₖₛ : σ ∶ Γ₁ →ₛ Γ₂ → (T : S ∶⊢ s) → (σ ↑ₖₛ s) ∶ Γ₁ ، T →ₛ (Γ₂ ، (T ⋯ₛ σ))
⊢↑ₖₛ ⊢σ T _ (here refl) _ refl = ⊢` refl
⊢↑ₖₛ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ T _ (there x) _ refl = ⊢wkₛ Γ₂ (σ ⍟ₛ x) (wk-drop-∈ x (Γ₁ _ x) ⋯ₛ σ) (T ⋯ₛ σ) (⊢σ _ x _ refl)

⊢σ-preserves : ∀ {σ : S₁ →ₛ S₂} {t : S₁ ⊢ s} {T : S₁ ∶⊢ s} →
  σ ∶ Γ₁ →ₛ Γ₂ →
  Γ₁ ⊢ t ∶ T →
  Γ₂ ⊢ (t ⋯ₛ σ) ∶ (T ⋯ₛ σ)
⊢σ-preserves ⊢σ (⊢` ⊢x)        = ⊢σ _ _ _ ⊢x
⊢σ-preserves {σ = σ} ⊢σ (⊢λ ⊢e)        = ⊢λ (⊢σ-preserves {σ = σ ↑ₖₛ _} (⊢↑ₖₛ {σ = σ} ⊢σ _) ⊢e)
⊢σ-preserves {σ = σ}  ⊢σ (⊢Λ ⊢e)       = ⊢Λ (⊢σ-preserves {σ = σ ↑ₖₛ _} (⊢↑ₖₛ {σ = σ} ⊢σ _) ⊢e)
⊢σ-preserves {σ = σ} ⊢σ (⊢· ⊢e₁ ⊢e₂)   = ⊢· (⊢σ-preserves {σ = σ} ⊢σ ⊢e₁) (⊢σ-preserves {σ = σ} ⊢σ ⊢e₂)
⊢σ-preserves {σ = σ} ⊢σ (⊢∙ ⊢e ⊢t ⊢t') = ⊢∙ (⊢σ-preserves {σ = σ} ⊢σ ⊢e) (⊢σ-preserves {σ = σ} ⊢σ ⊢t) (⊢σ-preserves {σ = σ ↑ₖₛ _} (⊢↑ₖₛ {σ = σ} ⊢σ _) ⊢t')
⊢σ-preserves ⊢σ ⊢★             = ⊢★

⊢[] : ∀ {Γ : Ctx S} {t : S ⊢ s} {T : S ∶⊢ s} → Γ ⊢ t ∶ T → (t ∷ₛ idₛ) ∶ (Γ ، T) →ₛ Γ
⊢[] ⊢t _ (here refl) _ refl = ⊢t
⊢[] ⊢t _ (there x)   _ refl = ⊢` refl

subject-reduction : 
  Γ ⊢ e ∶ t →   
  e ↪ e' → 
  Γ ⊢ e' ∶ t 
subject-reduction (⊢· {e₂ = e₂} (⊢λ ⊢e₁) ⊢e₂) (β-λ v₂)      = ⊢σ-preserves {σ = e₂ ∷ₛ idₛ} (⊢[] ⊢e₂) ⊢e₁
subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₁ e₁↪e)   = ⊢· (subject-reduction ⊢e₁ e₁↪e) ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₂ e₂↪e x) = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e)       
subject-reduction (⊢∙ {t = t} (⊢Λ ⊢e) ⊢t ⊢t') β-Λ           = ⊢σ-preserves {σ = t ∷ₛ idₛ} (⊢[] ⊢t) ⊢e        
subject-reduction (⊢∙ ⊢e ⊢t ⊢t')              (ξ-∙ e↪e')    = ⊢∙ (subject-reduction ⊢e e↪e') ⊢t ⊢t'                                                   