

module Substitution where

-- Imports 
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Sorts

-- Abstract Syntax
record Syntax : Set₁ where
  field
    -- Syntax
    Sort : Mode → Set
    _⊢_  : ∀ {m} → List (Sort Var) → Sort m → Set 
    `_   : ∀ {S} {s : Sort Var} → s ∈ S → S ⊢ s

    -- Axiom 
    `-injective : ∀ {S s} {x₁ x₂ : s ∈ S} → ` x₁ ≡ ` x₂ → x₁ ≡ x₂

  open Sorted Sort hiding (Scoped)
  open Meta
  
  private
    Scoped = List (Sort Var) → Sort Var → Set  

  variable 
    _∋/⊢_  _∋/⊢₁_ _∋/⊢₂_ : Scoped

  record Kit (_∋/⊢_ : Scoped) : Set where
    
    field
      id/`            : S ∋ s → S ∋/⊢ s
      `/id            : S ∋/⊢ s → S ⊢ s
      wk              : ∀ s' → S ∋/⊢ s → (s' ∷ S) ∋/⊢ s
      
      `/`-is-`        : ∀ (x : S ∋ s) → `/id (id/` x) ≡ ` x
      id/`-injective  : id/` x₁ ≡ id/` x₂ → x₁ ≡ x₂
      `/id-injective  : ∀ {x/t₁ x/t₂ : S ∋/⊢ s} →
                          `/id x/t₁ ≡ `/id x/t₂ → x/t₁ ≡ x/t₂
      wk-id/`         : ∀ s' (x : S ∋ s) →
                          wk s' (id/` x) ≡ id/` (suc x)  

    opaque 
      _→ₖ_ : List (Sort Var) → List (Sort Var) → Set
      S₁ →ₖ S₂ = ∀ s → S₁ ∋ s → S₂ ∋/⊢ s

      infixl  8  _&ₖ_
      _&ₖ_ : S₁ ∋ s → S₁ →ₖ S₂ → S₂ ∋/⊢ s
      x &ₖ ϕ = ϕ _ x 

      wkmₖ : ∀ s → S₁ →ₖ S₂ → S₁ →ₖ (s ∷ S₂)
      wkmₖ s ϕ _ x = wk s (ϕ _ x)

      _∷ₖ_ : S₂ ∋/⊢ s → S₁ →ₖ S₂ → (s ∷ S₁) →ₖ S₂
      (x/t ∷ₖ ϕ) _ zero     = x/t
      (x/t ∷ₖ ϕ) _ (suc x)  = ϕ _ x
  
      _↑ₖ_ : S₁ →ₖ S₂ → ∀ s → (s ∷ S₁) →ₖ (s ∷ S₂)
      ϕ ↑ₖ s = id/` zero ∷ₖ wkmₖ s ϕ
  
      _↑ₖ*_ : S₁ →ₖ S₂ → ∀ S → (S ++ S₁) →ₖ (S ++ S₂)
      ϕ ↑ₖ* []       = ϕ
      ϕ ↑ₖ* (s ∷ S)  = (ϕ ↑ₖ* S) ↑ₖ s
        
      idₖ : S →ₖ S
      idₖ s x = id/` x
  
      ⦅_⦆ₖ : S ∋/⊢ s → (s ∷ S) →ₖ S
      ⦅ x/t ⦆ₖ = x/t ∷ₖ idₖ
  
      weakenₖ : ∀ s → S →ₖ (s ∷ S)
      weakenₖ s = wkmₖ s idₖ
    
    _~_ : (ϕ₁ ϕ₂ : S₁ →ₖ S₂) → Set
    _~_ {S₁} ϕ₁ ϕ₂ = ∀ s (x : S₁ ∋ s) → x &ₖ ϕ₁ ≡ x &ₖ ϕ₂ 

    postulate
      ~-ext : ∀ {ϕ₁ ϕ₂ : S₁ →ₖ S₂} → ϕ₁ ~ ϕ₂ → ϕ₁ ≡ ϕ₂

    opaque
      unfolding
        _→ₖ_ _↑ₖ_ _↑ₖ*_ idₖ ⦅_⦆ₖ weakenₖ

      id↑~id : (idₖ {S} ↑ₖ s) ~ idₖ {s ∷ S}
      id↑~id s zero    = refl
      id↑~id s (suc x) =
        (idₖ ↑ₖ _) s (suc x) ≡⟨⟩
        wk _ (id/` x)        ≡⟨ wk-id/` _ x ⟩
        id/` (suc x)         ≡⟨⟩
        idₖ s (suc x)         ∎
  
      id↑*~id : ∀ S → (idₖ ↑ₖ* S) ~ idₖ {S ++ S′}
      id↑*~id []      sx x = refl
      id↑*~id (s ∷ S) sx x =
        ((idₖ ↑ₖ* S) ↑ₖ s) sx x ≡⟨ cong (λ ■ → (■ ↑ₖ s) sx x) (~-ext (id↑*~id S)) ⟩
        (idₖ ↑ₖ s) sx x        ≡⟨ id↑~id sx x ⟩
        idₖ sx x              ∎


  _∋/⊢[_]_ : ∀ {_∋/⊢_ : Scoped} → List (Sort Var) → Kit _∋/⊢_ → Sort Var → Set
  _∋/⊢[_]_ {_∋/⊢_} S K s = S ∋/⊢ s

  _–[_]→_ :  List (Sort Var) → Kit _∋/⊢_ → List (Sort Var) → Set
  S₁ –[ K ]→ S₂ = Kit._→ₖ_ K S₁ S₂

  open Kit {{ ... }} public
  
  record Traversal : Set₁ where
    infixl   5  _⋯_

    field
      _⋯_    : ∀ {{K : Kit _∋/⊢_}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
      ⋯-var  : ∀ {{K : Kit _∋/⊢_}} → (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) →
                 (` x) ⋯ ϕ ≡ `/id {{K}} (x &ₖ ϕ)
      ⋯-id   : ∀ {{K : Kit _∋/⊢_}} → (t : S ⊢ s) →
                 t ⋯ idₖ {{K}} ≡ t
    opaque
      unfolding
        _→ₖ_ _&ₖ_ wkmₖ _∷ₖ_ _↑ₖ_ _↑ₖ*_ idₖ ⦅_⦆ₖ weakenₖ 
        
      instance
        Kᵣ : Kit _∋_
        Kᵣ = record
          { id/`            = λ x → x
          ; `/id            = `_
          ; wk              = λ s' x → suc x
          ; `/`-is-`        = λ x → refl
          ; id/`-injective  = λ eq → eq
          ; `/id-injective  = `-injective
          ; wk-id/`         = λ s' x → refl }
  
        Kₛ : Kit _⊢_
        Kₛ = record
          { id/`            = `_
          ; `/id            = λ t → t
          ; `/`-is-`        = λ x → refl
          ; wk              = λ s' t → t ⋯ (weakenₖ {{Kᵣ}} s')
          ; id/`-injective  = `-injective
          ; `/id-injective  = λ eq → eq
          ; wk-id/`         = λ s' x → ⋯-var x (weakenₖ s') }
          
    open Kit Kᵣ public using () renaming 
      (_→ₖ_ to _→ᵣ_; wkmₖ to wkmᵣ; _∷ₖ_ to _∷ᵣ_; _↑ₖ_ to _↑ᵣ_; 
       _↑ₖ*_ to _↑ᵣ*_; idₖ to idᵣ; ⦅_⦆ₖ to ⦅_⦆ᵣ; weakenₖ to weakenᵣ)
    open Kit Kₛ public using () renaming 
      (_→ₖ_ to _→ₛ_; wkmₖ to wkmₛ; _∷ₖ_ to _∷ₛ_; _↑ₖ_ to _↑ₛ_; 
       _↑ₖ*_ to _↑ₛ*_; idₖ to idₛ; ⦅_⦆ₖ to ⦅_⦆ₛ; weakenₖ to weakenₛ)
     