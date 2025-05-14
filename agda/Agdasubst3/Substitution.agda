
module Substitution where


-- Imports 
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; module ≡-Reasoning)
open ≡-Reasoning

open import Variables
open import Sorts using (module Sorted)

module Sub (Sort : Mode → Set) where

  -- Abstract Syntax
  record Syntax : Set₁ where
    field
      -- Syntax
      _⊢_  : ∀ {m} → List (Sort Var) → Sort m → Set 
      `_   : ∀ {S} {s : Sort Var} → S ∋ s → S ⊢ s
  
      -- Axiom 
      `-injective : ∀ {S s} {x₁ x₂ : S ∋ s} → ` x₁ ≡ ` x₂ → x₁ ≡ x₂
  
    open Sorted Sort hiding (Scoped)
    open Meta
    
    record Kit (_∋/⊢_ : List (Sort Var) → Sort Var → Set) : Set where
      
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
        
        open import Data.Unit using (⊤; tt)
        KIT : ⊤
        KIT = tt

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
        unfolding KIT
  
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
  
  
    _∋/⊢[_]_ : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} → List (Sort Var) → Kit _∋/⊢_ → Sort Var → Set
    _∋/⊢[_]_ {_∋/⊢_} S K s = S ∋/⊢ s
  
    _–[_]→_ : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} → List (Sort Var) → Kit _∋/⊢_ → List (Sort Var) → Set
    S₁ –[ K ]→ S₂ = Kit._→ₖ_ K S₁ S₂
  
    open Kit {{ ... }} public
    
    record Traversal : Set₁ where
      infixl   5  _⋯_
  
      field
        _⋯_    : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → S₁ ⊢ s → S₁ –[ K ]→ S₂ → S₂ ⊢ s
        ⋯-var  : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → (x : S₁ ∋ s) (ϕ : S₁ –[ K ]→ S₂) →
                   (` x) ⋯ ϕ ≡ `/id {{K}} (x &ₖ ϕ)
        ⋯-id   : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → (t : S ⊢ s) →
                   t ⋯ idₖ {{K}} ≡ t
      instance
        Kᵣ : Kit _∋_
        Kᵣ = record
          { id/`            = λ x → x
          ; `/id            = `_
          ; wk              = λ s' x → suc x
          ; `/`-is-`        = λ x → refl
          ; id/`-injective  = λ eq → eq 
          ; `/id-injective  = `-injective 
          ; wk-id/`         = λ s' x → refl 
          }

      opaque
        unfolding KIT
        private 
          Kₛ-wk-id/` : {S : Sorts} {s : Sort Var} (s' : Sort Var) (x : S ∋ s) →
                      (` x) ⋯ Kit.weakenₖ Kᵣ s' ≡ (` suc x)
          Kₛ-wk-id/` = λ s' x → ⋯-var x (weakenₖ s')

      instance
        Kₛ : Kit _⊢_
        Kₛ = record
          { id/`            = `_
          ; `/id            = λ t → t
          ; wk              = λ s' t → t ⋯ (weakenₖ {{Kᵣ}} s')
          ; `/`-is-`        = λ x → refl
          ; id/`-injective  = `-injective
          ; `/id-injective  = λ eq → eq 
          ; wk-id/`         = Kₛ-wk-id/`
          }

      open Kit Kᵣ public using () renaming 
        (_→ₖ_ to _→ᵣ_; wkmₖ to wkmᵣ; _∷ₖ_ to _∷ᵣ_; _↑ₖ_ to _↑ᵣ_; 
         _↑ₖ*_ to _↑ᵣ*_; idₖ to idᵣ; ⦅_⦆ₖ to ⦅_⦆ᵣ; weakenₖ to weakenᵣ)
      open Kit Kₛ public using () renaming 
        (_→ₖ_ to _→ₛ_; wkmₖ to wkmₛ; _∷ₖ_ to _∷ₛ_; _↑ₖ_ to _↑ₛ_; 
         _↑ₖ*_ to _↑ₛ*_; idₖ to idₛ; ⦅_⦆ₖ to ⦅_⦆ₛ; weakenₖ to weakenₛ)

      _⋯ᵣ_ : S₁ ⊢ s → S₁ →ᵣ S₂ → S₂ ⊢ s
      t ⋯ᵣ ρ = t ⋯ ρ

      _⋯ₛ_ : S₁ ⊢ s → S₁ →ₛ S₂ → S₂ ⊢ s
      t ⋯ₛ σ = t ⋯ σ

  module _ where
    open import Isomorphism
    open Iso Sort
    open import Sorts
    open Sorted Sort
    open Meta
  
    record KitIso : Set₁ where
      field
        syn₁ syn₂ : Syntax
        iso : (Syntax._⊢_ syn₁) ≃ (Syntax._⊢_ syn₂)
      
        -- Axiom
        `_-is-`var : ∀ (x : S ∋ s) → _≃_.to iso (Syntax.`_ syn₁ x) ≡ (Syntax.`_ syn₂ x)
      
      open _≃_ iso

      open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong-app; subst; module ≡-Reasoning)
      
      to-Kit : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} → Syntax.Kit syn₁ _∋/⊢_ → Syntax.Kit syn₂ _∋/⊢_
      to-Kit record 
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
        ; `/`-is-` = λ x → trans (cong to (`/`-is-` x)) (`_-is-`var x)
        ; id/`-injective = id/`-injective
        ; `/id-injective = λ x → `/id-injective (to-injective x)
        ; wk-id/` = wk-id/` 
        }

      opaque
        unfolding Syntax.Kit.KIT
        abc : ∀ (_∋/⊢_ : List (Sort Var) → Sort Var → Set) (K : Syntax.Kit syn₁ _∋/⊢_) → 
             Syntax.Kit._→ₖ_ (to-Kit K) S₁ S₂ ≡ Syntax.Kit._→ₖ_ K S₁ S₂ 
        abc _ _ = refl 