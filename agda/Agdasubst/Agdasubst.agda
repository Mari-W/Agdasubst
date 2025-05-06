{-# OPTIONS --rewriting #-}
module Agdasubst where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional public using (_∈_)
open import Data.List.Relation.Unary.Any public using (here; there)
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Agda.Builtin.Equality.Rewrite

data SortTy : Set where
  Var : SortTy
  NoVar : SortTy

module WithSort (Sort : SortTy → Set) where

  variable
    st st₁ st₂ st₃ st₄ st' st₁' st₂' st₃' st₄' : SortTy
    s s₁ s₂ s₃ s₄ s' s₁' s₂' s₃' s₄' : Sort st
    S S₁ S₂ S₃ S₄ S' S₁' S₂' S₃' S₄' : List (Sort Var)
    
  ScopedT : Set₁
  ScopedT = ∀ {st} → List (Sort Var) → Sort st → Set

  data Desc : Set₁ where
    `σ : (A : Set) → (A → Desc) → Desc
    `X : ∀ {st} → List (Sort Var) → Sort st → Desc → Desc
    `■ : ∀ {st} → Sort st → Desc

  variable 
     d d₁ d₂ d₃ d₄ d' d₁' d₂' d₃' d₄' : Desc

  ⟦_⟧ : Desc → ScopedT → ScopedT
  ⟦ `σ A d      ⟧ X S s = Σ[ a ∈ A ] (⟦ d a ⟧ X S s)
  ⟦ `X S' s' d  ⟧ X S s = X (S' ++ S) s' × ⟦ d ⟧ X S s
  ⟦ `■ {st'} s' ⟧ X {st} S s = Σ[ eq ∈ st' ≡ st ] s ≡ subst Sort eq s'

  data Tm (d : Desc) : ScopedT where
    `var : ∀ {S s} → s ∈ S → Tm d S s
    `con : ∀ {st S} {s : Sort st} → ⟦ d ⟧ (Tm d) S s → Tm d S s

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
  
    _⨟ᵣᵣ_ : S₁ →ᵣ S₂ → S₂ →ᵣ S₃ → S₁ →ᵣ S₃
    (ρ₁ ⨟ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)
  
  _↑ᵣ_ : S₁ →ᵣ S₂ → (s : Sort Var) → (s ∷ S₁) →ᵣ (s ∷ S₂)
  ρ ↑ᵣ _ = here refl ∷ᵣ (ρ ⨟ᵣᵣ wkᵣ)

  _↑ᵣ⋆_ : S₁ →ᵣ S₂ → ∀ S → (S ++ S₁) →ᵣ (S ++ S₂)
  ρ ↑ᵣ⋆ []       = ρ
  ρ ↑ᵣ⋆ (s ∷ S)  = (ρ ↑ᵣ⋆ S) ↑ᵣ s
  
  _⋆⋯ᵣ_ : Tm d S₁ s → S₁ →ᵣ S₂ → Tm d S₂ s
  _⋆⋯ᵣ'_ : ⟦ d' ⟧ (Tm d) S₁ s → S₁ →ᵣ S₂ → ⟦ d' ⟧ (Tm d) S₂ s
  `var x ⋆⋯ᵣ ρ = `var (ρ ⍟ᵣ x) 
  `con e ⋆⋯ᵣ ρ = `con (e ⋆⋯ᵣ' ρ)
  _⋆⋯ᵣ'_ {d' = `σ A d'}     (a , D') ρ = a , D' ⋆⋯ᵣ' ρ
  _⋆⋯ᵣ'_ {d' = `X S' M' d'} (e , e') ρ = e ⋆⋯ᵣ (ρ ↑ᵣ⋆ S') , e' ⋆⋯ᵣ' ρ
  _⋆⋯ᵣ'_ {d' = `■ M'}       e        ρ = e

  ⋆wk : Tm d S s → Tm d (s' ∷ S) s
  ⋆wk T = T ⋆⋯ᵣ wkᵣ

  --opaque
  --  unfolding _→ᵣ_ _⍟ᵣ_ idᵣ wkᵣ _∷ᵣ_ _⨟ᵣᵣ_
  --  _→ₛ_ : List (Sort Var) → List (Sort Var) → Set
  --  S₁ →ₛ S₂ = ∀ s → s ∈ S₁ → Tm d S₂ s

  postulate
    ⋆⋯idᵣ′ : (T : Tm d S s) → T ⋯ id ≡ T 

  module WithDesc (d : Desc) where

    record _≃_ (A B : ScopedT) : Set₁ where
      field
        to   : ∀ {st S s} → A {st} S s → B S s
        from : ∀ {st S s} → B {st} S s → A S s
        from∘to : ∀ {st S s} (x : A {st} S s) → from (to x) ≡ x
        to∘from : ∀ {st S s} (y : B {st} S s) → to (from y) ≡ y

    open _≃_

    module Derive 
      (_⊢_ : ScopedT) 
      (iso : Tm d ≃ _⊢_) 
      (_⋯ᵣ_ : S₁ ⊢ s → S₁ →ᵣ S₂ → S₂ ⊢ s)
      -- (_⋯ₛ_ : S₁ ⊢ s → S₁ →ₛ S₂ → S₂ ⊢ s)
      where
    

      postulate 
        ⋯idᵣ : (T : S ⊢ s) → {! T  !} ⋯ᵣ idᵣ ≡ {!   !} 
      
      --{-# REWRITE ⋯idᵣ #-}
  





















  
  -- to : Tm desc S s → S ⊢ s
  -- to (`var x)                             = `_ x
  -- to (`con ([λ] , e , refl , refl))       = λx to e
  -- to (`con ([·] , e₁ , e₂ , refl , refl)) = to e₁ · to e₂
  -- to (`con ([⇒] , t₁ , t₂ , refl , refl)) = to t₁ ⇒ to t₂ 
-- 
  -- from : S ⊢ s → Tm desc S s
  -- from (` x)     = `var x
  -- from (λx e)    = `con ([λ] , from e , refl , refl)
  -- from (e₁ · e₂) = `con ([·] , from e₁ , from e₂ , refl , refl)
  -- from (t₁ ⇒ t₂) = `con ([⇒] , from t₁ , from t₂ , refl , refl)
-- 
  -- from∘to : (T : Tm desc S s) → from (to T) ≡ T
  -- from∘to (`var x) = refl
  -- from∘to (`con ([λ] , e , refl , refl)) = cong (λ e → `con ([λ] , e , refl , refl)) (from∘to e)
  -- from∘to (`con ([·] , e₁ , e₂ , refl , refl)) = cong₂ (λ e₁ e₂ → `con ([·] , e₁ , e₂ , refl , refl)) (from∘to e₁) (from∘to e₂)
  -- from∘to (`con ([⇒] , t₁ , t₂ , refl , refl)) = cong₂ (λ t₁ t₂ → `con ([⇒] , t₁ , t₂ , refl , refl)) (from∘to t₁) (from∘to t₂)
-- 
  --  to∘from : (T : S ⊢ s) → to (from T) ≡ T
  -- to∘from (` x)     = refl
  -- to∘from (λx e)    = cong λx_ (to∘from e)
  -- to∘from (e₁ · e₂) = cong₂ _·_ (to∘from e₁) (to∘from e₂)
  -- to∘from (t₁ ⇒ t₂) = cong₂ _⇒_ (to∘from t₁) (to∘from t₂)

 