-- Author: Hannes Saffrich
-- Modified: Marius Weidner
{-# OPTIONS --rewriting #-}
module Generics where

open import Data.List using (List; []; _∷_; _++_) public
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import DeBruijn
open import Sorts
open import Kits
open import SigmaCalculus

module GenericsWithSort (Sort : Mode → Set) where
  
  open SortsWithSort Sort
  open SortsMeta
  
  data Desc : Set₁ where
    `σ : (A : Set) → (A → Desc) → Desc
    `X : Scope → Sort m → Desc → Desc
    `■ : Sort m → Desc

  module GenericsMeta where
    variable
      d d₁ d₂ d₃ d′ d₁′ d₂′ d₃′  : Desc
  open GenericsMeta

  ⟦_⟧ : Desc → SCOPED → SCOPED
  ⟦ `σ A d      ⟧ X S s = Σ[ a ∈ A ] (⟦ d a ⟧ X S s)
  ⟦ `X S′ s′ d  ⟧ X S s = X (S′ ++ S) s′ × ⟦ d ⟧ X S s
  ⟦ `■ {m′} s′ ⟧ X {m} S s = Σ[ eq ∈ m′ ≡ m ] s ≡ subst Sort eq s′
  
  data Tm (d : Desc) : SCOPED where
    `var : S ∋ s → Tm d S s
    `con : ⟦ d ⟧ (Tm d) S s → Tm d S s

  open KitsWithSort Sort

  module GenericsWithDesc (d : Desc) where
    
    syn : Syntax
    syn = record
      { _⊢_         = Tm d
      ; `_          = `var
      ; `-injective = λ { refl → refl } }
 
    open Syntax syn hiding (_⊢_; `_; `-injective) public
   
    mutual
      _⋯_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → Tm d S₁ s → S₁ →ₖ S₂ → Tm d S₂ s
      (`var x)  ⋯ ϕ = `/id (x & ϕ)
      (`con e′) ⋯ ϕ = `con (e′ ⋯′ ϕ)
 
      _⋯′_ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → ⟦ d′ ⟧ (Tm d) S₁ s → S₁ →ₖ S₂ → ⟦ d′ ⟧ (Tm d) S₂ s
      _⋯′_ {d′ = `σ A d′}     (a , D′) ϕ = a , D′ ⋯′ ϕ
      _⋯′_ {d′ = `X S′ M′ d′} (e , e′) ϕ = e ⋯ (ϕ ↑ₖ* S′) , e′ ⋯′ ϕ
      _⋯′_ {d′ = `■ M′}       e        ϕ = e
   
    opaque 
      unfolding all_kit_definitions
            
      ⋯-var : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → (x : S₁ ∋ s) (ϕ : S₁ →ₖ S₂) →
                `/id (x & ϕ) ≡ `/id (x & ϕ)
      ⋯-var x ϕ = refl

      mutual
        ⋯-id : ∀ ⦃ K : Kit _∋/⊢_ ⦄ → (t : Tm d S s) →
                 (t ⋯ id) ≡ t
        ⋯-id (`var x) = `/`-is-` x
        ⋯-id (`con e) = cong `con (⋯-id′ e)
 
        ⋯-id′ : ∀ ⦃ K : Kit _∋/⊢_ ⦄ {s : Sort m} → (t : ⟦ d′ ⟧ (Tm d) S s) →
                (t ⋯′ id) ≡ t
        ⋯-id′ {d′ = `σ A d′}     (a , D′)      = cong (a ,_) (⋯-id′ D′)
        ⋯-id′ {d′ = `X S′ M′ d′} (e , e′)      = cong₂ _,_ (trans (cong (e ⋯_) (~-ext (id↑ₖ*~id S′))) (⋯-id e)) (⋯-id′ e′)
        ⋯-id′ {d′ = `■ M′}       (refl , refl) = refl
       
    traversal : Traversal
    traversal = record 
      { _⋯_ = _⋯_ 
      ; ⋯-var = ⋯-var 
      ; ⋯-id  = ⋯-id }

    open Traversal traversal hiding (_⋯_; ⋯-id; ⋯-var)

    opaque
      unfolding all_kit_and_compose_definitions

      mutual
        ⋯-fusion  : ∀ {s : Sort m} ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                    ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
                    (t : Tm d S₁ s) (ϕ₁ : S₁ →ₖ S₂) (ϕ₂ : S₂ →ₖ S₃) → 
                    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ； ϕ₂)
        ⋯-fusion (`var x)  ϕ₁ ϕ₂ = sym (&/⋯-⋯ (ϕ₁ _ x) ϕ₂)
        ⋯-fusion (`con e′) ϕ₁ ϕ₂ = cong `con (⋯-fusion′ e′ ϕ₁ ϕ₂)

        ⋯-fusion′  : ∀ {s : Sort m} ⦃ K₁ : Kit _∋/⊢₁_ ⦄ ⦃ K₂ : Kit _∋/⊢₂_ ⦄ ⦃ K : Kit _∋/⊢_ ⦄
                     ⦃ W₁ : WkKit K₁ ⦄ ⦃ C : ComposeKit K₁ K₂ K ⦄
                     (t : ⟦ d′ ⟧ (Tm d) S₁ s) (ϕ₁ : S₁ →ₖ S₂) (ϕ₂ : S₂ →ₖ S₃) → 
                     (t ⋯′ ϕ₁) ⋯′ ϕ₂ ≡ t ⋯′ (ϕ₁ ； ϕ₂)
        ⋯-fusion′ {d′ = `σ A d′}     (a , D′)      ϕ₁ ϕ₂ = cong (a ,_) (⋯-fusion′ D′ ϕ₁ ϕ₂)
        ⋯-fusion′ {d′ = `X S′ M′ d′} (e₁ , e₂)     ϕ₁ ϕ₂ = cong₂ _,_ (trans (⋯-fusion e₁ (ϕ₁ ↑ₖ* S′) (ϕ₂ ↑ₖ* S′))
          (cong (e₁ ⋯_) (sym (~-ext (dist-↑ₖ*-； S′ ϕ₁ ϕ₂)))))
          (⋯-fusion′ e₂ ϕ₁ ϕ₂)
        ⋯-fusion′ {d′ = `■ M′}       (refl , refl) ϕ₁ ϕ₂ = refl

    compose : ComposeTraversal
    compose = record { ⋯-fusion = ⋯-fusion }

    open ComposeTraversal hiding (⋯-fusion)

    rules : Rules
    rules = record 
      { Sort = Sort 
      ; syn = syn 
      ; traversal = traversal 
      ; compose = compose }
        
    
        