module Generics where

open import Data.List using (List; []; _∷_; _++_) public
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; subst)

open import Variables
open import Sorts using (module Sorted)
open import Substitution as _ using (module Sub) 

module Generic (Sort : Mode → Set) where
  
  open Sorted Sort
  open Meta
  
  data Desc : Set₁ where
    `σ : (A : Set) → (A → Desc) → Desc
    `X : Sorts → Sort m → Desc → Desc
    `■ : Sort m → Desc

  private variable
    d d₁ d₂ d₃ d′ d₁′ d₂′ d₃′  : Desc

  ⟦_⟧ : Desc → Scoped → Scoped
  ⟦ `σ A d      ⟧ X S s = Σ[ a ∈ A ] (⟦ d a ⟧ X S s)
  ⟦ `X S′ s′ d  ⟧ X S s = X (S′ ++ S) s′ × ⟦ d ⟧ X S s
  ⟦ `■ {m′} s′ ⟧ X {m} S s = Σ[ eq ∈ m′ ≡ m ] s ≡ subst Sort eq s′
  
  data Tm (d : Desc) : Scoped where
    `var : S ∋ s → Tm d S s
    `con : ⟦ d ⟧ (Tm d) S s → Tm d S s

  open Sub Sort

  module Substitution (d : Desc) where
    private
      syn : Syntax
      syn = record
        { _⊢_         = Tm d
        ; `_          = `var
        ; `-injective = λ { refl → refl }
        }

    open Syntax syn hiding (_⊢_; `_; `-injective) public
    
    opaque 
      unfolding _→ₖ_ _↑ₖ_ _↑ₖ*_ idₖ
             
      mutual
        _⋯_ : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → Tm d S₁ s → S₁ →ₖ S₂ → Tm d S₂ s
        (`var x)  ⋯  ϕ = `/id (ϕ _ x)
        (`con e′) ⋯ ϕ = `con (e′ ⋯′ ϕ)

        _⋯′_ : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → ⟦ d′ ⟧ (Tm d) S₁ s → S₁ →ₖ S₂ → ⟦ d′ ⟧ (Tm d) S₂ s
        _⋯′_ {d′ = `σ A d′}     (a , D′) ϕ = a , D′ ⋯′ ϕ
        _⋯′_ {d′ = `X S′ M′ d′} (e , e′) ϕ = e ⋯ (ϕ ↑ₖ* S′) , e′ ⋯′ ϕ
        _⋯′_ {d′ = `■ M′}       e        ϕ = e

      ⋯-var : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → (x : S₁ ∋ s) (ϕ : S₁ →ₖ S₂) →
                `/id (x &ₖ ϕ) ≡ `/id (x &ₖ ϕ)
      ⋯-var x ϕ = refl

      mutual
        ⋯-id : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} → (t : Tm d S s) →
                 (t ⋯ idₖ) ≡ t
        ⋯-id (`var x) = `/`-is-` x
        ⋯-id (`con e) = cong `con (⋯-id′ e)

        ⋯-id′ : ∀ {_∋/⊢_ : List (Sort Var) → Sort Var → Set} {{K : Kit _∋/⊢_}} {s : Sort m} → (t : ⟦ d′ ⟧ (Tm d) S s) →
                (t ⋯′ idₖ) ≡ t
        ⋯-id′ {d′ = `σ A d′}     (a , D′)      = cong (a ,_) (⋯-id′ D′)
        ⋯-id′ {d′ = `X S′ M′ d′} (e , e′)      = cong₂ _,_ (trans (cong (e ⋯_) (~-ext (id↑*~id S′))) (⋯-id e)) (⋯-id′ e′)
        ⋯-id′ {d′ = `■ M′}       (refl , refl) = refl

      traversal : Traversal
      traversal = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var ; ⋯-id  = ⋯-id }
    
    
       