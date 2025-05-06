module Generics where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Substitution as _

module Generic (Sort : Mode → Set) where
  
  private variable
    m m₁ m₂ m₃ m′ m₁′ m₂′ m₃′  : Mode
    s s₁ s₂ s₃ s′ s₁′ s₂′ s₃′  : Sort m
    S S₁ S₂ S₃ S′ S₁′ S₂′ S₃′  : List (Sort Var)
    x x₁ x₂ x₃ x′ x₁′ x₂′ x₃′  : s ∈ S
  
  Scoped = ∀ {m} → List (Sort Var) → Sort m → Set
  
  data Desc : Set₁ where
    `σ : (A : Set) → (A → Desc) → Desc
    `X : List (Sort Var) → Sort m → Desc → Desc
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


  module Substitution (d : Desc) where
    syn : Syntax
    syn = record
      { Sort        = Sort
      ; _⊢_         = Tm d
      ; `_          = `var
      ; `-injective = λ { refl → refl }
      }

    open Syntax syn hiding (Sort; `_; `-injective)
    
    opaque 
      unfolding _→ₖ_ _↑ₖ_ _↑ₖ*_
       
      mutual
        _⋯_ : Tm d S₁ s → S₁ –[ K ]→ S₂ → Tm d S₂ s
        _⋯_ {K = K} (`var x)  f = Kit.`/id K (f _ x)
        _⋯_ {K = K} (`con e′) f = `con (_⋯′_ {K = K} e′ f)

        _⋯′_ : ⟦ d′ ⟧ (Tm d) S₁ s → S₁ –[ K ]→ S₂ → ⟦ d′ ⟧ (Tm d) S₂ s
        _⋯′_ {d′ = `σ A d′}     {K = K} (a , D′) f = a , _⋯′_ {K = K} D′ f
        _⋯′_ {d′ = `X S′ M′ d′} {K = K} (e , e′) f = _⋯_ {K = K} e (Kit._↑ₖ*_ K f S′) , _⋯′_ {K = K} e′ f
        _⋯′_ {d′ = `■ M′}               e        f = e
c
      -- ⋯-var :
      --   ∀ {S₁ : List (Sort Var)} {m : Sort Var} {S₂ : List (Sort Var)}
      --     {_∋/⊢_ : Scoped} ⦃ 𝕂 : Kit _∋/⊢_ ⦄
      --     (x : S₁ ∋ m) (ϕ : S₁ –[ 𝕂 ]→ S₂) →
      --   `/id (ϕ m x) ≡ `/id (ϕ m x)
      -- ⋯-var x ϕ = refl
-- 
      -- mutual
      --   ⋯-id :
      --     ∀ {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄
      --       {S st} {s : Sort st} (t : Tm d S s) →
      --     (t ⋯ id) ≡ t
      --   ⋯-id (`var x) = `/`-is-` x
      --   ⋯-id (`con e) = cong `con (⋯-id′ e)
-- 
      --   ⋯-id′ :
      --     ∀ {d′} {_∋/⊢_ : Scoped} ⦃ K : Kit _∋/⊢_ ⦄
      --       {S st} {s : Sort st} (t : ⟦ d′ ⟧ (Tm d) S s) →
      --     (t ⋯′ id) ≡ t
      --   ⋯-id′ {d′ = `σ A d′}     (a , D′)  = cong (a ,_) (⋯-id′ D′)
      --   ⋯-id′ {d′ = `X S′ M′ d′} (e₁ , e₂) = cong₂ _,_ (trans (cong (e₁ ⋯_) (~-ext (id↑*~id S′))) (⋯-id e₁)) (⋯-id′ e₂)
      --   ⋯-id′ {d′ = `■ M′}       (refl , refl) = refl
-- 
    -- KT--  : Traversal
    -- KT--  = record { _⋯_ = _⋯_ ; ⋯-var = ⋯-var ; ⋯-id  = ⋯-id }
     