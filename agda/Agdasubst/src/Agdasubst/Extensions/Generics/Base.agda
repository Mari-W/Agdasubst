-- Author(s): Guillaume Allais et al. (2020), Hannes Saffrich (2024) and Marius Weidner (2025)
module Agdasubst.Extensions.Generics.Base where 

open import Data.List using (List; []; _∷_; _++_) public
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import Agdasubst.Common
open import Agdasubst.Lib

module GenericsWithSort (Sort : SORT) where
  
  open CommonWithSort Sort 
  open Meta
  
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

  module WithDesc (d : Desc) where
    
    syn : Syntax
    syn = record
      { _⊢_         = Tm d
      ; `_          = `var
      ; `-injective = λ { refl → refl } }
 
    open Syntax syn hiding (_⊢_; `_; `-injective) public
   
    mutual
      _⋯_ : ∀ {{K : Kit k }} → Tm d S₁ s → S₁ →ₖ S₂ → Tm d S₂ s
      (`var x)  ⋯ ϕ = `/id (x & ϕ)
      (`con e′) ⋯ ϕ = `con (e′ ⋯′ ϕ)
 
      _⋯′_ : ∀ {{K : Kit k }} → ⟦ d′ ⟧ (Tm d) S₁ s → S₁ →ₖ S₂ → ⟦ d′ ⟧ (Tm d) S₂ s
      _⋯′_ {d′ = `σ A d′}     (a , D′) ϕ = a , D′ ⋯′ ϕ
      _⋯′_ {d′ = `X S′ M′ d′} (e , e′) ϕ = e ⋯ (ϕ ↑ₖ⋆ S′) , e′ ⋯′ ϕ
      _⋯′_ {d′ = `■ M′}       e        ϕ = e
   
    opaque 
      unfolding all_kit_definitions
            
      ⋯-var : ∀ {{K : Kit k }} → (x : S₁ ∋ s) (ϕ : S₁ →ₖ S₂) →
                `/id (x & ϕ) ≡ `/id (x & ϕ)
      ⋯-var x ϕ = refl

      mutual
        ⋯-id : ∀ {{K : Kit k }} → (t : Tm d S s) →
                 (t ⋯ id) ≡ t
        ⋯-id (`var x) = `/`-is-` x
        ⋯-id (`con e) = cong `con (⋯-id′ e)
 
        ⋯-id′ : ∀ {{K : Kit k }} {s : Sort m} → (t : ⟦ d′ ⟧ (Tm d) S s) →
                (t ⋯′ id) ≡ t
        ⋯-id′ {d′ = `σ A d′}     (a , D′)      = cong (a ,_) (⋯-id′ D′)
        ⋯-id′ {d′ = `X S′ M′ d′} (e , e′)      = cong₂ _,_ (trans (cong (e ⋯_) (~-ext (id↑ₖ⋆~id S′))) (⋯-id e)) (⋯-id′ e′)
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
        ⋯-fusion′  : ∀ {s : Sort m} {{K₁ : Kit k₁ }} {{K₂ : Kit k₂ }} {{K : Kit k }} {{C : ComposeKit K₁ K₂ K}}
                    (t : Tm d S₁ s) (ϕ₁ : S₁ →ₖ S₂) (ϕ₂ : S₂ →ₖ S₃) → 
                    (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
        ⋯-fusion′ (`var x)  ϕ₁ ϕ₂ = &/⋯-⋯ (ϕ₁ _ x) ϕ₂
        ⋯-fusion′ (`con e′) ϕ₁ ϕ₂ = cong `con (⋯-fusion′′ e′ ϕ₁ ϕ₂)

        ⋯-fusion′′  : ∀ {s : Sort m} {{K₁ : Kit k₁ }} {{K₂ : Kit k₂ }} {{K : Kit k }} {{C : ComposeKit K₁ K₂ K}}
                     (t : ⟦ d′ ⟧ (Tm d) S₁ s) (ϕ₁ : S₁ →ₖ S₂) (ϕ₂ : S₂ →ₖ S₃) → 
                     (t ⋯′ ϕ₁) ⋯′ ϕ₂ ≡ t ⋯′ (ϕ₁ ; ϕ₂)
        ⋯-fusion′′ {d′ = `σ A d′}     (a , D′)      ϕ₁ ϕ₂ = cong (a ,_) (⋯-fusion′′ D′ ϕ₁ ϕ₂)
        ⋯-fusion′′ {d′ = `X S′ M′ d′} (e₁ , e₂)     ϕ₁ ϕ₂ = cong₂ _,_ (trans (⋯-fusion′ e₁ (ϕ₁ ↑ₖ⋆ S′) (ϕ₂ ↑ₖ⋆ S′))
          (cong (e₁ ⋯_) (sym (~-ext (dist-↑ₖ⋆-; S′ ϕ₁ ϕ₂)))))
          (⋯-fusion′′ e₂ ϕ₁ ϕ₂)
        ⋯-fusion′′ {d′ = `■ M′}       (refl , refl) ϕ₁ ϕ₂ = refl

    compose : Compose
    compose = record { ⋯-fusion′ = ⋯-fusion′ }

    open Compose compose hiding (⋯-fusion′)

    ⋯-fusion : ∀ {{K₁ : Kit k₁ }} {{K₂ : Kit k₂}}
                 (t : Tm d S₁ s) (ϕ₁ : S₁ –[ K₁ ]→ S₂) (ϕ₂ : S₂ –[ K₂ ]→ S₃)  → 
                 (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ let instance _ = K₁ ⊔ K₂; _ = C–⊔ in t ⋯ (ϕ₁ ; ϕ₂)
    ⋯-fusion {{K₁ }} {{K₂ }} = let instance _ = K₁ ⊔ K₂; _ = C–⊔ in ⋯-fusion′ 

    {-# REWRITE 
      id-def ∙-def₁ ∙-def₂ wk-def wkm-def ;-def 
      `/`-cancel def-&/⋯Cₛ def-&/⋯Cᵣ &/⋯→& &/⋯→&′ &/⋯→⋯ &/⋯→⋯′
      interact η-id η-law left-id right-id norm-id distributivity
      ⋯-id ⋯-fusion
      associativityᵣᵣᵣ associativityᵣᵣₛ associativityᵣᵣₖ
      associativityᵣₛᵣ associativityᵣₛₛ associativityᵣₛₖ
      associativityᵣₖᵣ associativityᵣₖₛ associativityᵣₖₖ
      associativityₛᵣᵣ associativityₛᵣₛ associativityₛᵣₖ
      associativityₛₛᵣ associativityₛₛₛ associativityₛₛₖ 
      associativityₛₖᵣ associativityₛₖₛ associativityₛₖₖ
      associativityₖᵣᵣ associativityₖᵣₛ associativityₖᵣₖ
      associativityₖₛᵣ associativityₖₛₛ associativityₖₛₖ
      associativityₖₖᵣ                  associativityₖₖₖ 
    #-} --             associativityₖₖₛ  