-- Author(s): Guillaume Allais et al. (2020), Hannes Saffrich (2024) and Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Extensions.Generics.Base where 

open import Data.List using (List; []; _∷_; _++_) public
open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import Agdasubst.Common
open import Agdasubst.Lib

--! G > 

module GenericsWithSort (Sort : Set) where
  
  open CommonWithSort Sort 
  open Meta
  
  --! Desc
  data Desc : Set₁ where
    `σ : (A : Set) → (A → Desc) → Desc
    `X : Scope → Sort → Desc → Desc
    `■ : Sort → Desc

  module GenericsMeta where
    variable
      d d₁ d₂ d₃ d′ d₁′ d₂′ d₃′  : Desc
  open GenericsMeta


  --! Denot
  ⟦_⟧ : Desc → Scoped → Scoped
  ⟦ `σ A d      ⟧ X S s = Σ[ a ∈ A ] (⟦ d a ⟧ X S s)
  ⟦ `X S′ s′ d  ⟧ X S s = X (S′ ++ S) s′ × ⟦ d ⟧ X S s
  ⟦ `■ s′ ⟧ X S s = s ≡ s′
  
  --! Tms
  data Tm (d : Desc) : Scoped where
    `var : S ∋ s → Tm d S s
    `con : ⟦ d ⟧ (Tm d) S s → Tm d S s

  open KitsWithSort Sort

  module WithDesc (d : Desc) where
    module _ where
      instance syn = mkSyntax (Tm d) `var  λ { refl → refl }
      open Syntax syn hiding (`_; _⊢_; _&_) public 

      private _⋯_ : ∀ {{K : Kit M}} → Tm d S₁ s → S₁ →ᴷ S₂ → Tm d S₂ s
      _⋯′_ : ∀ {{K : Kit M}} → ⟦ d′ ⟧ (Tm d) S₁ s → S₁ →ᴷ S₂ → ⟦ d′ ⟧ (Tm d) S₂ s

      (`var x)  ⋯ ϕ = x `⋯ ϕ
      (`con e′) ⋯ ϕ = `con (e′ ⋯′ ϕ)
      _⋯′_ {d′ = `σ A d′}     (a , D′) ϕ = a , D′ ⋯′ ϕ
      _⋯′_ {d′ = `X S′ M′ d′} (e , e′) ϕ = e ⋯ (ϕ ↑★ S′) , e′ ⋯′ ϕ
      _⋯′_ {d′ = `■ M′}       e        ϕ = e


      ⋯-right-id : ∀ {{K : Kit M}} → (t : Tm d S s) →
               (t ⋯ id) ≡ t
      ⋯-right-id′ : ∀ {{K : Kit M}} → (t : ⟦ d′ ⟧ (Tm d) S s) →
               (t ⋯′ id) ≡ t
      ⋯-right-id (`var x) = `⋯-right-id x
      ⋯-right-id (`con e) = cong `con (⋯-right-id′ e)
      ⋯-right-id′ {d′ = `σ A d′}     (a , D′)      = cong (a ,_) (⋯-right-id′ D′)
      ⋯-right-id′ {d′ = `X S′ M′ d′} (e , e′)      = cong₂ _,_ (trans (cong (e ⋯_) (~-ext (id↑★~id S′))) (⋯-right-id e)) (⋯-right-id′ e′)
      ⋯-right-id′ {d′ = `■ M′}       refl          = refl

      instance traversal = mkTraversal _⋯_ ⋯-right-id λ x ϕ → refl
      open Traversal traversal hiding (_⋯_; ⋯-right-id; ⋯-var) public

      ⋯-compositionality  : ∀ {s : Sort} {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{C : ComposeKit K₁ K₂ K₃}}
                  (t : Tm d S₁ s) (ϕ₁ : S₁ →ᴷ S₂) (ϕ₂ : S₂ →ᴷ S₃) → 
                  (t ⋯ ϕ₁) ⋯ ϕ₂ ≡ t ⋯ (ϕ₁ ; ϕ₂)
      ⋯-compositionality′ : ∀ {s : Sort} {{K₁ : Kit M₁}} {{K₂ : Kit M₂}} {{K₃ : Kit M₃}} {{C : ComposeKit K₁ K₂ K₃}}
                   (t : ⟦ d′ ⟧ (Tm d) S₁ s) (ϕ₁ : S₁ →ᴷ S₂) (ϕ₂ : S₂ →ᴷ S₃) → 
                   (t ⋯′ ϕ₁) ⋯′ ϕ₂ ≡ t ⋯′ (ϕ₁ ; ϕ₂)
      ⋯-compositionality (`var x)  ϕ₁ ϕ₂ = `⋯-compositionality x ϕ₁ ϕ₂
      ⋯-compositionality (`con e′) ϕ₁ ϕ₂ = cong `con (⋯-compositionality′ e′ ϕ₁ ϕ₂)
      ⋯-compositionality′ {d′ = `σ A d′}     (a , D′)      ϕ₁ ϕ₂ = cong (a ,_) (⋯-compositionality′ D′ ϕ₁ ϕ₂)
      ⋯-compositionality′ {d′ = `X S′ M′ d′} (e₁ , e₂)     ϕ₁ ϕ₂ = cong₂ _,_ (trans (⋯-compositionality e₁ (ϕ₁ ↑★ S′) (ϕ₂ ↑★ S′))
        (cong (e₁ ⋯_) (sym (~-ext (dist-↑★-; S′ ϕ₁ ϕ₂)))))
        (⋯-compositionality′ e₂ ϕ₁ ϕ₂)
      ⋯-compositionality′ {d′ = `■ M′}       refl          ϕ₁ ϕ₂ = refl

      compose : Compose
      compose = mkCompose ⋯-compositionality 

      open Compose compose hiding (⋯-compositionality) public
    
    _&_ : {{K : Kit M}} → S₁ ∋ s → S₁ –[ K ]→ S₂ → S₂ ∋/⊢[ K ] s
    _&_ = _&/⋯_ 

    _⋯_ : {{K : Kit M}} → Tm d S₁ s → S₁ –[ K ]→ S₂ → Tm d S₂ s
    _⋯_ {{K}} = let instance _ = K ;ᴷ V in _&/⋯_ 


module example where 
  --!! Sort
  data Sort : Set where expr : Sort

  open GenericsWithSort Sort

  --!! Label
  data Label : Set where [λ] [·] : Label

  --! DescL
  desc : Desc
  desc = `σ Label λ where
    [λ] → `X (expr ∷ []) expr (`■ expr)
    [·] → `X [] expr (`X [] expr (`■ expr))

  open WithDesc desc

  --! Pattern
  pattern `_ x      = `var x
  pattern λx_ e     = `con ([λ] , e , (refl , refl))
  pattern _·_ e₁ e₂ = `con ([·] , e₁ , e₂ , (refl , refl))
