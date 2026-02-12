{-# OPTIONS --rewriting --local-confluence --double-check #-}
module Examples.SystemF.Definitions where

open import Agdasubst

data Sort : Set where 
  kind type expr : Sort

open WithSort Sort 

data _⊢_ : Scoped where 
  `_       : S ∋ s → S ⊢ s     
  λx_      : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_      : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_  : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_      : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_      : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_      : S ⊢ type → S ⊢ type → S ⊢ type
  ★        : S ⊢ kind

open WithSyntax _⊢_ `_

[_,_]_⋯_ : Traversal
[ m , _↑*_ ] (` x) ⋯ φ = m ⟨ (φ _ x)  ⟩ 
[ m , _↑*_ ] λx e        ⋯ φ = λx ([ m , _↑*_ ] e ⋯ (φ ↑* _))
[ m , _↑*_ ] Λα e        ⋯ φ = Λα ([ m , _↑*_ ] e ⋯ (φ ↑* _))
[ m , _↑*_ ] ∀[α∶ k ] t  ⋯ φ = ∀[α∶ [ m , _↑*_ ] k ⋯ φ ] [ m , _↑*_ ] t ⋯ (φ ↑* _)
[ m , _↑*_ ] e₁ · e₂     ⋯ φ = {!   !} · {!   !}
[ m , _↑*_ ] e • t       ⋯ φ = {!   !}
[ m , _↑*_ ] t₁ ⇒ t₂     ⋯ φ = {!   !}
[ m , _↑*_ ] ★           ⋯ φ = {!   !} 

open WithTraversal [_,_]_⋯_


{-# REWRITE 
  beta-lift-id

  beta-ext-zero 
  beta-ext-suc  
  beta-lift     

  associativity  
  distributivityˢ
  distributivityᴿ
  interact       
  comp-idᵣ       
  comp-idₗ       
  η-id           
  η-lawˢ         
  η-lawᴿ      

  right-idˢ         
  right-idᴿ         
  compositionalityᴿˢ
  compositionalityᴿᴿ
  compositionalityˢᴿ
  compositionalityˢˢ

  coincidence      
  coincidence-fold 
#-}
