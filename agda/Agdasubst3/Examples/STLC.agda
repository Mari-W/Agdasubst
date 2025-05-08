{-# OPTIONS --rewriting #-}
module Examples.STLC where

open import Data.Product using (Σ; ∃-syntax; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; subst)

open import Prelude

data Sort : Mode → Set where
  expr : Sort Var
  type : Sort ¬Var

open Sorted Sort
open Meta 

data _⊢_ : Scoped where
  `_        : S ∋ s → S ⊢ s               
  λx_       : (expr ∷ S) ⊢ expr → S ⊢ expr        
  _·_       : S ⊢ expr → S ⊢ expr → S ⊢ expr      
  _⇒_       : S ⊢ type → S ⊢ type → S ⊢ type 

---- DERIVE BEGIN
-- SYNTAX
open Sub Sort
syn : Syntax
syn = record 
  { _⊢_ = _⊢_ 
  ; `_ = `_
  ; `-injective = λ { refl → refl } 
  }

-- GENERICS
open import Generics
open Generic Sort 

data Label : Set where
  [λ] [·] [⇒] : Label

desc : Desc
desc = `σ Label λ where
  [λ] → `X (expr ∷ []) expr (`■ expr)
  [·] → `X [] expr (`X [] expr (`■ expr))
  [⇒] → `X [] type (`X [] type (`■ type))
  
pattern ⋆λx_ e     = `con ([λ] , e , (refl , refl))
pattern _⋆·_ e₁ e₂ = `con ([·] , e₁ , e₂ , (refl , refl))
pattern _⋆⇒_ t₁ t₂ = `con ([⇒] , t₁ , t₂ , (refl , refl))
pattern ⋆`_ x      = `var x

-- ISO 
open import Isomorphism using (module Iso)
open Iso Sort

to : Tm desc S s → S ⊢ s
to (⋆` x)     = `_ x
to (⋆λx e)    = λx to e
to (e₁ ⋆· e₂) = to e₁ · to e₂
to (t₁ ⋆⇒ t₂) = to t₁ ⇒ to t₂ 

from : S ⊢ s → Tm desc S s
from (` x)     = `var x
from (λx e)    = ⋆λx from e 
from (e₁ · e₂) = from e₁ ⋆· from e₂ 
from (t₁ ⇒ t₂) = from t₁ ⋆⇒  from t₂

from∘to : (T : Tm desc S s) → from (to T) ≡ T
from∘to (⋆` x) = refl
from∘to (⋆λx e) = cong ⋆λx_ (from∘to e)
from∘to (e₁ ⋆· e₂) = cong₂ _⋆·_ (from∘to e₁) (from∘to e₂)
from∘to (t₁ ⋆⇒ t₂) = cong₂ _⋆⇒_ (from∘to t₁) (from∘to t₂)

to∘from : (T : S ⊢ s) → to (from T) ≡ T
to∘from (` x)     = refl
to∘from (λx e)    = cong λx_ (to∘from e)
to∘from (e₁ · e₂) = cong₂ _·_ (to∘from e₁) (to∘from e₂)
to∘from (t₁ ⇒ t₂) = cong₂ _⇒_ (to∘from t₁) (to∘from t₂)

iso : Tm desc ≃ _⊢_ 
iso = record { 
    to = to 
  ; from = from 
  ; from∘to = from∘to 
  ; to∘from = to∘from }
-- DERIVE END
