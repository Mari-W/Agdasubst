{-# OPTIONS --rewriting #-}
module Examples.STLC-reflection where

open import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Prelude

data Sort : SORT where
  expr : Sort Bind
  type : Sort NoBind

open WithSort Sort
open SortsMeta 

data _⊢_ : SCOPED where
  `_        : S ∋ s → S ⊢ s               
  λx_       : (expr ∷ S) ⊢ expr → S ⊢ expr        
  _·_       : S ⊢ expr → S ⊢ expr → S ⊢ expr      
  _⇒_       : S ⊢ type → S ⊢ type → S ⊢ type 

open import Derive

unquoteDecl syn = deriveSyntax Sort _⊢_ `_ syn