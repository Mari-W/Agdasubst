-- Author(s): Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Common where 

open import Agda.Builtin.Equality.Rewrite public
open import Data.List using (List; _∷_; []) public

--! A >

--! Tag
data Tag : Set where Ren Sub : Tag


module CommonWithSort (Sort : Set) where
  --! Scope
  Scope = List Sort

  --! Scoped 
  Scoped = Scope → Sort → Set

  module _ where
    private variable 
      s s′ : Sort 
      S : Scope

    --! Debruijn
    data _∋_ : Scoped where
      --!! Zero 
      zero : (s ∷ S) ∋ s
      --!! Suc 
      suc : S ∋ s → (s′ ∷ S) ∋ s



  module Meta where
    variable
      k k₁ k₂ k₃ k₄ k₅ k′ k₁′ k₂′ k₃′ k₄′ k₅′ : Tag
      s s₁ s₂ s₃ s₄ s₅ s′ s₁′ s₂′ s₃′ s₄′ s₅′ : Sort
      S S₁ S₂ S₃ S₄ S₅ S′ S₁′ S₂′ S₃′ S₄′ S₅′ : Scope
      x x₁ x₂ x₃ x₄ x₅ x′ x₁′ x₂′ x₃′ x₄′ x₅′ : S ∋ s
