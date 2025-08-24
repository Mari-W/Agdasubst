-- Author(s): Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Common where 

open import Agda.Builtin.Equality.Rewrite public
open import Data.List using (List; _∷_; []) public

--! A >

--!! ModeDef
data Mode : Set where Vᴹ Tᴹ : Mode

module CommonWithSort (Sort : Set) where
  Scope = List Sort
  Scoped = Scope → Sort → Set

  module _ where
    private variable 
      s s′ : Sort 
      S : Scope
      
    data _∋_ : Scoped where
      zero : (s ∷ S) ∋ s
      suc : S ∋ s → (s′ ∷ S) ∋ s

  module Meta where
    variable
      M M₁ M₂ M₃ M₄ M₅ M₆ M′ M₁′ M₂′ M₃′ M₄′ M₅′ M₆′ : Mode
      s s₁ s₂ s₃ s₄ s₅ s₆ s′ s₁′ s₂′ s₃′ s₄′ s₅′ s₆′ : Sort
      S S₁ S₂ S₃ S₄ S₅ S₆ S′ S₁′ S₂′ S₃′ S₄′ S₅′ S₆′ : Scope
      x x₁ x₂ x₃ x₄ x₅ x₆ x′ x₁′ x₂′ x₃′ x₄′ x₅′ x₆′ : S ∋ s
