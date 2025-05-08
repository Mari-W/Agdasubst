{-# OPTIONS --rewriting #-}
module Isomorphism where 

open import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Variables

module Iso (Sort : Mode → Set) where
  
  open import Sorts using (module Sorted)
  open Sorted Sort

  record _≃_ (A B : Scoped) : Set₁ where
    field
      to   : ∀ {m S s} → A {m} S s → B S s
      from : ∀ {m S s} → B {m} S s → A S s
      from∘to : ∀ {m S s} (a : A {m} S s) → from (to a) ≡ a
      to∘from : ∀ {m S s} (b : B {m} S s) → to (from b) ≡ b