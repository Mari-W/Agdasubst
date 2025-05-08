module Sorts where

open import Data.List using (List)
open import Variables

module Sorted (Sort : Mode → Set) where
  Sorts = List (Sort Var)
  Scoped = ∀ {m} → Sorts → Sort m → Set

  module Meta where
    variable
      m m₁ m₂ m₃ m′ m₁′ m₂′ m₃′  : Mode
      s s₁ s₂ s₃ s′ s₁′ s₂′ s₃′  : Sort m
      S S₁ S₂ S₃ S′ S₁′ S₂′ S₃′  : Sorts
      x x₁ x₂ x₃ x′ x₁′ x₂′ x₃′  : S ∋ s
