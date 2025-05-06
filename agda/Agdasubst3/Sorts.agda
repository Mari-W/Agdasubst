module Sorts where

open import Data.List.Membership.Propositional public using (_∈_)
open import Data.List.Relation.Unary.Any public using (here; there)
open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (flip)

pattern zero = here refl 
pattern suc x = there x

_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set ℓ
_∋_ = flip _∈_

data Mode : Set where Var ¬Var : Mode

module Sorted (Sort : Mode → Set) where
  Sorts = List (Sort Var)
  Scoped = ∀ {m} → Sorts → Sort m → Set

  module Isomorphism where
    record _≃_ (A B : Scoped) : Set₁ where
      field
        to   : ∀ {m S s} → A {m} S s → B S s
        from : ∀ {m S s} → B {m} S s → A S s
        from∘to : ∀ {m S s} (a : A {m} S s) → from (to a) ≡ a
        to∘from : ∀ {m S s} (b : B {m} S s) → to (from b) ≡ b

  module Meta where
    variable
      m m₁ m₂ m₃ m′ m₁′ m₂′ m₃′  : Mode
      s s₁ s₂ s₃ s′ s₁′ s₂′ s₃′  : Sort m
      S S₁ S₂ S₃ S′ S₁′ S₂′ S₃′  : Sorts
      x x₁ x₂ x₃ x′ x₁′ x₂′ x₃′  : S ∋ s
