module Isomorphism where 

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

      to-injective : ∀ {m S s} {a₁ a₂ : A {m} S s} → to a₁ ≡ to a₂ → a₁ ≡ a₂
      -- from-injective : ∀ {m S s} {b₁ b₂ : B {m} S s} → from b₁ ≡ from b₂ → b₁ ≡ b₂
    
    swap-to-from :  ∀ {m S s} {b : B {m} S s} {a : A {m} S s} → b ≡ to a → from b ≡ a
    swap-to-from refl = from∘to _