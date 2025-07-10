-- Author(s): Marius Weidner (2025)
module Agdasubst.Common where 

open import Agda.Builtin.Equality.Rewrite public
open import Data.List using (List; _∷_; []) public

data _∋_ {ℓ} {A : Set ℓ} : List A → A → Set ℓ where
  zero  : ∀ {xs x} → (x ∷ xs) ∋ x
  suc   : ∀ {xs x y} → xs ∋ x → (y ∷ xs) ∋ x

data Mode : Set where Bind NoBind : Mode
data Tag : Set where Ren Sub : Tag

SORT : Set₁
SORT = Mode → Set

module CommonWithSort (Sort : SORT) where
  BindSort = Sort Bind
  NoBindSort = Sort NoBind
  
  Scope = List BindSort
  
  SCOPED = ∀{m} → Scope → Sort m → Set
  SCOPED_BINDABLE = Scope → BindSort → Set

  module Meta where
    variable
      m m₁ m₂ m₃ m₄ m′ m₁′ m₂′ m₃′ m₄′ : Mode
      k k₁ k₂ k₃ k₄ k′ k₁′ k₂′ k₃′ k₄′ : Tag
      s s₁ s₂ s₃ s₄ s′ s₁′ s₂′ s₃′ s₄′ : Sort m
      S S₁ S₂ S₃ S₄ S′ S₁′ S₂′ S₃′ S₄′ : Scope
      x x₁ x₂ x₃ x₄ x′ x₁′ x₂′ x₃′ x₄′ : S ∋ s
