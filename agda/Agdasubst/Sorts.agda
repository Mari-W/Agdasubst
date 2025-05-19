-- Author: Marius Weidner
module Sorts where 

open import DeBruijn

data Mode : Set where Bind NoBind : Mode

SORT : Set₁
SORT = Mode → Set

module SortsWithSort (Sort : SORT) where
  BindSort = Sort Bind
  NoBindSort = Sort NoBind
  
  Scope = List BindSort
  
  SCOPED = ∀{m} → Scope → Sort m → Set
  SCOPED_BINDABLE = Scope → BindSort → Set
  SCOPED_NOT_BINDABLE = Scope → NoBindSort → Set

  module SortsMeta where
    variable
      m m₁ m₂ m₃ m₄ m′ m₁′ m₂′ m₃′ m₄′  : Mode
      s s₁ s₂ s₃ s₄ s′ s₁′ s₂′ s₃′ s₄′  : Sort m
      S S₁ S₂ S₃ S₄ S′ S₁′ S₂′ S₃′ S₄′  : Scope
      x x₁ x₂ x₃ x₄ x′ x₁′ x₂′ x₃′ x₄′  : S ∋ s
      _∋/⊢_ _∋/⊢₁_ _∋/⊢₂_ _∋/⊢₃_ _∋/⊢₄_ _∋/⊢′_ _∋/⊢₁′_ _∋/⊢₂′_ _∋/⊢₃′_ _∋/⊢₄′_  : SCOPED_BINDABLE
