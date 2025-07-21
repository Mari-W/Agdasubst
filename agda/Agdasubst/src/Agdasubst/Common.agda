-- Author(s): Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Common where 

open import Agda.Builtin.Equality.Rewrite public
open import Data.List using (List; _∷_; []) public

--! A >

data Mode : Set where Bind NoBind : Mode

--! Tag
data Tag : Set where Ren Sub : Tag

ModeIndexed : Set₁
ModeIndexed = Mode → Set

module _ where 
  open import Level using (Level)
  private variable
    ℓ : Level
    A : Set ℓ
    S : List A 
    s s′ : A

  data _∋_ {ℓ} {A : Set ℓ} : List A → A → Set ℓ where
    --!! Zero 
    zero : (s ∷ S) ∋ s
    --!! Suc 
    suc : S ∋ s → (s′ ∷ S) ∋ s 

module CommonWithSort (Sort : ModeIndexed) where
  --! SortB
  Sortᴮ = Sort Bind

  --! Scope
  Scope = List Sortᴮ

  --! Scoped 
  Scoped = ∀{m} → Scope → Sort m → Set

  module Meta where
    variable
      m m₁ m₂ m₃ m₄ m₅ m′ m₁′ m₂′ m₃′ m₄′ m₅′ : Mode
      k k₁ k₂ k₃ k₄ k₅ k′ k₁′ k₂′ k₃′ k₄′ k₅′ : Tag
      s s₁ s₂ s₃ s₄ s₅ s′ s₁′ s₂′ s₃′ s₄′ s₅′ : Sort m
      S S₁ S₂ S₃ S₄ S₅ S′ S₁′ S₂′ S₃′ S₄′ S₅′ : Scope
      x x₁ x₂ x₃ x₄ x₅ x′ x₁′ x₂′ x₃′ x₄′ x₅′ : S ∋ s
