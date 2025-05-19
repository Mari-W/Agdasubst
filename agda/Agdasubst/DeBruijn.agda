-- Author: Marius Weidner
module DeBruijn where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List; _∷_; []) public
open import Relation.Binary.PropositionalEquality using (refl)
open import Function using (flip)

pattern zero = here refl 
pattern suc x = there x

_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set ℓ
_∋_ = flip _∈_
