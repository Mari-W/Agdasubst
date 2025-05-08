module Variables where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (flip)

pattern zero = here refl 
pattern suc x = there x

_∋_ : ∀ {ℓ} {A : Set ℓ} → List A → A → Set ℓ
_∋_ = flip _∈_

data Mode : Set where Var ¬Var : Mode