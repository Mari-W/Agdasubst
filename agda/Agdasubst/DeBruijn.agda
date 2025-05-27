-- Author: Marius Weidner
module DeBruijn where

open import Data.List using (List; _∷_; []) public

data _∋_ {ℓ} {A : Set ℓ} : List A → A → Set ℓ where
  zero  : ∀ {xs x} → (x ∷ xs) ∋ x
  suc   : ∀ {xs x y} → xs ∋ x → (y ∷ xs) ∋ x
