{-# OPTIONS --rewriting #-}
module Prelude where

open import Data.List using 
  (
    List 
  ; []
  ; _++_
  ) public

open import Sorts using 
  (
    Mode
  ; Var
  ; ¬Var
  ; _∋_
  ; zero
  ; suc 
  ; module Sorted
  ) public

open import Substitution using 
  ( 
    Syntax
  ) public
  
open import Reflection_ using 
  (
    
  ) public

open import Generics using 
  (
    module Generic
  ) public

open import Rewrite using
  (
    module σ-Calculus
  ) public