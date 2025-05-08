{-# OPTIONS --rewriting #-}
module Prelude where


open import Data.List using 
  ( List
  ; []
  ; _∷_
  ; _++_
  ) public

open import Variables using
  ( Mode
  ; Var
  ; ¬Var
  ; _∋_
  ; zero
  ; suc 
  ) public

open import Sorts using (module Sorted) public

open import Substitution using 
  ( module Sub
  ) public
  
open import Reflection_ using 
  (
    
  ) public

open import Generics using 
  ( module Generic
  ) public

-- open import Rewriting using
--   ( module Rewrite
--   ) public