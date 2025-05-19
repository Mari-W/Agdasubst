-- Author: Marius Weidner
module Prelude where

open import DeBruijn public
open import Sorts public

module WithSort (Sort : SORT) where
  open SortsWithSort Sort public

  open import Kits
  open KitsWithSort Sort public

  