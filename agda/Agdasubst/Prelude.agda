-- Author(s): Marius Weidner (2025)
module Prelude where

open import Common public
open import Lib 

open import Extensions.Common public

module WithSort (Sort : SORT) where
  open CommonWithSort Sort public
  open KitsWithSort Sort public
