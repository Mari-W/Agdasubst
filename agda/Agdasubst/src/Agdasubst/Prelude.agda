-- Author(s): Marius Weidner (2025)
module Agdasubst.Prelude where

open import Agdasubst.Common public
open import Agdasubst.Extensions.Common public

module WithSort (Sort : SORT) where
  open CommonWithSort Sort public
  open ExtensionsCommonWithSort Sort public

  open import Agdasubst.Lib 
  open KitsWithSort Sort public 