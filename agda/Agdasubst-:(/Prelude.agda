-- Author: Marius Weidner
{-# OPTIONS --rewriting #-}
module Prelude where

open import Agda.Builtin.Equality.Rewrite public

open import DeBruijn public
open import Sorts public

module WithSort (Sort : SORT) where
  open SortsWithSort Sort public

  open import Kits
  open KitsWithSort Sort public
  