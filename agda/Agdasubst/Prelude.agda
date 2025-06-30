-- Author(s): Marius Weidner (2025)
{-# OPTIONS --rewriting #-}
module Prelude where

open import Common 
open import Lib 

module WithSort (Sort : SORT) where
  open CommonWithSort Sort public
  open KitsWithSort Sort public
