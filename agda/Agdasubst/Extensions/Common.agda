-- Author(s): Marius Weidner (2025)
module Extensions.Common where

open import Common public
open import Lib public

record Library : Set₁ where
  constructor mkLib
  pattern 
  field
    Sort : SORT

  open CommonWithSort Sort public
  open SortsMeta public
  open KitsWithSort Sort public

  field
    syn : Syntax  
  open Syntax syn public

  field
    traversal : Traversal
  open Traversal traversal public

  open KitsMeta public

  field
    compose : Compose 
  open Compose compose public 

open Library {{ ... }}  