-- Author(s): Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Extensions.Common where

open import Agdasubst.Common
open import Agdasubst.Lib

record Library : Set₁ where
  constructor mkLib 
  field Sort : Set

  open CommonWithSort Sort
  open Meta 
  open KitsWithSort Sort

  field instance syn : Syntax  
  open Syntax syn public

  field instance traversal : Traversal
  open Traversal traversal public
  open KitsMeta 

  field instance compose : Compose
  open Compose compose public 

open Library {{ ... }}  

module ExtensionsCommonWithSort (Sort : Set) where  
  open CommonWithSort Sort
  open KitsWithSort Sort
  instance
    library : {{syn : Syntax}} 
          {{traversal : Syntax.Traversal syn}} 
          {{compose : Syntax.Traversal.Compose traversal}} → 
          Library
    library {{syn}} {{traversal}} {{compose}} = mkLib Sort syn traversal compose  
