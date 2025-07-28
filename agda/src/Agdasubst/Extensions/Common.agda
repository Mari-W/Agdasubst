-- Author(s): Marius Weidner (2025)
{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module Agdasubst.Extensions.Common where

open import Agdasubst.Common
open import Agdasubst.Lib

record Library : Set₁ where
  constructor mkLib 
  field Sort : Set

  open CommonWithSort Sort
  open KitsWithSort Sort

  field instance syn : Syntax  
  open Syntax syn public

  field instance traversal : Traversal
  open Traversal traversal public

  field instance compose : Compose
  open Compose compose public 

  -- _ = {! id`–def   !}

  -- {-# REWRITE 
  --   id`–def `id–def ;wk-def
  --   extᶻ–def extˢ–def  
  --   idᴿ–def idˢ–def wkᴿ–def wkˢ–def 
-- 
  --   comp–idₗ comp–idᴿ norm–idˢ associativity distributivity interact
  --   η–idᴿ η–idˢ η–lawᴿ η-lawˢ
-- 
  --   compositionality right–id
  -- #-}

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
