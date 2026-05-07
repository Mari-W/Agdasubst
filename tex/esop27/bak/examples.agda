{-# OPTIONS --rewriting --local-confluence-check --double-check --allow-unsolved-metas #-}
module examples where
open import Agda.Builtin.Equality.Rewrite public
  
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String)

--! E >


--! Rewrite
+–idᵣ : ∀ n → n + 0 ≡ n
+–idᵣ zero     = refl
+–idᵣ (suc n)  = cong suc (+–idᵣ n)

--!! RewriteIt
{-# REWRITE +–idᵣ #-}

--! RewriteEx
_ : ∀ {n} → n + 0 ≡ n
_ = refl

--! Default
record Default (A : Set) : Set where
  field default : A

--!! DefFields
open Default {{...}}

--! DefInst
instance 
  default–ℕ : Default ℕ
  default–ℕ .default = 0 

--! DefInstS
instance 
  default–String : Default String
  default–String .default = ""
--! DefEx
_ : default ≡ 0
_ = refl

--! DefExS
_ : default ≡ ""
_ = refl


--! Opaque
opaque
  forty–two : ℕ
  forty–two = 42
  
--! OpaqueExO 
_ : forty–two ≡ 42
_ = {!   !} -- not provable.

--! OpaqueExT {
opaque   
  unfolding forty–two

  _ : forty–two ≡ 42
  _ = refl
--! }
