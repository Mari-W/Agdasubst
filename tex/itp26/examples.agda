{-# OPTIONS --rewriting --experimental-lazy-instances --allow-unsolved-metas #-}
module examples where

open import Data.List.Membership.Propositional  
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
  fun-exti : ∀{ℓ₁ ℓ₂} → ExtensionalityImplicit  ℓ₁ ℓ₂

open import Data.List hiding ([_])
open import Data.Nat hiding (_⊔_)
open import Data.Fin using (Fin)
open import Data.String using (String)

--! E >
open import Agda.Builtin.Equality.Rewrite public


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