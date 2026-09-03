{-# OPTIONS --rewriting --local-confluence-check --allow-unsolved-metas #-}
module examples where

open import Data.List.Membership.Propositional  
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
  fun-exti : ∀{ℓ₁ ℓ₂} → ExtensionalityImplicit  ℓ₁ ℓ₂
open import Level using (Level)

open import Data.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin using (Fin)
open import Data.String using (String)

--! E >
open import Agda.Builtin.Equality.Rewrite public


data Sort : Set where
  expr : Sort
Scope = List Sort

variable
  s s′     : Sort
  S S₁ S₂  : Scope

data _∋_ : Scope → Sort → Set where
  zero  : (s ∷ S) ∋ s
  suc   : S ∋ s → (s′ ∷ S) ∋ s

data _⊢_ : Scope → Sort → Set where
  `_   : S ∋ s → S ⊢ s
  _·_  : S ⊢ s → S ⊢ s → S ⊢ s

_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s

idᴿ : S →ᴿ S
idᴿ _ x = x

_[_]ᴿ : S₁ ⊢ s → S₁ →ᴿ S₂ → S₂ ⊢ s
(` x)     [ ξ ]ᴿ = ` (ξ _ x)
(t₁ · t₂) [ ξ ]ᴿ = (t₁ [ ξ ]ᴿ) · (t₂ [ ξ ]ᴿ)

--! Rewrite
right-idᴿ : ∀ (t : S ⊢ s) → t [ idᴿ ]ᴿ ≡ t
right-idᴿ (` x)      = refl
right-idᴿ (t₁ · t₂)  = cong₂ _·_ (right-idᴿ t₁) (right-idᴿ t₂)
-- ...

--!! RewriteIt
{-# REWRITE right-idᴿ #-}

--! RewriteEx
_ : ∀ {t : S ⊢ s} → t [ idᴿ ]ᴿ ≡ t
_ = refl

--! Default
record Default (A : Set) : Set where
  field default : A

--!! DefFields
open Default {{...}}

--! DefInst
instance 
  default–Nat : Default Nat
  default–Nat .default = 0 

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
  forty–two : Nat
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

--! Scoped {
data Kind : Set where
  ★  : Kind

data Type (n : Nat) : Set where
  `_       : Fin n → Type n 
  ∀[α:_]_  : Kind → Type (suc n) → Type n
  _⇒_      : Type n → Type n → Type n

data Expr (n m : Nat) : Set where
  `_   : Fin m → Expr n m
  λx_  : Expr n (suc m) → Expr n m
  Λα_  : Expr (suc n) m → Expr n m
  _·_  : Expr n m → Expr n m → Expr n m
  _•_  : Expr n m → Type n → Expr n m
--! }


open import Data.Bool using (Bool; true; false; _∨_)
record DecEq {a} (A : Set a) : Set a where
  constructor mkDecEq
  field
    --! DecEq 
    _≟_ : A → A → Bool 
open DecEq {{...}}

variable
  ℓ : Level


module SetProposal {𝒜 : Set ℓ} where
  𝒮 : Set ℓ 
  --!! SetProp
  𝒮 = 𝒜 → Bool 

  variable A : 𝒮
--! SetOps {
  opaque
    ∅ : 𝒮
    ∅ a = false
    _∪_ : 𝒮 → 𝒮 → 𝒮
    (A ∪ B) a = A a ∨ B a
--! }
    right-id : 
      --!! SetLawEx 
      (A ∪ ∅) ≡ A
    
    right-id {A} = fun-ext proof
      where proof : (a : 𝒜) → (A ∪ ∅) a ≡ A a
            proof a with A a
            ... | true   = refl
            ... | false  = refl

  {-# REWRITE right-id #-}