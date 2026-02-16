{-# OPTIONS --prop --rewriting --local-confluence-check --double-check #-}
module local where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data Mark : Prop where
  ALWAYS : Mark
  RIGHT-ID : Mark

variable
  M : Mark

record Enable (m : Mark) : Prop where
open Enable {{...}}

instance 
  blanket : Enable ALWAYS
  blanket = _
{-# INCOHERENT blanket #-}

data Nat : Set where 
  zero  : Nat 
  suc   : Nat → Nat

data RightId : Prop where

opaque
  _+_ : ∀ .{{_ : Enable M}} → Nat → Nat → Nat 
  zero   + y = y
  suc x  + y = suc (x + y)

  right-id : ∀ .{{rid : Enable RIGHT-ID}} x → _+_ {{rid}} x zero ≡ x 
  right-id zero    = refl
  right-id (suc x) = cong suc (right-id x)
    where open import Relation.Binary.PropositionalEquality using (cong)

{-# REWRITE right-id #-}

lem : _+_ {{blanket}} ≡ _+_ {RIGHT-ID}
lem = refl

module mod1 where
  private instance _ : Enable RIGHT-ID; _ = _

  _ : ∀ {x} → x + zero ≡ x 
  _ = refl

module mod2 where 
  _ : ∀ {x} → x + zero ≡ x 
  _ = {!  !} -- not provable.