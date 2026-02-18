{-# OPTIONS --rewriting --double-check --local-confluence-check #-}
module systemf-kit where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; drop)

data Sort : Set where expr type kind : Sort 

variable 
  s s₁ s₂ s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort
--! ]
Scope = List Sort

data Mode : Set 
data IsV : Mode → Set 

data Mode where
  V    : Mode
  T>V  : (m : Mode) → IsV m → Mode
data IsV where
  isV : IsV V
pattern T = T>V V isV
--! [
variable
  m n o : Mode

--! ]

data _⊢[_]_ : Scope → Mode → Sort → Set 

_⊢_ = _⊢[ T ]_; _∋_ = _⊢[ V ]_

data _⊢[_]_ where 
  zero     : (s ∷ S) ∋ s
  suc      : S ∋ s → (s′ ∷ S) ∋ s
  `_       : S ∋ s → S ⊢ s 
  λx_      : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_      : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_  : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_      : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_      : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_      : S ⊢ type → S ⊢ type → S ⊢ type
  *        : S ⊢ kind
--! }

variable
  e e₁ e₂ e′ : S ⊢ expr
  k k′ : S ⊢ kind
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s
  x/t x/t′ : S ⊢[ m ] s

data _⊑_ : Mode → Mode → Set where
  rfl  : o ⊑ o
  v⊑t  : V ⊑ T

_⊔_ : Mode → Mode → Mode
V ⊔ n  =  n
T ⊔ n  =  T

⊑t   : o ⊑ T
v⊑   : V ⊑ o
⊑m⊔  : m ⊑ (m ⊔ n)
⊑⊔n  : n ⊑ (m ⊔ n)

⊔⊔  : m ⊔ (n ⊔ o) ≡ (m ⊔ n) ⊔ o
⊔v  : m ⊔ V ≡ m
⊔t  : m ⊔ T ≡ T

⊑t {V} = v⊑t
⊑t {T} = rfl

v⊑ {V} = rfl
v⊑ {T} = v⊑t

⊑m⊔ {V} = v⊑
⊑m⊔ {T} = rfl

⊑⊔n {m = V} = rfl
⊑⊔n {m = T} = ⊑t

⊔⊔ {V} = refl
⊔⊔ {T} = refl

⊔v {V} = refl
⊔v {T} = refl

⊔t {V} = refl
⊔t {T} = refl

{-# REWRITE ⊔⊔ ⊔v ⊔t #-} 

zero[_] : ∀ m → (s ∷ S) ⊢[ m ] s
zero[ V ]      =  zero
zero[ T ]      =  ` zero

tm⊑ : m ⊑ o → S ⊢[ m ] s → S ⊢[ o ] s
tm⊑ rfl x  = x
tm⊑ v⊑t i  = ` i

_→[_]_ : Scope → Mode → Scope → Set
S₁ →[ m ] S₂ = ∀ s → S₁ ∋ s → S₂ ⊢[ m ] s 

_→ᴿ_ = _→[ V ]_
_→ˢ_ = _→[ T ]_

opaque
  _↑_ : S₁ →[ m ] S₂ → ∀ s → (s ∷ S₁) →[ m ] (s ∷ S₂)

  _⋯_ : S₁ ⊢[ m ] s → S₁ →[ n ] S₂ → S₂ ⊢[ m ⊔ n ] s
  _⋯_ {m = V} x φ =  (φ _ x)
  (` x)         ⋯ φ = tm⊑ ⊑t (x ⋯ φ)
  (λx e)        ⋯ φ = λx (e ⋯ (φ ↑ _))
  (Λα e)        ⋯ φ = Λα (e ⋯ (φ ↑ _))
  (∀[α∶ k ] t)  ⋯ φ = ∀[α∶ k ⋯ φ ] (t ⋯ (φ ↑ _))
  (e₁ · e₂)     ⋯ φ = (e₁ ⋯ φ) · (e₂ ⋯ φ)
  (e • t)       ⋯ φ = (e ⋯ φ) • (t ⋯ φ)
  (t₁ ⇒ t₂)     ⋯ φ = (t₁ ⋯ φ) ⇒ (t₂ ⋯ φ)
  *             ⋯ φ = *

  id[_] : ∀ m → S →[ m ] S
  id[_] _ _ x = tm⊑ v⊑ x

  _⁺_ : S₁ →[ m ] S₂ → ∀ s → S₁ →[ m ] (s ∷ S₂)

  suc[_]  :  ∀ m → S ⊢[ m ] s → ∀ s′ 
        →  (s′ ∷ S) ⊢[ m ] s
  suc[ V ] x s′  = suc x
  suc[ T ] t s′  = t ⋯ (id[ V ] ⁺ s′)

  (ϕ ⁺ s′) _ x = suc[ _ ] (ϕ _ x) s′

  (ϕ ↑ s′) _ zero    = zero[ _ ]
  (ϕ ↑ s′) _ (suc x) = (ϕ ⁺ s′) _ x

  _∘_ : S₁ →[ m ] S₂ → S₂ →[ n ] S₃ → S₁ →[ m ⊔ n ] S₃
  (ϕ₁ ∘ ϕ₂) _ x = (ϕ₁ _ x) ⋯ ϕ₂

  idᴿ : S →ᴿ S
  idᴿ = id[ V ]

  lift-id : id[_] {S = S} m ↑ s ≡ id[ m ] 
  lift-id {m = V} = ext (λ { zero → refl; (suc x) → refl })
  lift-id {m = T} = ext (λ { zero → refl; (suc x) → refl })

  right-id : ∀ (t : S ⊢ s) → t ⋯ id[ m ]                   ≡ t      
  right-id {m = V} (` x) = refl
  right-id {m = T} (` x) = refl
  right-id (λx e)        = cong λx_ (trans (cong (e ⋯_) lift-id) (right-id e))
  right-id (Λα e)        = cong Λα_ (trans (cong (e ⋯_) lift-id) (right-id e))
  right-id (∀[α∶ k ] t)  = cong₂ ∀[α∶_]_ (right-id k) (trans (cong (t ⋯_) lift-id) (right-id t))
  right-id (e₁ · e₂)     = cong₂ _·_ (right-id e₁) (right-id e₂)
  right-id (e • t)       = cong₂ _•_ (right-id e) (right-id t)
  right-id (t₁ ⇒ t₂)     = cong₂ _⇒_ (right-id t₁) (right-id t₂)
  right-id *             = refl

  