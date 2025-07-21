{-# OPTIONS --rewriting --experimental-lazy-instances #-}
module examples where

open import Data.Nat 
open import Data.Fin using (Fin)
open import Data.List
open import Data.List.Membership.Propositional  
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
  fun-exti : ∀{ℓ₁ ℓ₂} → ExtensionalityImplicit  ℓ₁ ℓ₂


--! E >
open import Agda.Builtin.Equality.Rewrite public

--! Rewrite
+–idᵣ : ∀ n → n + 0 ≡ n
+–idᵣ zero     = refl
+–idᵣ (suc n)  = cong suc (+–idᵣ n)

--! RewriteIt
{-# REWRITE +–idᵣ #-}

--! RewriteEx
_ : ∀ {n} → n + 0 ≡ n
_ = refl

--! Default
record Default {ℓ} (A : Set ℓ) : Set ℓ where
  field default : A

--! DefFields
open Default {{...}} public

--! DefInst
instance 
  default–ℕ : Default ℕ
  default–ℕ .default = 0 

--! DefEx
_ : default ≡ 0
_ = refl

--! Opaque
opaque
  forty–two : ℕ
  forty–two = 42
  
--! OpaqueExO 
_ : forty–two ≡ 42
_ = {!  !} -- not provable.

--! OpaqueExT {
opaque   
  unfolding forty–two

  _ : forty–two ≡ 42
  _ = refl
--! }


--! Scoped {
data Kind : Set where
  ★  : Kind

data Type (n : ℕ) : Set where
  `_       : Fin n → Type n 
  ∀[α:_]_  : Type (suc n) → Type n
  _⇒_      : Type n → Type n → Type n

data Expr (n m : ℕ) : Set where
  `_   : Fin m → Expr n m
  λx_  : Expr n (suc m) → Expr n m
  Λα_  : Expr (suc n) m → Expr n m
  _·_  : Expr n m → Expr n m → Expr n m
  _•_  : Expr n m → Type n → Expr n m
--! }

--! MultiSorted {
data Mode : Set where Bind NoBind : Mode

data Sort : Mode → Set where 
  expr type  : Sort Bind
  kind  : Sort NoBind
--! [
variable 
  m : Mode
  s s′ : Sort m
  S S₁ S₂ S₃ S₄ : List (Sort Bind)
--! ]
Sortᴮ = Sort Bind
Scope = List Sortᴮ

data _∋_ : Scope → Sortᴮ → Set where
  zero  : ∀ {S s} → (s ∷ S) ∋ s
  suc   : ∀ {S s s′} → S ∋ s → (s′ ∷ S) ∋ s

Scoped = ∀ {m} → Scope → Sort m → Set
data _⊢_ : Scoped where 
  `_       : S ∋ s → S ⊢ s     
  λx_      : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_      : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_  : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_      : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_      : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_      : S ⊢ type → S ⊢ type → S ⊢ type
  ★        : S ⊢ kind
--! } 

variable
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s

--! Ren {
opaque
  _→ᵣ_ : Scope → Scope → Set
  S₁ →ᵣ S₂ = ∀ {s} → S₁ ∋ s → S₂ ∋ s 

  _&ᵣ_ : S₁ ∋ s → S₁ →ᵣ S₂ → S₂ ∋ s
  x &ᵣ ρ = ρ x
  
  idᵣ : S →ᵣ S
  idᵣ x = x 

  wkᵣ : S →ᵣ (s ∷ S)
  wkᵣ x = suc x

  _∙ᵣ_ : S₂ ∋ s → S₁ →ᵣ S₂ → (s ∷ S₁) →ᵣ S₂
  (x ∙ᵣ _) zero     = x
  (_ ∙ᵣ ρ) (suc x)  = ρ x

  _;ᵣᵣ_ : S₁ →ᵣ S₂ → S₂ →ᵣ S₃ → S₁ →ᵣ S₃
  (ρ₁ ;ᵣᵣ ρ₂) x = ρ₂ (ρ₁ x)

_↑ᵣ_ : S₁ →ᵣ S₂ → ∀ s → (s ∷ S₁) →ᵣ (s ∷ S₂)
ρ ↑ᵣ _ = zero ∙ᵣ (ρ ;ᵣᵣ wkᵣ)

_⋯ᵣ_ : S₁ ⊢ s → S₁ →ᵣ S₂ → S₂ ⊢ s
-- Traversal Laws
(` x)         ⋯ᵣ ρ = ` (x &ᵣ ρ)
(λx e)        ⋯ᵣ ρ = λx (e ⋯ᵣ (ρ ↑ᵣ _))
(Λα e)        ⋯ᵣ ρ = Λα (e ⋯ᵣ (ρ ↑ᵣ _))
(∀[α∶ k ] t)  ⋯ᵣ ρ = ∀[α∶ k ⋯ᵣ ρ ] (t ⋯ᵣ (ρ ↑ᵣ _))
(e₁ · e₂)     ⋯ᵣ ρ = (e₁ ⋯ᵣ ρ) · (e₂ ⋯ᵣ ρ)
(e • t)       ⋯ᵣ ρ = (e ⋯ᵣ ρ) • (t ⋯ᵣ ρ)
(t₁ ⇒ t₂)     ⋯ᵣ ρ = (t₁ ⋯ᵣ ρ) ⇒ (t₂ ⋯ᵣ ρ)
★             ⋯ᵣ ρ = ★ 
--! }

--! Sub {
opaque
  unfolding _→ᵣ_ _&ᵣ_ idᵣ wkᵣ _∙ᵣ_ _;ᵣᵣ_

  _→ₛ_ : Scope → Scope → Set
  S₁ →ₛ S₂ = ∀ {s} → S₁ ∋ s → S₂ ⊢ s

  _&ₛ_ : S₁ ∋ s → S₁ →ₛ S₂ → S₂ ⊢ s
  x &ₛ σ = σ x

  idₛ : S →ₛ S
  idₛ = `_

  _∙ₛ_ : S₂ ⊢ s → S₁ →ₛ S₂ → (s ∷ S₁) →ₛ S₂
  (t ∙ₛ _) zero     = t
  (_ ∙ₛ σ) (suc x)  = σ x
  
  _;ᵣₛ_ : S₁ →ᵣ S₂ → S₂ →ₛ S₃ → S₁ →ₛ S₃
  (ρ₁ ;ᵣₛ σ₂) x = σ₂ (ρ₁ x)

  _;ₛᵣ_ : S₁ →ₛ S₂ → S₂ →ᵣ S₃ → S₁ →ₛ S₃
  (σ₁ ;ₛᵣ ρ₂) x = (σ₁ x) ⋯ᵣ ρ₂
  

_↑ₛ_ : S₁ →ₛ S₂ → ∀ s → (s ∷ S₁) →ₛ (s ∷ S₂)
(σ ↑ₛ _) = (` zero) ∙ₛ (σ ;ₛᵣ wkᵣ)

_⋯ₛ_ : S₁ ⊢ s → S₁ →ₛ S₂ → S₂ ⊢ s
-- Traversal Laws
(` x)         ⋯ₛ σ = (x &ₛ σ)
(λx e)        ⋯ₛ σ = λx (e ⋯ₛ (σ ↑ₛ _))
(Λα e)        ⋯ₛ σ = Λα (e ⋯ₛ (σ ↑ₛ _))
(∀[α∶ k ] t)  ⋯ₛ σ = ∀[α∶ k ⋯ₛ σ ] (t ⋯ₛ (σ ↑ₛ _))
(e₁ · e₂)     ⋯ₛ σ = (e₁ ⋯ₛ σ) · (e₂ ⋯ₛ σ)
(e • t)       ⋯ₛ σ = (e ⋯ₛ σ) • (t ⋯ₛ σ)
(t₁ ⇒ t₂)     ⋯ₛ σ = (t₁ ⋯ₛ σ) ⇒ (t₂ ⋯ₛ σ)
★             ⋯ₛ σ = ★

opaque
  unfolding _→ᵣ_ _&ᵣ_ idᵣ wkᵣ _∙ᵣ_ _;ᵣᵣ_ _→ₛ_ _&ₛ_ idₛ _∙ₛ_ _;ᵣₛ_ _;ₛᵣ_

  _;ₛₛ_ :  S₁ →ₛ S₂ → S₂ →ₛ S₃ → S₁ →ₛ S₃
  (σ₁ ;ₛₛ σ₂) x = (σ₁ x) ⋯ₛ σ₂
--! }

variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᵣ S₂ 
  σ σ₁ σ₂ σ₃ : S₁ →ₛ S₂ 

opaque
  unfolding _→ᵣ_ _&ᵣ_ idᵣ wkᵣ _∙ᵣ_ _;ᵣᵣ_ _→ₛ_ _&ₛ_ idₛ _∙ₛ_ _;ᵣₛ_ _;ₛᵣ_ _;ₛₛ_
  
  --! DefLaws {
  -- Definitional Laws 
  idᵣ-def : x &ᵣ idᵣ ≡ x
  wkᵣ-def : x &ᵣ wkᵣ {s = s′} ≡ suc x
  extZᵣ-def : zero &ᵣ (x ∙ᵣ ρ) ≡ x
  extSᵣ-def : (suc x′) &ᵣ (x ∙ᵣ ρ) ≡ x′ &ᵣ ρ 

  idₛ-def : x &ₛ idₛ ≡ ` x
  extZₛ-def : zero &ₛ (t ∙ₛ σ) ≡ t
  extSₛ-def : (suc x) &ₛ (t ∙ₛ σ) ≡ x &ₛ σ

  compᵣᵣ-def : x &ᵣ (ρ₁ ;ᵣᵣ ρ₂) ≡ (x &ᵣ ρ₁) &ᵣ ρ₂
  compᵣₛ-def : x &ₛ (ρ₁ ;ᵣₛ σ₂) ≡ (x &ᵣ ρ₁) &ₛ σ₂
  compₛᵣ-def : x &ₛ (σ₁ ;ₛᵣ ρ₂) ≡ (x &ₛ σ₁) ⋯ᵣ ρ₂
  compₛₛ-def : x &ₛ (σ₁ ;ₛₛ σ₂) ≡ (x &ₛ σ₁) ⋯ₛ σ₂
  --! }

  --! InteractLaws {
  -- Interaction Laws
  comp-idLᵣᵣ : idᵣ ;ᵣᵣ ρ ≡ ρ;    comp-idLᵣₛ : idᵣ ;ᵣₛ σ ≡ σ
  comp-idRᵣᵣ : ρ ;ᵣᵣ idᵣ ≡ ρ
  comp-idLₛᵣ : idₛ ;ₛᵣ ρ ≡ ρ ;ᵣₛ idₛ;   comp-idLₛₛ : idₛ ;ₛₛ σ ≡ σ   
  comp-idRₛᵣ : σ ;ₛᵣ idᵣ ≡ σ;   comp-idRₛₛ : σ ;ₛₛ idₛ ≡ σ 

  associativityᵣᵣᵣ : (ρ₁ ;ᵣᵣ ρ₂) ;ᵣᵣ ρ₃ ≡ ρ₁ ;ᵣᵣ (ρ₂ ;ᵣᵣ ρ₃)
  associativityᵣᵣₛ : (ρ₁ ;ᵣᵣ ρ₂) ;ᵣₛ σ₃ ≡ ρ₁ ;ᵣₛ (ρ₂ ;ᵣₛ σ₃)
  associativityᵣₛᵣ : (ρ₁ ;ᵣₛ σ₂) ;ₛᵣ ρ₃ ≡ ρ₁ ;ᵣₛ (σ₂ ;ₛᵣ ρ₃)
  associativityᵣₛₛ : (ρ₁ ;ᵣₛ σ₂) ;ₛₛ σ₃ ≡ ρ₁ ;ᵣₛ (σ₂ ;ₛₛ σ₃)
  associativityₛᵣᵣ : (σ₁ ;ₛᵣ ρ₂) ;ₛᵣ ρ₃ ≡ σ₁ ;ₛᵣ (ρ₂ ;ᵣᵣ ρ₃)
  associativityₛᵣₛ : (σ₁ ;ₛᵣ ρ₂) ;ₛₛ σ₃ ≡ σ₁ ;ₛₛ (ρ₂ ;ᵣₛ σ₃)
  associativityₛₛᵣ : (σ₁ ;ₛₛ σ₂) ;ₛᵣ ρ₃ ≡ σ₁ ;ₛₛ (σ₂ ;ₛᵣ ρ₃)
  associativityₛₛₛ : (σ₁ ;ₛₛ σ₂) ;ₛₛ σ₃ ≡ σ₁ ;ₛₛ (σ₂ ;ₛₛ σ₃)

  distributivityᵣᵣ : (x ∙ᵣ ρ₁) ;ᵣᵣ ρ₂ ≡ ((x &ᵣ ρ₂) ∙ᵣ (ρ₁ ;ᵣᵣ ρ₂))
  distributivityᵣₛ : (x ∙ᵣ ρ₁) ;ᵣₛ σ₂ ≡ ((x &ₛ σ₂) ∙ₛ (ρ₁ ;ᵣₛ σ₂))
  distributivityₛᵣ : (t ∙ₛ σ₁) ;ₛᵣ ρ₂ ≡ ((t ⋯ᵣ ρ₂) ∙ₛ (σ₁ ;ₛᵣ ρ₂))
  distributivityₛₛ : (t ∙ₛ σ₁) ;ₛₛ σ₂ ≡ ((t ⋯ₛ σ₂) ∙ₛ (σ₁ ;ₛₛ σ₂))

  interactᵣ : wkᵣ ;ᵣᵣ (x ∙ᵣ ρ) ≡ ρ;   interactₛ : wkᵣ ;ᵣₛ (t ∙ₛ σ) ≡ σ

  η-idᵣ  : zero {S = S} {s = s} ∙ᵣ wkᵣ ≡ idᵣ
  η-idₛ  : (` (zero {S = S} {s = s})) ∙ₛ (wkᵣ ;ᵣₛ idₛ) ≡ idₛ
  η-lawᵣ : (zero &ᵣ ρ) ∙ᵣ (wkᵣ ;ᵣᵣ ρ) ≡ ρ
  η-lawₛ : (zero &ₛ σ) ∙ₛ (wkᵣ ;ᵣₛ σ) ≡ σ
  --! }

  --! MonadLaws {
  -- Monad Laws
  right-idᵣ : (t : S ⊢ s) → t ⋯ᵣ idᵣ ≡ t
  right-idₛ : (t : S ⊢ s) → t ⋯ₛ idₛ ≡ t 

  compositionalityᵣᵣ : (t : S₁ ⊢ s) → (t ⋯ᵣ ρ₁) ⋯ᵣ ρ₂ ≡ t ⋯ᵣ (ρ₁ ;ᵣᵣ ρ₂)
  compositionalityᵣₛ : (t : S₁ ⊢ s) → (t ⋯ᵣ ρ₁) ⋯ₛ σ₂ ≡ t ⋯ₛ (ρ₁ ;ᵣₛ σ₂)
  compositionalityₛᵣ : (t : S₁ ⊢ s) → (t ⋯ₛ σ₁) ⋯ᵣ ρ₂ ≡ t ⋯ₛ (σ₁ ;ₛᵣ ρ₂)
  compositionalityₛₛ : (t : S₁ ⊢ s) → (t ⋯ₛ σ₁) ⋯ₛ σ₂ ≡ t ⋯ₛ (σ₁ ;ₛₛ σ₂)
  --! } 

  -- All proofs
  idᵣ-def = refl
  wkᵣ-def = refl 
  extZᵣ-def = refl
  extSᵣ-def = refl
  idₛ-def = refl
  extZₛ-def = refl
  extSₛ-def = refl

  compᵣᵣ-def = refl
  compᵣₛ-def = refl
  compₛᵣ-def = refl
  compₛₛ-def = refl

  interactᵣ = refl
  interactₛ = refl

  η-idᵣ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
  η-idₛ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
  η-lawᵣ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
  η-lawₛ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))

  distributivityᵣᵣ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
  distributivityᵣₛ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
  distributivityₛᵣ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
  distributivityₛₛ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))

  right-idᵣ (` x)        = refl
  right-idᵣ (λx e)       = cong λx_ (trans (cong (_⋯ᵣ_ {S₂ = expr ∷ _} e) η-idᵣ) (right-idᵣ e))
  right-idᵣ (Λα e)       = cong Λα_ (trans (cong (_⋯ᵣ_ {S₂ = type ∷ _} e) η-idᵣ) (right-idᵣ e))
  right-idᵣ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idᵣ k) (trans (cong (_⋯ᵣ_ {S₂ = type ∷ _} t) η-idᵣ) (right-idᵣ t))
  right-idᵣ (e₁ · e₂)    = cong₂ _·_ (right-idᵣ e₁) (right-idᵣ e₂)
  right-idᵣ (e • t)      = cong₂ _•_ (right-idᵣ e) (right-idᵣ t)
  right-idᵣ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idᵣ t₁) (right-idᵣ t₂)
  right-idᵣ ★            = refl

  right-idₛ (` x)        = refl
  right-idₛ (λx e)       = cong λx_ (trans (cong (_⋯ₛ_ {S₂ = expr ∷ _} e) η-idₛ) (right-idₛ e))
  right-idₛ (Λα e)       = cong Λα_ (trans (cong (_⋯ₛ_ {S₂ = type ∷ _} e) η-idₛ) (right-idₛ e))
  right-idₛ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idₛ k) (trans (cong (_⋯ₛ_ {S₂ = type ∷ _} t) η-idₛ) (right-idₛ t))
  right-idₛ (e₁ · e₂)    = cong₂ _·_ (right-idₛ e₁) (right-idₛ e₂)
  right-idₛ (e • t)      = cong₂ _•_ (right-idₛ e) (right-idₛ t)
  right-idₛ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idₛ t₁) (right-idₛ t₂)
  right-idₛ ★            = refl

  comp-idLᵣᵣ = refl
  comp-idRᵣᵣ = refl
  comp-idLᵣₛ = refl
  comp-idLₛᵣ = refl 
  comp-idLₛₛ = refl
  comp-idRₛᵣ {σ = σ} = fun-exti (fun-ext λ x → right-idᵣ (x &ₛ σ))
  comp-idRₛₛ {σ = σ} = fun-exti (fun-ext λ x → right-idₛ (x &ₛ σ))

  compositionalityᵣᵣ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (` x)        = refl
  compositionalityᵣᵣ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (λx e)       = cong λx_ (trans (compositionalityᵣᵣ {ρ₁ = (ρ₁ ↑ᵣ _)} {ρ₂ = (ρ₂ ↑ᵣ _)} e) (cong (_⋯ᵣ_ {S₂ = expr ∷ _} e) (distributivityᵣᵣ {ρ₂ = (ρ₂ ↑ᵣ _) })))
  compositionalityᵣᵣ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityᵣᵣ {ρ₁ = (ρ₁ ↑ᵣ _)} {ρ₂ = (ρ₂ ↑ᵣ _)} e) (cong (_⋯ᵣ_ {S₂ = type ∷ _} e) (distributivityᵣᵣ {ρ₂ = (ρ₂ ↑ᵣ _) })))
  compositionalityᵣᵣ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᵣᵣ k) (trans (compositionalityᵣᵣ {ρ₁ = (ρ₁ ↑ᵣ _)} {ρ₂ = (ρ₂ ↑ᵣ _)} t) (cong (_⋯ᵣ_ {S₂ = type ∷ _} t) (distributivityᵣᵣ {ρ₂ = (ρ₂ ↑ᵣ _) })))
  compositionalityᵣᵣ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᵣᵣ e₁) (compositionalityᵣᵣ e₂)
  compositionalityᵣᵣ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityᵣᵣ e) (compositionalityᵣᵣ t)
  compositionalityᵣᵣ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᵣᵣ t₁) (compositionalityᵣᵣ t₂)
  compositionalityᵣᵣ {ρ₁ = ρ₁} {ρ₂ = ρ₂} ★            = refl
  
  compositionalityᵣₛ {ρ₁ = ρ₁}  {σ₂ = σ₂} (` x)        = refl
  compositionalityᵣₛ {ρ₁ = ρ₁}  {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityᵣₛ {ρ₁ = (ρ₁ ↑ᵣ _)} {σ₂ = (σ₂ ↑ₛ _)} e) (cong (_⋯ₛ_ {S₂ = expr ∷ _} e) (distributivityᵣₛ {σ₂ = (σ₂ ↑ₛ _)})))
  compositionalityᵣₛ {ρ₁ = ρ₁}  {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityᵣₛ {ρ₁ = (ρ₁ ↑ᵣ _)} {σ₂ = (σ₂ ↑ₛ _)} e) (cong (_⋯ₛ_ {S₂ = type ∷ _} e) (distributivityᵣₛ {σ₂ = (σ₂ ↑ₛ _)})))
  compositionalityᵣₛ {ρ₁ = ρ₁}  {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᵣₛ k) (trans (compositionalityᵣₛ {ρ₁ = (ρ₁ ↑ᵣ _)} {σ₂ = (σ₂ ↑ₛ _)} t) (cong (_⋯ₛ_ {S₂ = type ∷ _} t) (distributivityᵣₛ {σ₂ = (σ₂ ↑ₛ _)})))
  compositionalityᵣₛ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᵣₛ e₁) (compositionalityᵣₛ e₂)
  compositionalityᵣₛ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityᵣₛ e) (compositionalityᵣₛ t)
  compositionalityᵣₛ {ρ₁ = ρ₁}  {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᵣₛ t₁) (compositionalityᵣₛ t₂)
  compositionalityᵣₛ {ρ₁ = ρ₁}  {σ₂ = σ₂} ★            = refl

  compositionalityₛᵣ {σ₁ = σ₁} {ρ₂ = ρ₂} (` x)        = refl
  compositionalityₛᵣ {σ₁ = σ₁} {ρ₂ = ρ₂} (λx e)       = cong λx_ (trans (compositionalityₛᵣ {σ₁ = (σ₁ ↑ₛ _)} {ρ₂ = (ρ₂ ↑ᵣ _)} e) (cong (_⋯ₛ_ {S₂ = expr ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᵣᵣ _) (sym (compositionalityᵣᵣ _)) }))))
  compositionalityₛᵣ {σ₁ = σ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityₛᵣ {σ₁ = (σ₁ ↑ₛ _)} {ρ₂ = (ρ₂ ↑ᵣ _)} e) (cong (_⋯ₛ_ {S₂ = type ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᵣᵣ _) (sym (compositionalityᵣᵣ _)) }))))
  compositionalityₛᵣ {σ₁ = σ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityₛᵣ k) (trans (compositionalityₛᵣ {σ₁ = (σ₁ ↑ₛ _)} {ρ₂ = (ρ₂ ↑ᵣ _)} t) (cong (_⋯ₛ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᵣᵣ _) (sym (compositionalityᵣᵣ _)) })))) 
  compositionalityₛᵣ {σ₁ = σ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityₛᵣ e₁) (compositionalityₛᵣ e₂)
  compositionalityₛᵣ {σ₁ = σ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityₛᵣ e) (compositionalityₛᵣ t)
  compositionalityₛᵣ {σ₁ = σ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityₛᵣ t₁) (compositionalityₛᵣ t₂)
  compositionalityₛᵣ {σ₁ = σ₁} {ρ₂ = ρ₂} ★            = refl

  compositionalityₛₛ {σ₁ = σ₁} {σ₂ = σ₂} (` x)        = refl
  compositionalityₛₛ {σ₁ = σ₁} {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityₛₛ {σ₁ = (σ₁ ↑ₛ _)} {σ₂ = (σ₂ ↑ₛ _)} e) (cong (_⋯ₛ_ {S₂ = expr ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᵣₛ (σ₁ x)) (sym (compositionalityₛᵣ (σ₁ x))) }))))
  compositionalityₛₛ {σ₁ = σ₁} {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityₛₛ {σ₁ = (σ₁ ↑ₛ _)} {σ₂ = (σ₂ ↑ₛ _)} e) (cong (_⋯ₛ_ {S₂ = type ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᵣₛ (σ₁ x)) (sym (compositionalityₛᵣ (σ₁ x))) }))))
  compositionalityₛₛ {σ₁ = σ₁} {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityₛₛ k) (trans (compositionalityₛₛ {σ₁ = (σ₁ ↑ₛ _)} {σ₂ = (σ₂ ↑ₛ _)} t) (cong (_⋯ₛ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᵣₛ (σ₁ x)) (sym (compositionalityₛᵣ (σ₁ x))) }))))
  compositionalityₛₛ {σ₁ = σ₁} {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityₛₛ e₁) (compositionalityₛₛ e₂)
  compositionalityₛₛ {σ₁ = σ₁} {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityₛₛ e) (compositionalityₛₛ t)
  compositionalityₛₛ {σ₁ = σ₁} {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityₛₛ t₁) (compositionalityₛₛ t₂)
  compositionalityₛₛ {σ₁ = σ₁} {σ₂ = σ₂} ★            = refl
  
  associativityᵣᵣᵣ = refl
  associativityᵣᵣₛ = refl
  associativityᵣₛᵣ = refl
  associativityᵣₛₛ = refl 
  associativityₛᵣᵣ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityᵣᵣ (x &ₛ σ₁))
  associativityₛᵣₛ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityᵣₛ (x &ₛ σ₁))
  associativityₛₛᵣ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityₛᵣ (x &ₛ σ₁))
  associativityₛₛₛ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityₛₛ (x &ₛ σ₁))

--! RewriteSys {
{-# REWRITE 
  idᵣ-def wkᵣ-def extZᵣ-def extSᵣ-def
  idₛ-def extZₛ-def extSₛ-def
  compᵣᵣ-def compᵣₛ-def compₛᵣ-def compₛₛ-def
  comp-idLᵣᵣ comp-idLᵣₛ comp-idRᵣᵣ
  comp-idLₛᵣ comp-idLₛₛ comp-idRₛᵣ comp-idRₛₛ
  associativityᵣᵣᵣ associativityᵣᵣₛ 
  associativityᵣₛᵣ associativityᵣₛₛ
  associativityₛᵣᵣ associativityₛᵣₛ 
  associativityₛₛᵣ associativityₛₛₛ
  distributivityᵣᵣ distributivityᵣₛ 
  distributivityₛᵣ distributivityₛₛ
  interactᵣ interactₛ
  η-idᵣ η-idₛ η-lawᵣ η-lawₛ
  right-idᵣ right-idₛ
  compositionalityᵣᵣ compositionalityᵣₛ 
  compositionalityₛᵣ compositionalityₛₛ
#-}
--! }


