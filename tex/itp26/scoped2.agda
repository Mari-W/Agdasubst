{-# OPTIONS --rewriting --double-check --local-confluence-check #-}
module scoped2 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
  fun-exti : ∀{ℓ₁ ℓ₂} → ExtensionalityImplicit  ℓ₁ ℓ₂

open import Data.List hiding ([_])
open import Data.Nat hiding (_⊔_)
open import Data.Fin using (Fin)
open import Data.String using (String)

--! E >
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
data Sort : Set where 
  expr type kind : Sort 
--! [
variable 

  s s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort
--! ]

Scope = List Sort
Scoped = Scope → Sort → Set

data _∋_ : Scoped where
  zero  : ∀ {S s} → (s ∷ S) ∋ s
  suc   : ∀ {S s s′} → S ∋ s → (s′ ∷ S) ∋ s

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
  e e₁ e₂ e′ : S ⊢ expr
  k k′ : S ⊢ kind
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s

--! Ren {
opaque
  _→ᴿ_ : Scope → Scope → Set
  S₁ →ᴿ S₂ = ∀ {s} → S₁ ∋ s → S₂ ∋ s 

  wk : S →ᴿ (s ∷ S)
  wk x = suc x
  -- omitted: idᴿ _&ᴿ_ _∙ᴿ_
  --          _;ᴿᴿ_ _↑ᴿ_ _⋯ᴿ_ 
--! }

  _&ᴿ_ : S₁ ∋ s → (S₁ →ᴿ S₂) → S₂ ∋ s
  x &ᴿ ρ = ρ x

  idᴿ : S →ᴿ S 
  idᴿ x = x 
  
  _∙ᴿ_ : S₂ ∋ s → (S₁ →ᴿ S₂) → ((s ∷ S₁) →ᴿ S₂)
  (x ∙ᴿ _) zero     = x
  (_ ∙ᴿ ρ) (suc x)  = ρ x
  _;ᴿᴿ_ : (S₁ →ᴿ S₂) → (S₂ →ᴿ S₃) → (S₁ →ᴿ S₃)
  (ρ₁ ;ᴿᴿ ρ₂) x = ρ₂ (ρ₁ x)

_↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → ((s ∷ S₁) →ᴿ (s ∷ S₂))
ρ ↑ᴿ _ = zero ∙ᴿ (ρ ;ᴿᴿ wk)
_⋯ᴿ_ : S₁ ⊢ s → (S₁ →ᴿ S₂) → S₂ ⊢ s
-- Traversal Laws
(` x)         ⋯ᴿ ρ = ` (x &ᴿ ρ)
(λx e)        ⋯ᴿ ρ = λx (e ⋯ᴿ (ρ ↑ᴿ _))
(Λα e)        ⋯ᴿ ρ = Λα (e ⋯ᴿ (ρ ↑ᴿ _))
(∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ (ρ ↑ᴿ _))
(e₁ · e₂)     ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
(e • t)       ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
(t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
★             ⋯ᴿ ρ = ★ 

opaque
  unfolding _→ᴿ_ wk 
--! Sub {
  _→ˢ_ : Scope → Scope → Set
  S₁ →ˢ S₂ = ∀ {s} → S₁ ∋ s → S₂ ⊢ s

  _&ˢ_ : S₁ ∋ s → (S₁ →ˢ S₂) → S₂ ⊢ s
  x &ˢ σ = σ x

  idˢ : S →ˢ S
  idˢ = `_

  _∙ˢ_ : S₂ ⊢ s → (S₁ →ˢ S₂) → 
    (s ∷ S₁) →ˢ S₂
  (t ∙ˢ _) zero     = t
  (_ ∙ˢ σ) (suc x)  = σ x
--! }
  _;ᴿˢ_ : (S₁ →ᴿ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)
  (ρ₁ ;ᴿˢ σ₂) x = σ₂ (ρ₁ x)

  _;ˢᴿ_ : (S₁ →ˢ S₂) → (S₂ →ᴿ S₃) → (S₁ →ˢ S₃)
  (σ₁ ;ˢᴿ ρ₂) x = (σ₁ x) ⋯ᴿ ρ₂
-- opaque end  

--! SubInst {
-- omitted: _;ᴿˢ_ _;ˢᴿ_ ...

-- Lifting shorthand (not opaque)
_↑ˢ_ : (S₁ →ˢ S₂) → ∀ s → ((s ∷ S₁) →ˢ (s ∷ S₂))
(σ ↑ˢ _) = (` zero) ∙ˢ (σ ;ˢᴿ wk)

-- Traversal Laws (not opaque)
_⋯ˢ_ : S₁ ⊢ s → (S₁ →ˢ S₂) → S₂ ⊢ s
(` x)         ⋯ˢ σ = (x &ˢ σ)
(λx e)        ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ _))
(Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ _))
(∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
(e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
(e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
(t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
★             ⋯ˢ σ = ★

opaque
  unfolding _→ˢ_ 
  _;ˢˢ_ :  (S₁ →ˢ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)
  (σ₁ ;ˢˢ σ₂) x = (σ₁ x) ⋯ˢ σ₂
--! }

variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂ 
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂ 

module _B where
  -- for coloring only!
  record _d : Set where
    field
      --! MonadLaws {
      -- Monad Laws
      ＋right-idᴿ  : t ⋯ᴿ idᴿ  ≡ t
      ＋right-idˢ  : t ⋯ˢ idˢ  ≡ t

      ＋compositionalityᴿᴿ  : (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂  ≡ t ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂)
      ＋compositionalityᴿˢ  : (t ⋯ᴿ ρ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (ρ₁ ;ᴿˢ σ₂)
      ＋compositionalityˢᴿ  : (t ⋯ˢ σ₁) ⋯ᴿ ρ₂  ≡ t ⋯ˢ (σ₁ ;ˢᴿ ρ₂)
      ＋compositionalityˢˢ  : (t ⋯ˢ σ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (σ₁ ;ˢˢ σ₂)
      --! } 
  opaque 
    unfolding _→ᴿ_ _&ᴿ_ idᴿ wk _∙ᴿ_ _;ᴿᴿ_ _→ˢ_ _&ˢ_ idˢ _∙ˢ_ _;ᴿˢ_ _;ˢᴿ_ _;ˢˢ_

    --! DefLaws {
    -- Definitional Laws 
    ＋idᴿ  : x &ᴿ idᴿ               ≡ x
    ＋wk   : x &ᴿ wk {s = s′}       ≡ suc x
    ext₀ᴿ  : zero &ᴿ (x ∙ᴿ ρ)      ≡ x
    extₛᴿ  : (suc x′) &ᴿ (x ∙ᴿ ρ)  ≡ x′ &ᴿ ρ 

    compᴿᴿ  : x &ᴿ (ρ₁ ;ᴿᴿ ρ₂)  ≡ (x &ᴿ ρ₁) &ᴿ ρ₂
    compˢˢ  : x &ˢ (σ₁ ;ˢˢ σ₂)  ≡ (x &ˢ σ₁) ⋯ˢ σ₂
    -- omitted: ＋idˢ ext₀ˢ extₛˢ
    --          compᴿˢ compˢᴿ
    --! }
    ＋idˢ  : x &ˢ idˢ             ≡ ` x
    ext₀ˢ  : zero &ˢ (t ∙ˢ σ)     ≡ t
    extₛˢ  : (suc x) &ˢ (t ∙ˢ σ)  ≡ x &ˢ σ
    compᴿˢ  : x &ˢ (ρ₁ ;ᴿˢ σ₂)  ≡ (x &ᴿ ρ₁) &ˢ σ₂
    compˢᴿ  : x &ˢ (σ₁ ;ˢᴿ ρ₂)  ≡ (x &ˢ σ₁) ⋯ᴿ ρ₂
    -- Interaction Laws
    comp-idₗᴿᴿ  : idᴿ ;ᴿᴿ ρ  ≡ ρ;    comp-idₗᴿˢ  : idᴿ ;ᴿˢ σ  ≡ σ
    comp-idᵣᴿᴿ  : ρ ;ᴿᴿ idᴿ  ≡ ρ 
    comp-idᵣˢˢ  : σ ;ˢˢ idˢ  ≡ σ;    comp-idᵣˢᴿ  : σ ;ˢᴿ idᴿ  ≡ σ 
    comp-idₗˢˢ  : idˢ ;ˢˢ σ  ≡ σ
    
    associativityᴿᴿᴿ  : (ρ₁ ;ᴿᴿ ρ₂) ;ᴿᴿ ρ₃  ≡ ρ₁ ;ᴿᴿ (ρ₂ ;ᴿᴿ ρ₃)
    associativityᴿᴿˢ  : (ρ₁ ;ᴿᴿ ρ₂) ;ᴿˢ σ₃  ≡ ρ₁ ;ᴿˢ (ρ₂ ;ᴿˢ σ₃)
    associativityᴿˢᴿ  : (ρ₁ ;ᴿˢ σ₂) ;ˢᴿ ρ₃  ≡ ρ₁ ;ᴿˢ (σ₂ ;ˢᴿ ρ₃)
    associativityᴿˢˢ  : (ρ₁ ;ᴿˢ σ₂) ;ˢˢ σ₃  ≡ ρ₁ ;ᴿˢ (σ₂ ;ˢˢ σ₃)
    associativityˢᴿᴿ  : (σ₁ ;ˢᴿ ρ₂) ;ˢᴿ ρ₃  ≡ σ₁ ;ˢᴿ (ρ₂ ;ᴿᴿ ρ₃)
    associativityˢᴿˢ  : (σ₁ ;ˢᴿ ρ₂) ;ˢˢ σ₃  ≡ σ₁ ;ˢˢ (ρ₂ ;ᴿˢ σ₃)
    associativityˢˢᴿ  : (σ₁ ;ˢˢ σ₂) ;ˢᴿ ρ₃  ≡ σ₁ ;ˢˢ (σ₂ ;ˢᴿ ρ₃)
    associativityˢˢˢ  : (σ₁ ;ˢˢ σ₂) ;ˢˢ σ₃  ≡ σ₁ ;ˢˢ (σ₂ ;ˢˢ σ₃)

    distributivityᴿᴿ  : (x ∙ᴿ ρ₁) ;ᴿᴿ ρ₂  ≡ ((x &ᴿ ρ₂) ∙ᴿ (ρ₁ ;ᴿᴿ ρ₂))
    distributivityᴿˢ  : (x ∙ᴿ ρ₁) ;ᴿˢ σ₂  ≡ ((x &ˢ σ₂) ∙ˢ (ρ₁ ;ᴿˢ σ₂))
    distributivityˢᴿ  : (t ∙ˢ σ₁) ;ˢᴿ ρ₂  ≡ ((t ⋯ᴿ ρ₂) ∙ˢ (σ₁ ;ˢᴿ ρ₂))
    distributivityˢˢ  : (t ∙ˢ σ₁) ;ˢˢ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ;ˢˢ σ₂))

    interactᴿ : wk ;ᴿᴿ (x ∙ᴿ ρ) ≡ ρ;   interactˢ : wk ;ᴿˢ (t ∙ˢ σ) ≡ σ

    η-idᴿ    : zero {S = S} {s = s} ∙ᴿ wk  ≡ idᴿ
    η-idˢ  : (` (zero {S = S} {s = s})) ∙ˢ (wk ;ᴿˢ idˢ) ≡ idˢ
    η-lawᴿ  : (zero &ᴿ ρ) ∙ᴿ (wk ;ᴿᴿ ρ)   ≡ ρ
    η-lawˢ  : (zero &ˢ σ) ∙ˢ (wk ;ᴿˢ σ)   ≡ σ
    --! InteractLaws {
    -- Coincidence Laws
    coincidence        : t ⋯ˢ (ρ ;ᴿˢ idˢ)  ≡ t ⋯ᴿ ρ
    coincidence-foldⱽ  : t ⋯ˢ ((` x) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ 
                         t ⋯ᴿ (x ∙ᴿ ρ)
    coincidence-foldᵀ  : t ⋯ˢ ((t′ ⋯ᴿ ρ) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ 
                         (t ⋯ˢ (t′ ∙ˢ idˢ)) ⋯ᴿ ρ
    -- Interaction Laws 
    -- omitted. 

    --! }

 
    right-idᴿ  : (t : S ⊢ s) → t ⋯ᴿ idᴿ  ≡ t
    right-idˢ  : (t : S ⊢ s) → t ⋯ˢ idˢ  ≡ t 
 
    compositionalityᴿᴿ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂  ≡ t ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂)
    compositionalityᴿˢ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (ρ₁ ;ᴿˢ σ₂)
    compositionalityˢᴿ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂  ≡ t ⋯ˢ (σ₁ ;ˢᴿ ρ₂)
    compositionalityˢˢ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (σ₁ ;ˢˢ σ₂)
    
    -- All proofs
    ＋idᴿ = refl 
    ＋wk = refl 
    ext₀ᴿ = refl
    extₛᴿ = refl
    ＋idˢ = refl
    ext₀ˢ = refl
    extₛˢ = refl

    compᴿᴿ = refl
    compᴿˢ = refl
    compˢᴿ = refl
    compˢˢ = refl

    interactᴿ = refl
    interactˢ = refl

    η-idᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    η-idˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    η-lawᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    η-lawˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))

    distributivityᴿᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    distributivityᴿˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    distributivityˢᴿ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
    distributivityˢˢ = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))

    comp-idₗᴿᴿ = refl
    comp-idᵣᴿᴿ = refl
    comp-idₗᴿˢ = refl
    comp-idₗˢˢ = refl
    comp-idᵣˢᴿ {σ = σ} = fun-exti (fun-ext λ x → right-idᴿ (x &ˢ σ))
    comp-idᵣˢˢ {σ = σ} = fun-exti (fun-ext λ x → right-idˢ (x &ˢ σ))

    right-idᴿ (` x)        = refl
    right-idᴿ (λx e)       = cong λx_ (trans (cong (_⋯ᴿ_ {S₂ = expr ∷ _} e) η-idᴿ) (right-idᴿ e))
    right-idᴿ (Λα e)       = cong Λα_ (trans (cong (_⋯ᴿ_ {S₂ = type ∷ _} e) η-idᴿ) (right-idᴿ e))
    right-idᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idᴿ k) (trans (cong (_⋯ᴿ_ {S₂ = type ∷ _} t) η-idᴿ) (right-idᴿ t))
    right-idᴿ (e₁ · e₂)    = cong₂ _·_ (right-idᴿ e₁) (right-idᴿ e₂)
    right-idᴿ (e • t)      = cong₂ _•_ (right-idᴿ e) (right-idᴿ t)
    right-idᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idᴿ t₁) (right-idᴿ t₂)
    right-idᴿ ★            = refl

    right-idˢ (` x)        = refl
    right-idˢ (λx e)       = cong λx_ (trans (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) η-idˢ) (right-idˢ e))
    right-idˢ (Λα e)       = cong Λα_ (trans (cong (_⋯ˢ_ {S₂ = type ∷ _} e) η-idˢ) (right-idˢ e))
    right-idˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idˢ k) (trans (cong (_⋯ˢ_ {S₂ = type ∷ _} t) η-idˢ) (right-idˢ t))
    right-idˢ (e₁ · e₂)    = cong₂ _·_ (right-idˢ e₁) (right-idˢ e₂)
    right-idˢ (e • t)      = cong₂ _•_ (right-idˢ e) (right-idˢ t)
    right-idˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idˢ t₁) (right-idˢ t₂)
    right-idˢ ★            = refl

    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (` x)        = refl
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (λx e)       = cong λx_ (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} e) (cong (_⋯ᴿ_ {S₂ = expr ∷ _} e) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ _) })))
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} e) (cong (_⋯ᴿ_ {S₂ = type ∷ _} e) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ _) })))
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿᴿ k) (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} t) (cong (_⋯ᴿ_ {S₂ = type ∷ _} t) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ _) })))
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿᴿ e₁) (compositionalityᴿᴿ e₂)
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityᴿᴿ e) (compositionalityᴿᴿ t)
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)
    compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} ★            = refl

    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (` x)        = refl
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ _)} {σ₂ = (σ₂ ↑ˢ _)} e) (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ _)})))
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ _)} {σ₂ = (σ₂ ↑ˢ _)} e) (cong (_⋯ˢ_ {S₂ = type ∷ _} e) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ _)})))
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿˢ k) (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ _)} {σ₂ = (σ₂ ↑ˢ _)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ _)})))
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿˢ e₁) (compositionalityᴿˢ e₂)
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityᴿˢ e) (compositionalityᴿˢ t)
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿˢ t₁) (compositionalityᴿˢ t₂)
    compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} ★            = refl

    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (` x)        = refl
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (λx e)       = cong λx_ (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} e) (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) }))))
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} e) (cong (_⋯ˢ_ {S₂ = type ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) }))))
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢᴿ k) (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) })))) 
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityˢᴿ e₁) (compositionalityˢᴿ e₂)
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityˢᴿ e) (compositionalityˢᴿ t)
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢᴿ t₁) (compositionalityˢᴿ t₂)
    compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} ★            = refl

    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (` x)        = refl
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ _)} {σ₂ = (σ₂ ↑ˢ _)} e) (cong (_⋯ˢ_ {S₂ = expr ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ _)} {σ₂ = (σ₂ ↑ˢ _)} e) (cong (_⋯ˢ_ {S₂ = type ∷ _} e) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢˢ k) (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ _)} {σ₂ = (σ₂ ↑ˢ _)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityˢˢ e₁) (compositionalityˢˢ e₂)
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (e • t)      = cong₂ _•_ (compositionalityˢˢ e) (compositionalityˢˢ t)
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢˢ t₁) (compositionalityˢˢ t₂)
    compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} ★            = refl
    
    associativityᴿᴿᴿ = refl
    associativityᴿᴿˢ = refl
    associativityᴿˢᴿ = refl
    associativityᴿˢˢ = refl 
    associativityˢᴿᴿ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityᴿᴿ (x &ˢ σ₁))
    associativityˢᴿˢ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityᴿˢ (x &ˢ σ₁))
    associativityˢˢᴿ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityˢᴿ (x &ˢ σ₁))
    associativityˢˢˢ {σ₁ = σ₁} = fun-exti (fun-ext λ x → compositionalityˢˢ (x &ˢ σ₁))

    -- Coincidence Laws
    coincidence {t = t} {ρ = ρ} = 
      --! CoincidenceProof
      t ⋯ˢ (ρ ;ᴿˢ idˢ)  ≡⟨ sym (compositionalityᴿˢ t) ⟩ 
      (t ⋯ᴿ ρ) ⋯ˢ idˢ   ≡⟨ right-idˢ (t  ⋯ᴿ ρ) ⟩ 
      t ⋯ᴿ ρ            ∎

    coincidence-foldⱽ {t = t} {x = x} {ρ = ρ} = 
      t ⋯ˢ ((` x) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡⟨ cong (_⋯ˢ_ t) (sym (distributivityᴿˢ {ρ₁ = ρ} {σ₂ = idˢ})) ⟩ 
      t ⋯ˢ ((x ∙ᴿ ρ) ;ᴿˢ idˢ)     ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
      (t ⋯ˢ idˢ) ⋯ᴿ (x ∙ᴿ ρ)      ≡⟨ cong (_⋯ᴿ (x ∙ᴿ ρ)) (right-idˢ _) ⟩  
      t ⋯ᴿ (x ∙ᴿ ρ)               ∎
    
    swap-id : (ρ : S₁ →ᴿ S₂) → ρ ;ᴿˢ idˢ ≡ idˢ ;ˢᴿ ρ 
    swap-id _ = refl

    coincidence-foldᵀ {t = t} {t′ = t′} {ρ = ρ} rewrite swap-id ρ = 
      (t ⋯ˢ ((t′ ⋯ᴿ ρ) ∙ˢ (λ x → ` ρ x))) ≡⟨ cong (_⋯ˢ_ t) (sym (distributivityˢᴿ {σ₁ = idˢ} {ρ₂ = ρ})) ⟩ 
      (t ⋯ˢ ((t′ ∙ˢ idˢ) ;ˢᴿ ρ))     ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
      ((t ⋯ˢ (t′ ∙ˢ idˢ)) ⋯ᴿ ρ)      ∎
  -- ＋idᴿ ＋wk ext₀ᴿ extₛᴿ
  -- ＋idˢ ext₀ˢ extₛˢ
  -- compᴿᴿ compᴿˢ compˢᴿ compˢˢ

  --! RewriteSys {
  {-# REWRITE 
    comp-idₗᴿᴿ comp-idₗᴿˢ comp-idᵣᴿᴿ 
    comp-idᵣˢˢ comp-idᵣˢᴿ comp-idₗˢˢ
    associativityᴿᴿᴿ associativityᴿᴿˢ 
    associativityᴿˢᴿ associativityᴿˢˢ
    associativityˢᴿᴿ associativityˢᴿˢ 
    associativityˢˢᴿ associativityˢˢˢ
    distributivityᴿᴿ distributivityᴿˢ 
    distributivityˢᴿ distributivityˢˢ
    interactᴿ interactˢ
    η-idᴿ η-idˢ η-lawᴿ η-lawˢ

    coincidence 
    coincidence-foldⱽ coincidence-foldᵀ

    right-idᴿ right-idˢ
    compositionalityᴿᴿ compositionalityᴿˢ 
    compositionalityˢᴿ compositionalityˢˢ
    
  #-}
  --! }

  -- Typing ----------------------------------------------------------------------

  --! UpArrow
  ↑ᵗ_ : Sort → Sort 
  ↑ᵗ expr = type
  ↑ᵗ type = kind 
  ↑ᵗ kind = kind

  --! TypeOf
  _∶⊢_ : Scope → Sort → Set
  S ∶⊢ s = S ⊢ (↑ᵗ s)
  

  depth : S ∋ s → ℕ
  depth zero     = zero
  depth (suc x)  = suc (depth x)

  -- We need to drop one extra using `suc`, because otherwise the types in a
  -- context are allowed to use themselves.
  drop-∈ : S ∋ s → Scope → Scope
  drop-∈ e xs = drop (suc (depth e)) xs

  Ctx : Scope → Set
  Ctx S = ∀ s → (x : S ∋ s) → drop-∈ x S ∶⊢ s

  []ₜ : Ctx []
  []ₜ _ ()

  _∷ₜ_ : S ∶⊢ s → Ctx S → Ctx (s ∷ S)
  (t ∷ₜ Γ) _ zero     = t
  (t ∷ₜ Γ) _ (suc x)  = Γ _ x

  --!! Wk 
  weaken : S ⊢ s → (s′ ∷ S) ⊢ s

  weaken t = t ⋯ᴿ wk

  --!! Subst
  _[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s

  t [ t′ ] = t ⋯ˢ (t′ ∙ˢ idˢ) 

  wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s′ → S ⊢ s′
  wk-drop-∈ zero t = weaken t 
  wk-drop-∈ (suc x)  t = weaken (wk-drop-∈ x t) 

  wk-telescope : Ctx S → S ∋ s → S ∶⊢ s
  wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

  infix   4  _∋_∶_

  --!! Lookup
  _∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set

  Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

  variable 
    Γ Γ₁ Γ₂ Γ₃ Γ′ Γ₁′ Γ₂′ Γ₃′ : Ctx S

  --! TypingR
  data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
    ⊢` : ∀ {x : S ∋ s} {t} → 
      Γ ∋ x ∶ t →
      Γ ⊢ (` x) ∶ t
    ⊢λ : 
      (t ∷ₜ Γ) ⊢ e ∶ (weaken t′) → 
      Γ ⊢ (λx e) ∶ (t ⇒ t′)
    ⊢Λ : 
      (k ∷ₜ Γ) ⊢ e ∶ t →  
      Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
    ⊢· : 
      Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
      Γ ⊢ e₂ ∶ t₁ →
      Γ ⊢ (e₁ · e₂) ∶ t₂
    ⊢• : 
      Γ ⊢ e ∶ (∀[α∶ k ] t′) →
      Γ ⊢ t ∶ k →
      (k ∷ₜ Γ) ⊢ t′ ∶ k′ →
      Γ ⊢ (e • t) ∶ (t′ [ t ])
    ⊢★ : {t : S ⊢ type} →
      Γ ⊢ t ∶ ★

  --!! WTR
  _∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set

  _∶_→ᴿ_ {S₁} {S₂} ρ Γ₁ Γ₂ = ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) → (Γ₁ ∋ x ∶ t) → Γ₂ ∋ (x &ᴿ ρ) ∶ t ⋯ᴿ ρ 

  --!! WTS
  _∶_→ˢ_ : S₁ →ˢ S₂ → Ctx S₁ → Ctx S₂ → Set

  _∶_→ˢ_ {S₁} {S₂} σ Γ₁ Γ₂ = ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) → (Γ₁ ∋ x ∶ t) → Γ₂ ⊢ (x &ˢ σ) ∶ (t ⋯ˢ σ) 

  --! Semantics {
  data Val : S ⊢ expr → Set where
    vλ : Val (λx e)
    vΛ : Val (Λα e)

  data _↪_ : S ⊢ expr → S ⊢ expr → Set where
    β-λ :
      Val e₂ →
      ((λx e₁) · e₂) ↪ (e₁ [ e₂ ])
    β-Λ :
      ((Λα e) • t) ↪ (e [ t ])
    ξ-·₁ :
      e₁ ↪ e →
      (e₁ · e₂) ↪ (e · e₂)
    ξ-·₂ :
      e₂ ↪ e →
      Val e₁ →
      (e₁ · e₂) ↪ (e₁ · e)
    ξ-• :
      e ↪ e′ →
      (e • t) ↪ (e′ • t)
  --! }

  ⊢wkᴿ : ∀ (Γ : Ctx S) (x : S ∋ s) t (t′ : S ∶⊢ s′) → Γ ∋ x ∶ t → (t′ ∷ₜ Γ) ∋ (suc x) ∶ (weaken t) 
  ⊢wkᴿ _ _ _ _ refl = refl

  ⊢↑ᴿ : ρ ∶ Γ₁ →ᴿ Γ₂ → (t : S₁ ∶⊢ s) → (ρ ↑ᴿ s) ∶ (t ∷ₜ Γ₁) →ᴿ ((t ⋯ᴿ ρ) ∷ₜ Γ₂)
  ⊢↑ᴿ ⊢ρ _ _ (zero) _ refl = {!   !} -- refl
  ⊢↑ᴿ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ t _ (suc x) _ refl = {!   !} -- ⊢wkᴿ Γ₂ (x &ᴿ ρ) (wk-drop-∈ x (Γ₁ _ x) ⋯ᴿ ρ) (t ⋯ᴿ ρ) (⊢ρ _ x _ refl)

  --! RPT
  _⊢⋯ᴿ_ : ∀ {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
    ρ ∶ Γ₁ →ᴿ Γ₂ →
    Γ₁ ⊢ e ∶ t →
    Γ₂ ⊢ (e ⋯ᴿ ρ) ∶ (t ⋯ᴿ ρ)
  ⊢ρ ⊢⋯ᴿ (⊢` ⊢x)    = 
    ⊢` (⊢ρ _ _ _ ⊢x) 
  ⊢ρ ⊢⋯ᴿ (⊢λ ⊢e)        = 
    ⊢λ ((⊢↑ᴿ ⊢ρ _) ⊢⋯ᴿ ⊢e)
  ⊢ρ ⊢⋯ᴿ (⊢Λ ⊢e)        =
    ⊢Λ ((⊢↑ᴿ ⊢ρ _) ⊢⋯ᴿ ⊢e)
  ⊢ρ ⊢⋯ᴿ (⊢· ⊢e₁ ⊢e₂)   = 
    ⊢· (⊢ρ ⊢⋯ᴿ ⊢e₁) (⊢ρ ⊢⋯ᴿ ⊢e₂)
  ⊢ρ ⊢⋯ᴿ (⊢• ⊢e ⊢t ⊢t') = 
    {!   !} -- ⊢• (⊢ρ ⊢⋯ᴿ ⊢e) (⊢ρ ⊢⋯ᴿ ⊢t) ((⊢↑ᴿ ⊢ρ _) ⊢⋯ᴿ ⊢t')
  ⊢ρ ⊢⋯ᴿ ⊢★             = 
    ⊢★

  ⊢wkˢ : ∀ (Γ : Ctx S) (e : S ⊢ s) (t : S ∶⊢ s) (t′ : S ∶⊢ s′) → Γ ⊢ e ∶ t → (t′ ∷ₜ Γ) ⊢ weaken e ∶ weaken t 
  ⊢wkˢ Γ _ _ t' ⊢t = {!   !} -- (λ s x t ⊢x → ⊢wkᴿ Γ x t t' ⊢x) ⊢⋯ᴿ ⊢t

  ⊢↑ˢ : σ ∶ Γ₁ →ˢ Γ₂ → (t : S ∶⊢ s) → (σ ↑ˢ s) ∶ t ∷ₜ Γ₁ →ˢ ((t ⋯ˢ σ) ∷ₜ Γ₂)
  ⊢↑ˢ ⊢σ _ _ (zero) _ refl = {!   !} -- ⊢` refl
  ⊢↑ˢ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ t _ (suc x) _ refl = {!   !} -- ⊢wkˢ Γ₂ (x &ˢ σ) (wk-drop-∈ x (Γ₁ _ x) ⋯ˢ σ) (t ⋯ˢ σ) (⊢σ _ x _ refl)

  --! SPT
  _⊢⋯ˢ_ : ∀ {σ : S₁ →ˢ S₂} {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
    σ ∶ Γ₁ →ˢ Γ₂ →
    Γ₁ ⊢ e ∶ t →
    Γ₂ ⊢ (e ⋯ˢ σ) ∶ (t ⋯ˢ σ)
  ⊢σ ⊢⋯ˢ (⊢` ⊢x)                = 
    ⊢σ _ _ _ ⊢x
  _⊢⋯ˢ_ {σ = σ} ⊢σ (⊢λ ⊢e)        = 
    ⊢λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢e)
  _⊢⋯ˢ_ {σ = σ}  ⊢σ (⊢Λ ⊢e)       = 
    ⊢Λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢e)
  _⊢⋯ˢ_ {σ = σ} ⊢σ (⊢· ⊢e₁ ⊢e₂)   =
    ⊢· (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e₁) (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e₂)
  _⊢⋯ˢ_ {σ = σ} ⊢σ (⊢• ⊢e ⊢t ⊢t') = 
    {!   !} -- ⊢• (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e) (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢t) 
    --    (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢t')
  _⊢⋯ˢ_ ⊢σ ⊢★             = 
    ⊢★

  ⊢[] : ∀ {Γ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s} → Γ ⊢ e ∶ t → (e ∙ˢ idˢ) ∶ (t ∷ₜ Γ) →ˢ Γ
  ⊢[] ⊢t _ zero     _ refl = {!   !} -- ⊢t
  ⊢[] ⊢t _ (suc x)  _ refl = {!   !} -- ⊢` refl

  --! SR
  subject-reduction : 
    Γ ⊢ e ∶ t →   
    e ↪ e′ → 
    Γ ⊢ e′ ∶ t 
  subject-reduction (⊢· {e₂ = e₂} (⊢λ ⊢e₁) ⊢e₂) (β-λ v₂)        = _⊢⋯ˢ_ {σ = e₂ ∙ˢ idˢ} (⊢[] ⊢e₂) ⊢e₁
  subject-reduction (⊢• {t = t} (⊢Λ ⊢e) ⊢t ⊢t') β-Λ             = _⊢⋯ˢ_ {σ = t ∙ˢ idˢ} (⊢[] ⊢t) ⊢e     
  subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₁ e₁↪e)     = ⊢· (subject-reduction ⊢e₁ e₁↪e) ⊢e₂
  subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₂ e₂↪e x)   = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e)          
  subject-reduction (⊢• ⊢e ⊢t ⊢t')              (ξ-• e↪e')      = ⊢• (subject-reduction ⊢e e↪e') ⊢t ⊢t' 