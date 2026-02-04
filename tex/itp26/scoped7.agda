{-# OPTIONS --rewriting --double-check --local-confluence-check #-}
module scoped7 where

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

  s s₁ s₂ s′ : Sort 
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


-- mapT : {_→ᴷ_ : Scope → Scope → Set} → 
--   (on : ∀ {S₁ S₂ s} → S₁ →ᴷ S₂ → S₁ ∋ s → S₂ ⊢ s) → 
--   (up : ∀ {S₁ S₂ s} → S₁ →ᴷ S₂ → (s ∷ S₁) →ᴷ (s ∷ S₂)) → 
--   S₁ ⊢ s → 
--   S₁ →ᴷ S₂ →
--   S₂ ⊢ s
-- mapT on up (` x)         σ = on σ x
-- mapT on up (λx e)        σ = λx mapT on up e (up σ)
-- mapT on up (Λα e)        σ = Λα mapT on up e (up σ)
-- mapT on up (∀[α∶ k ] t)  σ = ∀[α∶ mapT on up k σ ] mapT on up t (up σ)
-- mapT on up (e₁ · e₂)     σ = mapT on up e₁ σ · mapT on up e₂ σ
-- mapT on up (e • t)       σ = mapT on up e σ • mapT on up t σ
-- mapT on up (t₁ ⇒ t₂)     σ = mapT on up t₁ σ ⇒ mapT on up t₂ σ
-- mapT on up ★             σ = ★

opaque
  _→ᴿ_ : Scope → Scope → Set
  S₁ →ᴿ S₂ = ∀ {s} → S₁ ∋ s → S₂ ∋ s 

  variable
    ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂ 

  _&ᴿ_ : S₁ ∋ s → (S₁ →ᴿ S₂) → S₂ ∋ s
  x &ᴿ ρ = ρ x

  idᴿ : S →ᴿ S
  idᴿ x = x

  wk : S →ᴿ (s ∷ S)
  wk x = suc x

  _∙ᴿ_ : S₂ ∋ s → (S₁ →ᴿ S₂) → ((s ∷ S₁) →ᴿ S₂)
  (x ∙ᴿ _) zero     = x
  (_ ∙ᴿ ρ) (suc x)  = ρ x

  _;ᴿᴿ_ : (S₁ →ᴿ S₂) → (S₂ →ᴿ S₃) → (S₁ →ᴿ S₃)
  (ρ₁ ;ᴿᴿ ρ₂) x = ρ₂ (ρ₁ x)

  _↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → ((s ∷ S₁) →ᴿ (s ∷ S₂))
  ρ ↑ᴿ _ = zero ∙ᴿ (ρ ;ᴿᴿ wk)

  _⋯ᴿ_ : S₁ ⊢ s → (S₁ →ᴿ S₂) → S₂ ⊢ s
  (` x)         ⋯ᴿ ρ = ` (x &ᴿ ρ)
  (λx e)        ⋯ᴿ ρ = λx (e ⋯ᴿ (ρ ↑ᴿ _))
  (Λα e)        ⋯ᴿ ρ = Λα (e ⋯ᴿ (ρ ↑ᴿ _))
  (∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ (ρ ↑ᴿ _))
  (e₁ · e₂)     ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
  (e • t)       ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
  (t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
  ★             ⋯ᴿ ρ = ★ 
 
opaque
  _→ˢ_ : Scope → Scope → Set
  S₁ →ˢ S₂ = ∀ {s} → S₁ ∋ s → S₂ ⊢ s

  variable
    σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂ 


  _&ˢ_ : S₁ ∋ s → (S₁ →ˢ S₂) → S₂ ⊢ s
  x &ˢ σ = σ x

  idˢ : S →ˢ S
  idˢ = `_

  _∙ˢ_ : S₂ ⊢ s → (S₁ →ˢ S₂) → 
    (s ∷ S₁) →ˢ S₂
  (t ∙ˢ _) zero     = t
  (_ ∙ˢ σ) (suc x)  = σ x

  _;ᴿˢ_ : (S₁ →ᴿ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)
  (ρ₁ ;ᴿˢ σ₂) x = σ₂ (x &ᴿ ρ₁)

  _;ˢᴿ_ : (S₁ →ˢ S₂) → (S₂ →ᴿ S₃) → (S₁ →ˢ S₃)
  (σ₁ ;ˢᴿ ρ₂) x = (σ₁ x) ⋯ᴿ ρ₂

  _↑ˢ_ : (S₁ →ˢ S₂) → ∀ s → ((s ∷ S₁) →ˢ (s ∷ S₂))
  (σ ↑ˢ _) = (` zero) ∙ˢ (σ ;ˢᴿ wk)

  _⋯ˢ_ : S₁ ⊢ s → (S₁ →ˢ S₂) → S₂ ⊢ s
  (` x)         ⋯ˢ σ = x &ˢ σ
  (λx e)        ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ _))
  (Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ _))
  (∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  (e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  (e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  ★             ⋯ˢ σ = ★

  _;ˢˢ_ :  (S₁ →ˢ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)
  (σ₁ ;ˢˢ σ₂) x = (σ₁ x) ⋯ˢ σ₂

postulate
  compositionalityᴿᴿ      : (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂ ≡ (t ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂))                         -- closrr
  compositionalityᴿˢ      : (t ⋯ᴿ ρ₁) ⋯ˢ σ₂ ≡ t ⋯ˢ (ρ₁ ;ᴿˢ σ₂)                           -- closrs
  compositionalityˢᴿ      : (t ⋯ˢ σ₁) ⋯ᴿ ρ₂ ≡ t ⋯ˢ (σ₁ ;ˢᴿ ρ₂)                           -- clossr
  compositionalityˢˢ      : (t ⋯ˢ σ₁) ⋯ˢ σ₂ ≡ (t ⋯ˢ (σ₁ ;ˢˢ σ₂))                         -- closss
  wk-beta                 : x &ᴿ wk {s = s}         ≡ suc x                              -- varshift1
  wk-beta-compᴿ           : x &ᴿ (wk {s = s} ;ᴿᴿ ρ) ≡ suc x &ᴿ ρ                         -- varshift2r
  wk-beta-compˢ           : x &ˢ (wk {s = s} ;ᴿˢ σ) ≡ suc x &ˢ σ                         -- varshift2s
  ext-beta-zeroᴿ          : zero &ᴿ (x ∙ᴿ ρ)           ≡ x                               -- fvarconsr
  ext-beta-zeroˢ          : zero &ˢ (t ∙ˢ σ)           ≡ t                               -- fvarconss
  lift-beta-zeroᴿ         : zero &ᴿ (ρ ↑ᴿ s)           ≡ zero                            -- fvarlift1r
  lift-beta-zeroˢ         : zero &ˢ (σ ↑ˢ s)           ≡ ` zero                          -- fvarlift2s
  lift-beta-zero-compᴿᴿ   : zero &ᴿ ((ρ₁ ↑ᴿ s) ;ᴿᴿ ρ₂) ≡ zero &ᴿ ρ₂                      -- fvarlift2rr
  lift-beta-zero-compᴿˢ   : zero &ˢ ((ρ₁ ↑ᴿ s) ;ᴿˢ σ₂) ≡ zero &ˢ σ₂                      -- fvarlift2rs
  lift-beta-zero-compˢᴿ   : zero &ˢ ((σ₁ ↑ˢ s) ;ˢᴿ ρ₂) ≡ ` (zero &ᴿ ρ₂)                  -- fvarlift2sr
  lift-beta-zero-compˢˢ   : zero &ˢ ((σ₁ ↑ˢ s) ;ˢˢ σ₂) ≡ zero &ˢ σ₂                      -- fvarlift2ss
  ext-beta-sucᴿ           : suc x &ᴿ (x′ ∙ᴿ ρ) ≡ x &ᴿ ρ                                  -- rvarconsr 
  ext-beta-sucˢ           : suc x &ˢ (t ∙ˢ σ)  ≡ x &ˢ σ                                  -- rvarconss 
  lift-beta-sucᴿ          : suc x &ᴿ (ρ ↑ᴿ s)  ≡ x &ᴿ (ρ ;ᴿᴿ wk)                         -- rvarlift1r
  lift-beta-sucˢ          : suc x &ˢ (σ ↑ˢ s)  ≡ x &ˢ (σ ;ˢᴿ wk)                         -- rvarlift1s
  lift-beta-suc-compᴿᴿ    : suc x &ᴿ ((ρ₁ ↑ᴿ s) ;ᴿᴿ ρ₂) ≡ x &ᴿ (ρ₁ ;ᴿᴿ (wk ;ᴿᴿ ρ₂))      -- rvarlift2rr
  lift-beta-suc-compᴿˢ    : suc x &ˢ ((ρ₁ ↑ᴿ s) ;ᴿˢ σ₂) ≡ x &ˢ (ρ₁ ;ᴿˢ (wk ;ᴿˢ σ₂))      -- rvarlift2rs
  lift-beta-suc-compˢᴿ    : suc x &ˢ ((σ₁ ↑ˢ s) ;ˢᴿ ρ₂) ≡ x &ˢ (σ₁ ;ˢᴿ (wk ;ᴿᴿ ρ₂))      -- rvarlift2sr
  lift-beta-suc-compˢˢ    : suc x &ˢ ((σ₁ ↑ˢ s) ;ˢˢ σ₂) ≡ x &ˢ (σ₁ ;ˢˢ (wk ;ᴿˢ σ₂))      -- rvarlift2ss
  comp-assocᴿᴿᴿ           : (ρ₁ ;ᴿᴿ ρ₂) ;ᴿᴿ ρ₃  ≡ ρ₁ ;ᴿᴿ (ρ₂ ;ᴿᴿ ρ₃)                     -- assenvrrr
  comp-assocᴿᴿˢ           : (ρ₁ ;ᴿᴿ ρ₂) ;ᴿˢ σ₃  ≡ ρ₁ ;ᴿˢ (ρ₂ ;ᴿˢ σ₃)                     -- assenvrrs
  comp-assocᴿˢᴿ           : (ρ₁ ;ᴿˢ σ₂) ;ˢᴿ ρ₃  ≡ ρ₁ ;ᴿˢ (σ₂ ;ˢᴿ ρ₃)                     -- assenvrsr
  comp-assocᴿˢˢ           : (ρ₁ ;ᴿˢ σ₂) ;ˢˢ σ₃  ≡ ρ₁ ;ᴿˢ (σ₂ ;ˢˢ σ₃)                     -- assenvrss
  comp-assocˢᴿᴿ           : (σ₁ ;ˢᴿ ρ₂) ;ˢᴿ ρ₃  ≡ σ₁ ;ˢᴿ (ρ₂ ;ᴿᴿ ρ₃)                     -- assenvsrr
  comp-assocˢᴿˢ           : (σ₁ ;ˢᴿ ρ₂) ;ˢˢ σ₃  ≡ σ₁ ;ˢˢ (ρ₂ ;ᴿˢ σ₃)                     -- assenvsrs
  comp-assocˢˢᴿ           : (σ₁ ;ˢˢ σ₂) ;ˢᴿ ρ₃  ≡ σ₁ ;ˢˢ (σ₂ ;ˢᴿ ρ₃)                     -- assenvssr
  comp-assocˢˢˢ           : (σ₁ ;ˢˢ σ₂) ;ˢˢ σ₃  ≡ σ₁ ;ˢˢ (σ₂ ;ˢˢ σ₃)                     -- assenvsss
  distributivityᴿᴿ        : (x ∙ᴿ ρ₁) ;ᴿᴿ ρ₂  ≡ ((x &ᴿ ρ₂) ∙ᴿ (ρ₁ ;ᴿᴿ ρ₂))               -- mapenvrr
  distributivityᴿˢ        : (x ∙ᴿ ρ₁) ;ᴿˢ σ₂  ≡ ((x &ˢ σ₂) ∙ˢ (ρ₁ ;ᴿˢ σ₂))               -- mapenvrs
  distributivityˢᴿ        : (t ∙ˢ σ₁) ;ˢᴿ ρ₂  ≡ ((t ⋯ᴿ ρ₂) ∙ˢ (σ₁ ;ˢᴿ ρ₂))               -- mapenvsr
  distributivityˢˢ        : (t ∙ˢ σ₁) ;ˢˢ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ;ˢˢ σ₂))               -- mapenvss
  interactᴿ               : wk ;ᴿᴿ (x ∙ᴿ ρ) ≡ ρ                                          -- shiftconsr
  interactˢ               : wk ;ᴿˢ (t ∙ˢ σ) ≡ σ                                          -- shiftconss
  wk-liftᴿ                : wk ;ᴿᴿ (ρ ↑ᴿ s) ≡ ρ ;ᴿᴿ wk                                   -- shiftlift1r
  wk-liftˢ                : wk ;ᴿˢ (σ ↑ˢ s) ≡ σ ;ˢᴿ wk                                   -- shiftlift1s
  wk-lift-compᴿᴿ          : wk ;ᴿᴿ ((ρ₁ ↑ᴿ s) ;ᴿᴿ ρ₂) ≡ ρ₁ ;ᴿᴿ (wk  ;ᴿᴿ ρ₂)              -- shiftlift2rr  
  wk-lift-compᴿˢ          : wk ;ᴿˢ ((ρ₁ ↑ᴿ s) ;ᴿˢ σ₂) ≡ ρ₁ ;ᴿˢ (wk  ;ᴿˢ σ₂)              -- shiftlift2rs 
  wk-lift-compˢᴿ          : wk ;ᴿˢ ((σ₁ ↑ˢ s) ;ˢᴿ ρ₂) ≡ σ₁ ;ˢᴿ (wk  ;ᴿᴿ ρ₂)              -- shiftlift2sr  
  wk-lift-compˢˢ          : wk ;ᴿˢ ((σ₁ ↑ˢ s) ;ˢˢ σ₂) ≡ σ₁ ;ˢˢ (wk  ;ᴿˢ σ₂)              -- shiftlift2ss  
  lift-dist-compᴿᴿ        : (ρ₁ ↑ᴿ s) ;ᴿᴿ (ρ₂ ↑ᴿ s) ≡ (ρ₁ ;ᴿᴿ ρ₂) ↑ᴿ s                   -- lift1rr
  lift-dist-compᴿˢ        : (ρ₁ ↑ᴿ s) ;ᴿˢ (σ₂ ↑ˢ s) ≡ (ρ₁ ;ᴿˢ σ₂) ↑ˢ s                   -- lift1rs
  lift-dist-compˢᴿ        : (σ₁ ↑ˢ s) ;ˢᴿ (ρ₂ ↑ᴿ s) ≡ (σ₁ ;ˢᴿ ρ₂) ↑ˢ s                   -- lift1sr
  lift-dist-compˢˢ        : (σ₁ ↑ˢ s) ;ˢˢ (σ₂ ↑ˢ s) ≡ (σ₁ ;ˢˢ σ₂) ↑ˢ s                   -- lift1ss
  lift-dist-comp-compᴿᴿᴿ  : (ρ₁ ↑ᴿ s) ;ᴿᴿ ((ρ₂ ↑ᴿ s) ;ᴿᴿ ρ₃) ≡ ((ρ₁ ;ᴿᴿ ρ₂) ↑ᴿ s) ;ᴿᴿ ρ₃ -- lift2rrr
  lift-dist-comp-compᴿˢᴿ  : (ρ₁ ↑ᴿ s) ;ᴿˢ ((σ₂ ↑ˢ s) ;ˢᴿ ρ₃) ≡ ((ρ₁ ;ᴿˢ σ₂) ↑ˢ s) ;ˢᴿ ρ₃ -- lift2rsr
  lift-dist-comp-compˢᴿᴿ  : (σ₁ ↑ˢ s) ;ˢᴿ ((ρ₂ ↑ᴿ s) ;ᴿᴿ ρ₃) ≡ ((σ₁ ;ˢᴿ ρ₂) ↑ˢ s) ;ˢᴿ ρ₃ -- lift2srr
  lift-dist-comp-compˢˢᴿ  : (σ₁ ↑ˢ s) ;ˢˢ ((σ₂ ↑ˢ s) ;ˢᴿ ρ₃) ≡ ((σ₁ ;ˢˢ σ₂) ↑ˢ s) ;ˢᴿ ρ₃ -- lift2ssr
  lift-dist-comp-compᴿᴿˢ  : (ρ₁ ↑ᴿ s) ;ᴿˢ ((ρ₂ ↑ᴿ s) ;ᴿˢ σ₃) ≡ ((ρ₁ ;ᴿᴿ ρ₂) ↑ᴿ s) ;ᴿˢ σ₃ -- lift2rrs
  lift-dist-comp-compᴿˢˢ  : (ρ₁ ↑ᴿ s) ;ᴿˢ ((σ₂ ↑ˢ s) ;ˢˢ σ₃) ≡ ((ρ₁ ;ᴿˢ σ₂) ↑ˢ s) ;ˢˢ σ₃ -- lift2rss
  lift-dist-comp-compˢᴿˢ  : (σ₁ ↑ˢ s) ;ˢˢ ((ρ₂ ↑ᴿ s) ;ᴿˢ σ₃) ≡ ((σ₁ ;ˢᴿ ρ₂) ↑ˢ s) ;ˢˢ σ₃ -- lift2srs
  lift-dist-comp-compˢˢˢ  : (σ₁ ↑ˢ s) ;ˢˢ ((σ₂ ↑ˢ s) ;ˢˢ σ₃) ≡ ((σ₁ ;ˢˢ σ₂) ↑ˢ s) ;ˢˢ σ₃ -- lift2sss
  lift-extᴿᴿ              : (ρ₁ ↑ᴿ s) ;ᴿᴿ (x ∙ᴿ ρ₂) ≡ x ∙ᴿ (ρ₁ ;ᴿᴿ ρ₂)                   -- liftenvrr
  lift-extᴿˢ              : (ρ₁ ↑ᴿ s) ;ᴿˢ (t ∙ˢ σ₂) ≡ t ∙ˢ (ρ₁ ;ᴿˢ σ₂)                   -- liftenvrr
  lift-extˢᴿ              : (σ₁ ↑ˢ s) ;ˢᴿ (x ∙ᴿ ρ₂) ≡ (` x) ∙ˢ (σ₁ ;ˢᴿ ρ₂)                   -- liftenvrr
  lift-extˢˢ              : (σ₁ ↑ˢ s) ;ˢˢ (t ∙ˢ σ₂) ≡ t ∙ˢ (σ₁ ;ˢˢ σ₂)                   -- liftenvrr
  comp-idₗᴿᴿ              : idᴿ ;ᴿᴿ ρ  ≡ ρ                                               -- idlrr
  comp-idₗᴿˢ              : idᴿ ;ᴿˢ σ  ≡ σ                                               -- idlrs
  comp-idᵣᴿᴿ              : ρ ;ᴿᴿ idᴿ  ≡ ρ                                               -- idrrr
  comp-idᵣˢˢ              : σ ;ˢˢ idˢ  ≡ σ                                               -- idrss
  comp-idᵣˢᴿ              : σ ;ˢᴿ idᴿ  ≡ σ                                               -- idrsr
  comp-idₗˢˢ              : idˢ ;ˢˢ σ  ≡ σ                                               -- idlss
  up-idᴿ                  : idᴿ {S = S} ↑ᴿ s ≡ idᴿ                                       -- liftidr
  up-idˢ                  : idˢ {S = S} ↑ˢ s ≡ idˢ                                       -- liftids
  right-idᴿ               : t ⋯ᴿ idᴿ         ≡ t                                         -- idr
  right-idˢ               : t ⋯ˢ idˢ         ≡ t                                         -- ids

  glue-ren-subst          : (ρ₁ ;ᴿˢ idˢ)         ≡ (idˢ ;ˢᴿ ρ₁)
  glue-comp-subst-ren     : σ₁ ;ˢˢ (idˢ ;ˢᴿ ρ₂)  ≡ σ₁ ;ˢᴿ ρ₂
  glue-comp-ren-subst     : (idˢ ;ˢᴿ ρ₁) ;ˢˢ σ₂  ≡ ρ₁ ;ᴿˢ σ₂
  glue-comp-ren-ren       : ρ₁ ;ᴿˢ (idˢ ;ˢᴿ ρ₂)  ≡ idˢ ;ˢᴿ (ρ₁ ;ᴿᴿ ρ₂)
  coincidence             : t ⋯ˢ (ρ ;ᴿˢ idˢ)  ≡ t ⋯ᴿ ρ
  coincidence-foldⱽ       : t ⋯ˢ ((` x) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ 
                              t ⋯ᴿ (x ∙ᴿ ρ)
  coincidence-foldᵀ       : t ⋯ˢ ((t′ ⋯ᴿ ρ) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ 
                            (t ⋯ˢ (t′ ∙ˢ idˢ)) ⋯ᴿ ρ
  idˢ-def  : x &ˢ idˢ             ≡ ` x
  idᴿ-def  : x &ᴿ idᴿ             ≡ x

{-# REWRITE 
  compositionalityᴿᴿ      
  compositionalityᴿˢ      
  compositionalityˢᴿ      
  compositionalityˢˢ      
  wk-beta                 
  wk-beta-compᴿ           
  wk-beta-compˢ           
  ext-beta-zeroᴿ          
  ext-beta-zeroˢ          
  lift-beta-zeroᴿ         
  lift-beta-zeroˢ         
  lift-beta-zero-compᴿᴿ   
  lift-beta-zero-compᴿˢ   
  lift-beta-zero-compˢᴿ   
  lift-beta-zero-compˢˢ
  ext-beta-sucᴿ           
  ext-beta-sucˢ           
  lift-beta-sucᴿ          
  lift-beta-sucˢ          
  lift-beta-suc-compᴿᴿ    
  lift-beta-suc-compᴿˢ    
  lift-beta-suc-compˢᴿ    
  lift-beta-suc-compˢˢ    
  comp-assocᴿᴿᴿ           
  comp-assocᴿᴿˢ           
  comp-assocᴿˢᴿ           
  comp-assocᴿˢˢ           
  comp-assocˢᴿᴿ           
  comp-assocˢᴿˢ           
  comp-assocˢˢᴿ           
  comp-assocˢˢˢ           
  distributivityᴿᴿ        
  distributivityᴿˢ        
  distributivityˢᴿ        
  distributivityˢˢ        
  interactᴿ               
  interactˢ               
  wk-liftᴿ                
  wk-liftˢ                
  wk-lift-compᴿᴿ          
  wk-lift-compᴿˢ          
  wk-lift-compˢᴿ          
  wk-lift-compˢˢ          
  lift-dist-compᴿᴿ        
  lift-dist-compᴿˢ        
  lift-dist-compˢᴿ        
  lift-dist-compˢˢ        
  lift-dist-comp-compᴿᴿᴿ  
  lift-dist-comp-compᴿˢᴿ  
  lift-dist-comp-compˢᴿᴿ  
  lift-dist-comp-compˢˢᴿ  
  lift-dist-comp-compᴿᴿˢ  
  lift-dist-comp-compᴿˢˢ  
  lift-dist-comp-compˢᴿˢ  
  lift-dist-comp-compˢˢˢ  
  lift-extᴿᴿ              
  lift-extᴿˢ              
  lift-extˢᴿ              
  lift-extˢˢ              
  comp-idₗᴿᴿ              
  comp-idₗᴿˢ              
  comp-idᵣᴿᴿ              
  comp-idᵣˢˢ              
  comp-idᵣˢᴿ              
  comp-idₗˢˢ              
  up-idᴿ                  
  up-idˢ                  
  right-idᴿ               
  right-idˢ 
  idˢ-def
  idᴿ-def 
#-}



{- -- Typing ----------------------------------------------------------------------

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
⊢↑ᴿ ⊢ρ _ _ (zero) _ refl = refl -- refl
⊢↑ᴿ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ t _ (suc x) _ refl = ⊢wkᴿ Γ₂ (x &ᴿ ρ) (wk-drop-∈ x (Γ₁ _ x) ⋯ᴿ ρ) (t ⋯ᴿ ρ) (⊢ρ _ x _ refl)

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
  {! ⊢• (⊢ρ ⊢⋯ᴿ ⊢e) (⊢ρ ⊢⋯ᴿ ⊢t) ((⊢↑ᴿ ⊢ρ _) ⊢⋯ᴿ ⊢t')  !}
⊢ρ ⊢⋯ᴿ ⊢★             = 
  ⊢★

⊢wkˢ : ∀ (Γ : Ctx S) (e : S ⊢ s) (t : S ∶⊢ s) (t′ : S ∶⊢ s′) → Γ ⊢ e ∶ t → (t′ ∷ₜ Γ) ⊢ weaken e ∶ weaken t 
⊢wkˢ Γ _ _ t' ⊢t = (λ s x t ⊢x → ⊢wkᴿ Γ x t t' ⊢x) ⊢⋯ᴿ ⊢t

⊢↑ˢ : σ ∶ Γ₁ →ˢ Γ₂ → (t : S ∶⊢ s) → (σ ↑ˢ s) ∶ t ∷ₜ Γ₁ →ˢ ((t ⋯ˢ σ) ∷ₜ Γ₂)
⊢↑ˢ ⊢σ _ _ (zero) _ refl = ⊢` refl
⊢↑ˢ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ t _ (suc x) _ refl = ⊢wkˢ Γ₂ (x &ˢ σ) (wk-drop-∈ x (Γ₁ _ x) ⋯ˢ σ) (t ⋯ˢ σ) (⊢σ _ x _ refl)

--! SPT
_⊢⋯ˢ_ : ∀ {σ : S₁ →ˢ S₂} {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
  σ ∶ Γ₁ →ˢ Γ₂ →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢ (e ⋯ˢ σ) ∶ (t ⋯ˢ σ)
⊢σ ⊢⋯ˢ (⊢` ⊢x)                  = 
  ⊢σ _ _ _ ⊢x
_⊢⋯ˢ_ {σ = σ} ⊢σ (⊢λ ⊢e)        = 
  ⊢λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢e) -- ⊢λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢e)
_⊢⋯ˢ_ {σ = σ}  ⊢σ (⊢Λ ⊢e)       = 
  ⊢Λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢e)
_⊢⋯ˢ_ {σ = σ} ⊢σ (⊢· ⊢e₁ ⊢e₂)   =
  ⊢· (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e₁) (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e₂)
_⊢⋯ˢ_ {σ = σ} ⊢σ (⊢• ⊢e ⊢t ⊢t') = 
  {! ⊢• (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e) (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢t) 
     (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢t')  !}
_⊢⋯ˢ_ ⊢σ ⊢★             = 
  ⊢★

⊢[] : ∀ {Γ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s} → Γ ⊢ e ∶ t → (e ∙ˢ idˢ) ∶ (t ∷ₜ Γ) →ˢ Γ
⊢[] ⊢t _ zero     _ refl = {! ⊢t   !} -- ⊢t
⊢[] ⊢t _ (suc x)  _ refl = {!   !} -- ⊢` refl

--! SR
subject-reduction : 
  Γ ⊢ e ∶ t →   
  e ↪ e′ → 
  Γ ⊢ e′ ∶ t 
subject-reduction (⊢· {e₂ = e₂} (⊢λ ⊢e₁) ⊢e₂) (β-λ v₂)        = {!   !} -- _⊢⋯ˢ_ {σ = e₂ ∙ˢ idˢ} (⊢[] ⊢e₂) ⊢e₁
subject-reduction (⊢• {t = t} (⊢Λ ⊢e) ⊢t ⊢t') β-Λ             = _⊢⋯ˢ_ {σ = t ∙ˢ idˢ} (⊢[] ⊢t) ⊢e     
subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₁ e₁↪e)     = ⊢· (subject-reduction ⊢e₁ e₁↪e) ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₂ e₂↪e x)   = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e)          
subject-reduction (⊢• ⊢e ⊢t ⊢t')              (ξ-• e↪e')      = ⊢• (subject-reduction ⊢e e↪e') ⊢t ⊢t'  -}