{-# OPTIONS --rewriting --double-check --local-confluence-check #-}
module scoped8-4 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
  fun-exti : ∀{ℓ₁ ℓ₂} → ExtensionalityImplicit  ℓ₁ ℓ₂

open import Data.Nat hiding (_⊔_; _^_)
open import Data.List hiding ([_])
open import Data.Fin using (Fin)
open import Data.String using (String)

--! E >
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

data Mode : Set 
data IsV : Mode → Set 
data Mode where
  V    : Mode
  T>V  : (m : Mode) → IsV m → Mode
data IsV where
  isV : IsV V
pattern T = T>V V isV
variable
  q r u : Mode

data _⊢[_]_ : Scope → Mode → Sort → Set 
_⊢_ = _⊢[ T ]_
_∋_ = _⊢[ V ]_
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
  ★        : S ⊢ kind
--! } 

variable
  e e₁ e₂ e′ : S ⊢ expr
  k k′ : S ⊢ kind
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s
  Q Q′ R U : S ⊢[ q ] s

_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 

variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂

idᴿ : S →ᴿ S
idᴿ _ x = x
{-# INLINE idᴿ #-}

_↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → ((s ∷ S₁) →ᴿ (s ∷ S₂))
(ρ ↑ᴿ _) _ zero    = zero
(ρ ↑ᴿ _) _ (suc x) = suc (ρ _ x)

_;ᴿᴿ_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
_;ᴿᴿ_ = λ z z₁ s z₂ → z₁ s (z s z₂)

wkᴿ : S →ᴿ (s ∷ S)
wkᴿ _ = suc

_⋯ᴿ_ : S₁ ⊢[ q ] s → S₁ →ᴿ S₂ → S₂ ⊢[ T ] s 
_⋯ᴿ_ {q = V} x ρ = ` ρ _ x
(` x)         ⋯ᴿ ρ = ` (ρ _ x)
(λx e)        ⋯ᴿ ρ = λx (e ⋯ᴿ (ρ ↑ᴿ _))
(Λα e)        ⋯ᴿ ρ = Λα (e ⋯ᴿ (ρ ↑ᴿ _))
(∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ (ρ ↑ᴿ _))
(e₁ · e₂)     ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
(e • t)       ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
(t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
★             ⋯ᴿ ρ = ★ 

_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s 

_⊩[_]_ : Scope → Mode → Scope → Set
S₁ ⊩[ _ ] S₂ = S₁ →ˢ S₂ 

variable
  σ σ₁ σ₂ σ₃ : S₁ ⊩[ T ] S₂  

wkˢ : ∀ s → S ⊩[ T ] (s ∷ S)
wkˢ = λ s s₁ z → ` suc z
{-# INLINE wkˢ #-}

idˢ : S ⊩[ T ] S
idˢ = λ s → `_
{-# INLINE idˢ #-}

opaque
  _∙ˢ_ : S₂ ⊢[ T ] s → S₁ ⊩[ T ] S₂ → (s ∷ S₁) ⊩[ T ] S₂  
  --_∙ˢ_ {q = V} t σ _ zero = ` t
  
  _∙ˢ_  t σ _ zero = t
  (t ∙ˢ σ) _ (suc x) = σ _ x 

  _↑ˢ′_ : S₁ ⊩[ T ] S₂ → ∀ s → (s ∷ S₁) ⊩[ T ] (s ∷ S₂)
  σ ↑ˢ′ s = (` zero) ∙ˢ λ s₁ x → (σ _ x) ⋯ᴿ λ s₂ x₁ → suc x₁

  _⋯ˢ_ : S₁ ⊢[ q ] s → S₁ ⊩[ T ] S₂ → S₂ ⊢[ T ] s
  _⋯ˢ_ {q = V} x σ = σ _ x
  (` x) ⋯ˢ σ = σ _ x
  (λx e)        ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ′ _))
  (Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ′ _))
  (∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ′ _))
  (e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  (e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  ★             ⋯ˢ σ = ★

  _;ˢˢ_ : S₁ ⊩[ T ] S₂ → S₂ ⊩[ T ] S₃ → S₁ ⊩[ T ] S₃
  (σ₁ ;ˢˢ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂


_↑ˢ_ : S₁ ⊩[ T ] S₂ → ∀ s → (s ∷ S₁) ⊩[ T ] (s ∷ S₂)
σ ↑ˢ s = (` zero) ∙ˢ (σ ;ˢˢ wkˢ _)
{-# INLINE _↑ˢ_ #-}

postulate
  ext-beta-zeroˢ          : zero ⋯ˢ (t ∙ˢ σ)           ≡ t                               -- fvarconss

  ext-beta-sucˢ           : suc x ⋯ˢ (t ∙ˢ σ)  ≡ (` x) ⋯ˢ σ                                  -- rvarconss 
  comp-assocˢˢˢ           : (σ₁ ;ˢˢ σ₂) ;ˢˢ σ₃  ≡ σ₁ ;ˢˢ (σ₂ ;ˢˢ σ₃)                     -- assenvsss
  distributivityˢˢ        : (t ∙ˢ σ₁) ;ˢˢ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ;ˢˢ σ₂)) 
  distributivityˢᴿ  : (t ∙ˢ σ₁) ;ˢˢ (λ s x → ` (ρ₂ _ x))  ≡ ((t ⋯ᴿ ρ₂) ∙ˢ (σ₁ ;ˢˢ (λ s x → ` (ρ₂ _ x))))              -- mapenvss
  interactˢ               : wkˢ s ;ˢˢ (t ∙ˢ σ) ≡ σ                                        -- shiftconss  
  
  comp-idᵣˢˢ              : σ ;ˢˢ idˢ  ≡ σ                                               -- idrss
  comp-idₗˢˢ              : idˢ ;ˢˢ σ  ≡ σ                                               -- idlss
  
  right-idˢ               : t ⋯ˢ idˢ         ≡ t                                         -- ids

  η-idᴿ  : (` zero {s = s} {S = S}) ∙ˢ (wkˢ _) ≡ idˢ
  η-lawˢ  : (zero  ⋯ˢ σ) ∙ˢ (wkˢ _ ;ˢˢ σ)   ≡ σ
  η-lawᴿ : (zero ⋯ᴿ ρ) ∙ˢ ((wkˢ _ ;ˢˢ (λ s x → ` (ρ _ x)))) ≡ (λ s x → ` (ρ _ x))
  
  η-lawˢ₂  : ((` zero) ⋯ˢ σ) ∙ˢ (wkˢ _ ;ˢˢ σ)   ≡ σ
  trav-1 : (` x)        ⋯ˢ σ ≡ x ⋯ˢ σ
  trav0 : (λx e)        ⋯ˢ σ ≡ λx (e ⋯ˢ (σ ↑ˢ _))
  trav1 : (Λα e)        ⋯ˢ σ ≡ Λα (e ⋯ˢ (σ ↑ˢ _))
  trav2 : (∀[α∶ k ] t)  ⋯ˢ σ ≡ ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  trav3 : (e₁ · e₂)     ⋯ˢ σ ≡ (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  trav4 : (e • t)       ⋯ˢ σ ≡ (e ⋯ˢ σ) • (t ⋯ˢ σ)
  trav5 : (t₁ ⇒ t₂)     ⋯ˢ σ ≡ (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  trav6 : ★             ⋯ˢ σ ≡ ★ 

  compositionalityᴿˢ      : (Q ⋯ᴿ ρ₁) ⋯ˢ σ₂ ≡ (Q ⋯ˢ ((λ s x → ` (ρ₁ _ x)) ;ˢˢ σ₂))                       -- closss
  compositionalityᴿᴿ      : (Q ⋯ᴿ ρ₁) ⋯ᴿ ρ₂ ≡ (Q ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂))                         -- closss
  compositionalityˢᴿ      : (Q ⋯ˢ σ₁) ⋯ᴿ ρ₂ ≡ (Q ⋯ˢ (σ₁ ;ˢˢ λ s x → ` (ρ₂ _ x)))                         -- closss
  compositionalityˢˢ      : (Q ⋯ˢ σ₁) ⋯ˢ σ₂ ≡ (Q ⋯ˢ (σ₁ ;ˢˢ σ₂))                         -- closss

  right-idˢ′               : t ⋯ᴿ idᴿ  ≡ t                                         -- ids 
  up-idˢ′                  : idᴿ {S = S} ↑ᴿ s ≡ idᴿ                                       -- liftids
  coincidence              : Q ⋯ˢ ((λ s x → ` (ρ _ x)))  ≡ Q ⋯ᴿ ρ

  coincidence-foldᵀ  : (Q′ ⋯ˢ ((λ s x → ` (ρ ↑ᴿ type) s x) ;ˢˢ ((Q ⋯ᴿ ρ) ∙ˢ (λ s → `_)))) ≡ 
                         ((Q′ ⋯ˢ ((Q ⋯ᴿ ρ) ∙ˢ (λ s z → ` ρ s z))))

{-# REWRITE 
  coincidence
  coincidence-foldᵀ
  right-idˢ′
  up-idˢ′

  compositionalityˢˢ   
  compositionalityˢᴿ
  compositionalityᴿˢ
  compositionalityᴿᴿ

  ext-beta-zeroˢ          
  ext-beta-sucˢ           
  
  comp-assocˢˢˢ           
  distributivityˢˢ       
  distributivityˢᴿ 
  interactˢ                

  comp-idᵣˢˢ              
  comp-idₗˢˢ
  η-lawˢ
  η-lawᴿ                   
  η-idᴿ 

  right-idˢ       
  trav-1
  trav0
  trav1
  trav2
  trav3
  trav4
  trav5
  trav6
#-}

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

drop-∈ : S ∋ s → Scope → Scope
drop-∈ e xs = drop (suc (depth e)) xs

Ctx : Scope → Set
Ctx S = ∀ s → (x : S ∋ s) → drop-∈ x S ∶⊢ s

[]ₜ : Ctx []
[]ₜ _ ()

_∷ₜ_ : S ∶⊢ s → Ctx S → Ctx (s ∷ S)
(t ∷ₜ Γ) _ zero     = t
(t ∷ₜ Γ) _ (suc x)  = Γ _ x

--!! wkˢ 
weaken : S ⊢ s → (s′ ∷ S) ⊢ s

weaken {s′ = s} t = t ⋯ᴿ λ s₂ x → suc x

--!! Subst
_⟨_⟩ : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s

t ⟨ t′ ⟩ = t ⋯ˢ (t′ ∙ˢ idˢ) 

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
    Γ ⊢ (e • t) ∶ (t′ ⟨ t ⟩)
  ⊢★ : {t : S ⊢ type} →
    Γ ⊢ t ∶ ★

--!! WTR
_∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
-- 
_∶_→ᴿ_ {S₁} {S₂} ρ Γ₁ Γ₂ = ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) → (Γ₁ ∋ x ∶ t) → Γ₂ ∋ (ρ _ x) ∶ t ⋯ᴿ ρ 

--!! WTS
_∶_→ˢ_ : S₁ →ˢ S₂ → Ctx S₁ → Ctx S₂ → Set

_∶_→ˢ_ {S₁} {S₂} σ Γ₁ Γ₂ = ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) → (Γ₁ ∋ x ∶ t) → Γ₂ ⊢ (x ⋯ˢ σ) ∶ (t ⋯ˢ σ) 

--! Semantics {
data Val : S ⊢ expr → Set where
  vλ : Val (λx e)
  vΛ : Val (Λα e)

data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  β-λ :
    Val e₂ →
    ((λx e₁) · e₂) ↪ (e₁ ⟨ e₂ ⟩)
  β-Λ :
    ((Λα e) • t) ↪ (e ⟨ t ⟩)
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

-- postulate
⊢wkᴿ : ∀ (Γ : Ctx S) (x : S ∋ s) t (t′ : S ∶⊢ s′) → Γ ∋ x ∶ t → (t′ ∷ₜ Γ) ∋ (suc x) ∶ (weaken t) 
⊢wkᴿ _ _ _ _ refl = refl

⊢↑ᴿ : ρ ∶ Γ₁ →ᴿ Γ₂ → (t : S₁ ∶⊢ s) → (ρ ↑ᴿ s) ∶ (t ∷ₜ Γ₁) →ᴿ ((t ⋯ᴿ ρ) ∷ₜ Γ₂)
⊢↑ᴿ ⊢ρ _ _ (zero) _ refl = refl -- refl
⊢↑ᴿ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ t _ (suc x) _ refl = ⊢wkᴿ Γ₂ (ρ _ x) (wk-drop-∈ x (Γ₁ _ x) ⋯ᴿ ρ) (t ⋯ᴿ ρ) (⊢ρ _ x _ refl)
-- 
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
  ⊢• (⊢ρ ⊢⋯ᴿ ⊢e) (⊢ρ ⊢⋯ᴿ ⊢t) ((⊢↑ᴿ ⊢ρ _) ⊢⋯ᴿ ⊢t')
⊢ρ ⊢⋯ᴿ ⊢★             = 
  ⊢★

⊢wkˢ : ∀ (Γ : Ctx S) (e : S ⊢ s) (t : S ∶⊢ s) (t′ : S ∶⊢ s′) → Γ ⊢ e ∶ t → (t′ ∷ₜ Γ) ⊢ weaken e ∶ weaken t 
⊢wkˢ Γ e t t' ⊢t = (λ s x t ⊢x → ⊢wkᴿ Γ x t t' ⊢x) ⊢⋯ᴿ ⊢t

⊢↑ˢ : σ ∶ Γ₁ →ˢ Γ₂ → (t : S ∶⊢ s) → (σ ↑ˢ s) ∶ t ∷ₜ Γ₁ →ˢ ((t ⋯ˢ σ) ∷ₜ Γ₂)
⊢↑ˢ ⊢σ _ _ (zero) _ refl = ⊢` refl -- ⊢` refl 
⊢↑ˢ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ t _ (suc x) _ refl = 
  ⊢wkˢ Γ₂ (x ⋯ˢ σ) (wk-drop-∈ x (Γ₁ _ x) ⋯ˢ σ) (t ⋯ˢ σ) (⊢σ _ x _ refl)

_⊢⋯ˢ_ : ∀ {σ : S₁ →ˢ S₂} {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
  σ ∶ Γ₁ →ˢ Γ₂ →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢ (e ⋯ˢ σ) ∶ (t ⋯ˢ σ)
--! SPT
⊢σ ⊢⋯ˢ (⊢` ⊢x)                  = ⊢σ _ _ _ ⊢x 
_⊢⋯ˢ_ {σ = σ} ⊢σ (⊢λ ⊢e)        = ⊢λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢e) 
_⊢⋯ˢ_ {σ = σ}  ⊢σ (⊢Λ ⊢e)       = ⊢Λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢e)
_⊢⋯ˢ_ {σ = σ} ⊢σ (⊢· ⊢e₁ ⊢e₂)   =
  ⊢· (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e₁) (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e₂)
_⊢⋯ˢ_ {σ = σ} ⊢σ (⊢• ⊢e ⊢t ⊢t') = 
   ⊢• (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e) (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢t) 
       (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢t')
_⊢⋯ˢ_ ⊢σ ⊢★             = 
  ⊢★

⊢[] : ∀ {Γ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s} → Γ ⊢ e ∶ t → (e ∙ˢ idˢ) ∶ (t ∷ₜ Γ) →ˢ Γ
⊢[] ⊢t _ zero     _ refl = ⊢t 
⊢[] ⊢t _ (suc x)  _ refl = ⊢` refl 
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