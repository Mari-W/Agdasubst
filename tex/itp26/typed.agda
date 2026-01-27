{-# OPTIONS --rewriting --double-check #-}
module typed where

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

--! T >

data Sort : Set where 
  kind type : Sort 

variable 
  s s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort

Scope = List Sort
Scoped = Scope → Sort → Set
data _∋_ : Scoped where
  zero  : ∀ {S s} → (s ∷ S) ∋ s
  suc   : ∀ {S s s′} → S ∋ s → (s′ ∷ S) ∋ s
data _⊢_ : Scoped where 
  `_       : S ∋ s → S ⊢ s     
  ∀[α∶_]_  : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _⇒_      : S ⊢ type → S ⊢ type → S ⊢ type
  ★        : S ⊢ kind


variable
  k k′ : S ⊢ kind
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s

opaque
  _→ᴿ_ : Scope → Scope → Set
  S₁ →ᴿ S₂ = ∀ {s} → S₁ ∋ s → S₂ ∋ s 

  wk : S →ᴿ (s ∷ S)
  wk x = suc x

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
(` x)         ⋯ᴿ ρ = ` (x &ᴿ ρ)
(∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ (ρ ↑ᴿ _))
(t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
★             ⋯ᴿ ρ = ★ 

opaque
  unfolding _→ᴿ_ wk 
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
  
  _;ᴿˢ_ : (S₁ →ᴿ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)
  (ρ₁ ;ᴿˢ σ₂) x = σ₂ (ρ₁ x)

  _;ˢᴿ_ : (S₁ →ˢ S₂) → (S₂ →ᴿ S₃) → (S₁ →ˢ S₃)
  (σ₁ ;ˢᴿ ρ₂) x = (σ₁ x) ⋯ᴿ ρ₂

_↑ˢ_ : (S₁ →ˢ S₂) → ∀ s → ((s ∷ S₁) →ˢ (s ∷ S₂))
(σ ↑ˢ _) = (` zero) ∙ˢ (σ ;ˢᴿ wk)

_⋯ˢ_ : S₁ ⊢ s → (S₁ →ˢ S₂) → S₂ ⊢ s
(` x)         ⋯ˢ σ = (x &ˢ σ)
(∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
(t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
★             ⋯ˢ σ = ★

opaque
  unfolding _→ˢ_ 
  _;ˢˢ_ :  (S₁ →ˢ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)
  (σ₁ ;ˢˢ σ₂) x = (σ₁ x) ⋯ˢ σ₂

variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂ 
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂ 

opaque 
  unfolding _→ᴿ_ _&ᴿ_ idᴿ wk _∙ᴿ_ _;ᴿᴿ_ _→ˢ_ _&ˢ_ idˢ _∙ˢ_ _;ᴿˢ_ _;ˢᴿ_ _;ˢˢ_

  ＋idᴿ  : x &ᴿ idᴿ             ≡ x
  ＋wk   : x &ᴿ wk {s = s′}     ≡ suc x
  ext₀ᴿ  : zero &ᴿ (x ∙ᴿ ρ)     ≡ x
  extₛᴿ  : (suc x′) &ᴿ (x ∙ᴿ ρ) ≡ x′ &ᴿ ρ 

  ＋idˢ  : x &ˢ idˢ             ≡ ` x
  ext₀ˢ  : zero &ˢ (t ∙ˢ σ)     ≡ t
  extₛˢ  : (suc x) &ˢ (t ∙ˢ σ)  ≡ x &ˢ σ

  compᴿᴿ  : x &ᴿ (ρ₁ ;ᴿᴿ ρ₂)  ≡ (x &ᴿ ρ₁) &ᴿ ρ₂
  compᴿˢ  : x &ˢ (ρ₁ ;ᴿˢ σ₂)  ≡ (x &ᴿ ρ₁) &ˢ σ₂
  compˢᴿ  : x &ˢ (σ₁ ;ˢᴿ ρ₂)  ≡ (x &ˢ σ₁) ⋯ᴿ ρ₂
  compˢˢ  : x &ˢ (σ₁ ;ˢˢ σ₂)  ≡ (x &ˢ σ₁) ⋯ˢ σ₂

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

  η-id    : zero {S = S} {s = s} ∙ᴿ wk  ≡ idᴿ
  η-idˢ  : (` (zero {S = S} {s = s})) ∙ˢ (wk ;ᴿˢ idˢ) ≡ idˢ
  η-lawᴿ  : (zero &ᴿ ρ) ∙ᴿ (wk ;ᴿᴿ ρ)   ≡ ρ
  η-lawˢ  : (zero &ˢ σ) ∙ˢ (wk ;ᴿˢ σ)   ≡ σ

  coincidence        : t ⋯ˢ (ρ ;ᴿˢ idˢ)  ≡ t ⋯ᴿ ρ
  coincidence-foldⱽ  : t ⋯ˢ ((` x) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ t ⋯ᴿ (x ∙ᴿ ρ)
  coincidence-foldᵀ  : t ⋯ˢ ((t′ ⋯ᴿ ρ) ∙ˢ (ρ ;ᴿˢ idˢ)) ≡ (t ⋯ˢ (t′ ∙ˢ idˢ)) ⋯ᴿ ρ
 
  right-idᴿ  : (t : S ⊢ s) → t ⋯ᴿ idᴿ  ≡ t
  right-idˢ  : (t : S ⊢ s) → t ⋯ˢ idˢ  ≡ t 
 
  compositionalityᴿᴿ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂  ≡ t ⋯ᴿ (ρ₁ ;ᴿᴿ ρ₂)
  compositionalityᴿˢ  : (t : S₁ ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (ρ₁ ;ᴿˢ σ₂)
  compositionalityˢᴿ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂  ≡ t ⋯ˢ (σ₁ ;ˢᴿ ρ₂)
  compositionalityˢˢ  : (t : S₁ ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (σ₁ ;ˢˢ σ₂)
    
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

  η-id = fun-exti (fun-ext (λ { zero → refl ; (suc x) → refl }))
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
  right-idᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idᴿ k) (trans (cong (_⋯ᴿ_ {S₂ = type ∷ _} t) η-id) (right-idᴿ t))
  right-idᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idᴿ t₁) (right-idᴿ t₂)
  right-idᴿ ★            = refl

  right-idˢ (` x)        = refl
  right-idˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idˢ k) (trans (cong (_⋯ˢ_ {S₂ = type ∷ _} t) η-idˢ) (right-idˢ t))
  right-idˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idˢ t₁) (right-idˢ t₂)
  right-idˢ ★            = refl

  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (` x)        = refl
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿᴿ k) (trans (compositionalityᴿᴿ {ρ₁ = (ρ₁ ↑ᴿ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} t) (cong (_⋯ᴿ_ {S₂ = type ∷ _} t) (distributivityᴿᴿ {ρ₂ = (ρ₂ ↑ᴿ _) })))
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} ★            = refl

  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (` x)        = refl
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿˢ k) (trans (compositionalityᴿˢ {ρ₁ = (ρ₁ ↑ᴿ _)} {σ₂ = (σ₂ ↑ˢ _)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (distributivityᴿˢ {σ₂ = (σ₂ ↑ˢ _)})))
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿˢ t₁) (compositionalityᴿˢ t₂)
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} ★            = refl

  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (` x)        = refl
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢᴿ k) (trans (compositionalityˢᴿ {σ₁ = (σ₁ ↑ˢ _)} {ρ₂ = (ρ₂ ↑ᴿ _)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿᴿ _) (sym (compositionalityᴿᴿ _)) })))) 
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢᴿ t₁) (compositionalityˢᴿ t₂)
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} ★            = refl

  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (` x)        = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢˢ k) (trans (compositionalityˢˢ {σ₁ = (σ₁ ↑ˢ _)} {σ₂ = (σ₂ ↑ˢ _)} t) (cong (_⋯ˢ_ {S₂ = type ∷ _} t) (fun-exti (fun-ext λ { zero → refl; (suc x) → trans (compositionalityᴿˢ (σ₁ x)) (sym (compositionalityˢᴿ (σ₁ x))) }))))
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

  coincidence {t = t} {ρ = ρ} = 
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


{-# REWRITE 
  ＋idᴿ ＋wk ext₀ᴿ extₛᴿ
  ＋idˢ ext₀ˢ extₛˢ
  compᴿᴿ compᴿˢ compˢᴿ compˢˢ

  comp-idₗᴿᴿ comp-idₗᴿˢ comp-idᵣᴿᴿ 
  comp-idᵣˢˢ comp-idᵣˢᴿ comp-idₗˢˢ
  associativityᴿᴿᴿ associativityᴿᴿˢ 
  associativityᴿˢᴿ associativityᴿˢˢ
  associativityˢᴿᴿ associativityˢᴿˢ 
  associativityˢˢᴿ associativityˢˢˢ
  distributivityᴿᴿ distributivityᴿˢ 
  distributivityˢᴿ distributivityˢˢ
  interactᴿ interactˢ
  η-id η-lawᴿ η-lawˢ

  coincidence 
  coincidence-foldⱽ coincidence-foldᵀ

  right-idᴿ right-idˢ
  compositionalityᴿᴿ compositionalityᴿˢ 
  compositionalityˢᴿ compositionalityˢˢ
    
#-}

--!! Weaken
weaken : S ⊢ s → (s′ ∷ S) ⊢ s

weaken t = t ⋯ᴿ wk

--!! Subst
_[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s

t [ t′ ] = t ⋯ˢ (t′ ∙ˢ idˢ) 

-- Typing ----------------------------------------------------------------------

data Ctx : Scope → Set where
  ∅     : Ctx []
  _⸴_   : Ctx S → S ⊢ type → Ctx S          
  _⸴★  : Ctx S → Ctx (type ∷ S) 

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx S

data _∈_ : S ⊢ type → Ctx S → Set where
  zero   : t ∈ (Γ ⸴ t)
  suc  : t ∈ Γ → t ∈ (Γ ⸴ t′)
  suc★  : t ∈ Γ → (weaken t) ∈ (Γ ⸴★)

data Expr {S : Scope} (Γ : Ctx S) : S ⊢ type → Set where
  `_    : t ∈ Γ → Expr Γ t
  λx_   : Expr (Γ ⸴ t₁) t₂ → Expr Γ (t₁ ⇒ t₂) 
  Λα_   : {t : (type ∷ S) ⊢ type} → Expr (Γ ⸴★) t → Expr Γ (∀[α∶ ★ ] t)
  _·_   : Expr Γ (t₁ ⇒ t₂) → Expr Γ t₁ → Expr Γ t₂
  _∙_   : {t : (type ∷ S) ⊢ type} → Expr Γ (∀[α∶ ★ ] t) → (t' : S ⊢ type) → Expr Γ (t [ t' ])

_→ᴿᴱ[_]_ : Ctx S₁ → (S₁ →ᴿ S₂) → Ctx S₂ → Set
Γ₁ →ᴿᴱ[ ρ ] Γ₂ = ∀ t → t ∈ Γ₁ → (t ⋯ᴿ ρ) ∈ Γ₂

idᴿᴱ : Γ →ᴿᴱ[ idᴿ ] Γ
idᴿᴱ _ x = x

wkᴱ : Γ →ᴿᴱ[ idᴿ ] (Γ ⸴ t) 
wkᴱ _ x = suc x 

wkᴱ★ : Γ →ᴿᴱ[ wk ] (Γ ⸴★) 
wkᴱ★ _ x = suc★ x

_∙ᴿᴱ_ : (t ⋯ᴿ ρ) ∈ Γ₂ → (Γ₁ →ᴿᴱ[ ρ ] Γ₂) → 
        (Γ₁ ⸴ t) →ᴿᴱ[ ρ ] Γ₂
(x ∙ᴿᴱ _) _ zero = x
(_ ∙ᴿᴱ ρᴱ) _ (suc x) = ρᴱ _ x 

_∙ᴿᴱ★_ : {ρ : S₁ →ᴿ S₂} → (x : S₂ ∋ type) → (Γ₁ →ᴿᴱ[ ρ ] Γ₂) → (Γ₁ ⸴★) →ᴿᴱ[ x ∙ᴿ ρ ] Γ₂
(_ ∙ᴿᴱ★ ρᴱ) _ (suc★ x) = ρᴱ _ x 

_;ᴿᴿᴱ_ : (Γ₁ →ᴿᴱ[ ρ₁ ] Γ₂) → (Γ₂ →ᴿᴱ[ ρ₂ ] Γ₃) → (Γ₁ →ᴿᴱ[ ρ₁ ;ᴿᴿ ρ₂ ] Γ₃)
(ρ₁ ;ᴿᴿᴱ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_↑ᴿᴱ_ : (Γ₁ →ᴿᴱ[ ρ ] Γ₂) → ∀ t → (Γ₁ ⸴ t) →ᴿᴱ[ ρ ] (Γ₂ ⸴ (t ⋯ᴿ ρ))
(ρᴱ ↑ᴿᴱ t) = zero ∙ᴿᴱ (_;ᴿᴿᴱ_ {ρ₂ = idᴿ} ρᴱ wkᴱ)

_↑ᴿᴱ★ : (Γ₁ →ᴿᴱ[ ρ ] Γ₂) → (Γ₁ ⸴★) →ᴿᴱ[ ρ ↑ᴿ type ] (Γ₂ ⸴★)
ρᴱ ↑ᴿᴱ★ = zero ∙ᴿᴱ★ (ρᴱ ;ᴿᴿᴱ wkᴱ★)
  
_⋯ᴿᴱ[_]_ : {t : S₁ ⊢ type} {Γ₂ : Ctx S₂} → 
  Expr Γ₁ t → (ρ : S₁ →ᴿ S₂) → (ρᴱ : Γ₁ →ᴿᴱ[ ρ ] Γ₂) → Expr Γ₂ (t ⋯ᴿ ρ)
(` x)        ⋯ᴿᴱ[ ρ ] ρᴱ = ` (ρᴱ _ x)
(λx e)       ⋯ᴿᴱ[ ρ ] ρᴱ = λx (e ⋯ᴿᴱ[ ρ ] (ρᴱ ↑ᴿᴱ _))
(Λα e)       ⋯ᴿᴱ[ ρ ] ρᴱ = Λα (e ⋯ᴿᴱ[ ρ ↑ᴿ _ ] (ρᴱ ↑ᴿᴱ★))
(e₁ · e₂)    ⋯ᴿᴱ[ ρ ] ρᴱ = (e₁ ⋯ᴿᴱ[ ρ ] ρᴱ) · (e₂ ⋯ᴿᴱ[ ρ ] ρᴱ)
_∙_ {t = t} e t′ ⋯ᴿᴱ[ ρ ] ρᴱ = (e ⋯ᴿᴱ[ ρ ] ρᴱ) ∙ (t′ ⋯ᴿ ρ)

weakenᴱ : Expr Γ t → Expr (Γ ⸴ t′) t
weakenᴱ e = e ⋯ᴿᴱ[ idᴿ ] wkᴱ
  
weakenᴱ★ : Expr Γ t → Expr (Γ ⸴★) (weaken t)
weakenᴱ★ e = e ⋯ᴿᴱ[ wk ] wkᴱ★

_→ˢᴱ[_]_ : Ctx S₁ → (S₁ →ˢ S₂) → Ctx S₂ → Set
Γ₁ →ˢᴱ[ σ ] Γ₂ = ∀ t → t ∈ Γ₁ → Expr Γ₂ (t ⋯ˢ σ)

idˢᴱ : Γ →ˢᴱ[ idˢ ] Γ
idˢᴱ _ x = ` x

_∙ˢᴱ_ : Expr Γ₂ (t ⋯ˢ σ) → (Γ₁ →ˢᴱ[ σ ] Γ₂) → 
        (Γ₁ ⸴ t) →ˢᴱ[ σ ] Γ₂
(e ∙ˢᴱ _) _ zero    = e
(_ ∙ˢᴱ σᴱ) _ (suc x) = σᴱ _ x

_∙ˢᴱ★_ : (t : S₂ ⊢ type) → (Γ₁ →ˢᴱ[ σ ] Γ₂) → (Γ₁ ⸴★) →ˢᴱ[ t ∙ˢ σ ] Γ₂
(t ∙ˢᴱ★ σᴱ) _ (suc★ x) = (σᴱ _ x)

_;ᴿˢᴱ_ : (Γ₁ →ᴿᴱ[ ρ ] Γ₂) → (Γ₂ →ˢᴱ[ σ ] Γ₃) → (Γ₁ →ˢᴱ[ ρ ;ᴿˢ σ ] Γ₃)
(ρᴱ ;ᴿˢᴱ σᴱ) _ x =  σᴱ _ (ρᴱ _ x)


_;ˢᴿᴱ_ : (Γ₁ →ˢᴱ[ σ ] Γ₂) → (Γ₂ →ᴿᴱ[ ρ ] Γ₃) → (Γ₁ →ˢᴱ[ σ ;ˢᴿ ρ ] Γ₃)
(σᴱ ;ˢᴿᴱ ρᴱ) _ x = (σᴱ _ x) ⋯ᴿᴱ[ _ ] ρᴱ

_↑ˢᴱ_ : (Γ₁ →ˢᴱ[ σ ] Γ₂) → ∀ t → (Γ₁ ⸴ t) →ˢᴱ[ σ ] (Γ₂ ⸴ (t ⋯ˢ σ))
_↑ˢᴱ_ {σ = σ} σᴱ t = _∙ˢᴱ_ {σ = σ} (` zero) (_;ˢᴿᴱ_ {σ = σ} {ρ = idᴿ} σᴱ wkᴱ)

_↑ˢᴱ★ : (Γ₁ →ˢᴱ[ σ ] Γ₂) → (Γ₁ ⸴★) →ˢᴱ[ σ ↑ˢ type ] (Γ₂ ⸴★)
_↑ˢᴱ★ {σ = σ} σᴱ = _∙ˢᴱ★_ {σ = σ ;ˢᴿ wk} (` zero) (_;ˢᴿᴱ_ {σ = σ} σᴱ wkᴱ★)

_⋯ˢᴱ[_]_ : {t : S₁ ⊢ type} {Γ₂ : Ctx S₂} → 
  Expr Γ₁ t → (σ : S₁ →ˢ S₂) → (σᴱ : Γ₁ →ˢᴱ[ σ ] Γ₂) → Expr Γ₂ (t ⋯ˢ σ)
(` x)      ⋯ˢᴱ[ σ ] σᴱ = σᴱ _ x
(λx e)     ⋯ˢᴱ[ σ ] σᴱ = λx (e ⋯ˢᴱ[ σ ] (_↑ˢᴱ_ {σ = σ} σᴱ _))
(Λα e)     ⋯ˢᴱ[ σ ] σᴱ = Λα (e ⋯ˢᴱ[ σ ↑ˢ _ ] (_↑ˢᴱ★ {σ = σ} σᴱ))
(e₁ · e₂)  ⋯ˢᴱ[ σ ] σᴱ = (e₁ ⋯ˢᴱ[ σ ] σᴱ) · (e₂ ⋯ˢᴱ[ σ ] σᴱ)
(e ∙ t′)   ⋯ˢᴱ[ σ ] σᴱ = (e ⋯ˢᴱ[ σ ] σᴱ) ∙ (t′ ⋯ˢ σ)

_[_]ᴱ : Expr (Γ ⸴ t′) t → Expr Γ t′ → Expr Γ t
e [ e′ ]ᴱ = e ⋯ˢᴱ[ idˢ ] (_∙ˢᴱ_ {σ = idˢ} e′  idˢᴱ)

_[_]ᴱ★ : {t : (type ∷ S) ⊢ type} → Expr (Γ ⸴★) t → (t′ : S ⊢ type) → Expr Γ (t [ t′ ])
e [ t′ ]ᴱ★ = e ⋯ˢᴱ[ t′ ∙ˢ idˢ ] (t′ ∙ˢᴱ★ idˢᴱ)