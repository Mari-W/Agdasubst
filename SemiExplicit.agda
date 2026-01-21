module SemiExplicit where 
   

open import Data.List using (List; []; _∷_; drop)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; module ≡-Reasoning)
open ≡-Reasoning

data Sort : Set where 
  expr type kind : Sort 

variable 

  s s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort

Scope = List Sort
Scoped = Scope → Sort → Set

data _∋_ : Scoped where
  zero  : ∀ {S s} → (s ∷ S) ∋ s
  suc   : ∀ {S s s′} → S ∋ s → (s′ ∷ S) ∋ s

data _⊢_ : Scoped
_→ˢ_ : Scope → Scope → Set

S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s

data _⊢_ where 
  `_       : S ∋ s → S ⊢ s     
  λ[_]x_   : S₁ →ˢ S₂ → (expr ∷ S₁) ⊢ expr → S₂ ⊢ expr
  _·_      : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _⇒_      : S ⊢ type → S ⊢ type → S ⊢ type
  ★        : S ⊢ kind

λx_ : (expr ∷ S) ⊢ expr → S ⊢ expr
λx e = λ[ (λ _ x → ` x) ]x e

_&ˢ_ : S₁ ∋ s → (S₁ →ˢ S₂) → S₂ ⊢ s
x &ˢ σ = σ _ x

idˢ : S →ˢ S
idˢ _ = `_

wkˢ : S →ˢ (s ∷ S)
wkˢ _ x = ` (suc x)

_∙ˢ_ : S₂ ⊢ s → (S₁ →ˢ S₂) → ((s ∷ S₁) →ˢ S₂)
(t ∙ˢ _)  _ zero     = t
(_ ∙ˢ σ)  _ (suc x)  = σ _ x

_;ˢˢ_ :  (S₁ →ˢ S₂) → (S₂ →ˢ S₃) → (S₁ →ˢ S₃)
_⋯ˢ_ : S₁ ⊢ s → (S₁ →ˢ S₂) → S₂ ⊢ s

(σ₁ ;ˢˢ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂

(` x)         ⋯ˢ σ = (x &ˢ σ)
(λ[ λσ ]x e)  ⋯ˢ σ = λ[ λσ ;ˢˢ σ ]x e
(e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
(t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
★             ⋯ˢ σ = ★

_↑ˢ : (S₁ →ˢ S₂) → ∀ {s} → ((s ∷ S₁) →ˢ (s ∷ S₂))
σ ↑ˢ = (` zero) ∙ˢ (σ ;ˢˢ wkˢ)


variable
  e e₁ e₂ e₃ e′ : S ⊢ expr
  T T₁ T₂ T₃ T′ : S ⊢ type
  x x₁ x₂ x₃ x′ : S ∋ s
  t t₁ t₂ t₃ t′ : S ⊢ s
  σ σ₁ σ₂ σ₃ σ′ : S₁ →ˢ S₂ 

idˢ–def     : x &ˢ idˢ            ≡ ` x
ext₀ˢ–def   : zero &ˢ (t ∙ˢ σ)    ≡ t
wkˢ–def     : x &ˢ wkˢ {s = s′}   ≡ ` (suc x)
extₛˢ–def   : (suc x) &ˢ (t ∙ˢ σ) ≡ x &ˢ σ
compˢˢ–def  : x &ˢ (σ₁ ;ˢˢ σ₂)    ≡ (x &ˢ σ₁) ⋯ˢ σ₂

comp-idᵣˢˢ  : (σ : S₁ →ˢ S₂) → σ ;ˢˢ idˢ ≡ σ
comp-idₗˢˢ  : (σ : S₁ →ˢ S₂) → idˢ ;ˢˢ σ ≡ σ
associativityˢˢˢ  : (σ₁ : S₁ →ˢ S₂) (σ₂ : S₂ →ˢ S₃) (σ₃ : S₃ →ˢ S₄) → (σ₁ ;ˢˢ σ₂) ;ˢˢ σ₃  ≡ σ₁ ;ˢˢ (σ₂ ;ˢˢ σ₃)
distributivityˢˢ  : (t : S₂ ⊢ s) (σ₁ : S₁ →ˢ S₂) (σ₂ : S₂ →ˢ S₃) → (t ∙ˢ σ₁) ;ˢˢ σ₂    ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ;ˢˢ σ₂))
interactˢ : (t : S₂ ⊢ s) (σ : S₁ →ˢ S₂) → wkˢ ;ˢˢ (t ∙ˢ σ) ≡ σ

η-idˢ   : (` zero {S = S} {s = s}) ∙ˢ wkˢ  ≡ idˢ
η-lawˢ  : (σ : (s ∷ S₁) →ˢ S₂) → (zero &ˢ σ) ∙ˢ (wkˢ ;ˢˢ σ)       ≡ σ

right-idˢ          : (t : S ⊢ s) → t ⋯ˢ idˢ ≡ t 
compositionalityˢˢ : (t : S₁ ⊢ s) (σ₁ : S₁ →ˢ S₂) (σ₂ : S₂ →ˢ S₃) → (t ⋯ˢ σ₁) ⋯ˢ σ₂  ≡ t ⋯ˢ (σ₁ ;ˢˢ σ₂)


_~_ : (σ₁ σ₂ : S₁ →ˢ S₂) → Set
_~_ {S₁} σ₁ σ₂ = ∀ {s} (x : S₁ ∋ s) → x &ˢ σ₁ ≡ x &ˢ σ₂
postulate 
  ~-ext : ∀ {σ₁ σ₂ : S₁ →ˢ S₂} → σ₁ ~ σ₂ → σ₁ ≡ σ₂  

idˢ–def     = refl
ext₀ˢ–def   = refl
wkˢ–def     = refl
extₛˢ–def   = refl
compˢˢ–def  = refl

comp-idᵣˢˢ σ = ~-ext λ x → right-idˢ (σ _ x) 
comp-idₗˢˢ σ = refl 
associativityˢˢˢ σ₁ σ₂ σ₃ = ~-ext λ x → compositionalityˢˢ (σ₁ _ x) σ₂ σ₃
distributivityˢˢ t σ₁ σ₂  = ~-ext λ { zero → refl ; (suc x) → refl }
interactˢ t σ = refl
η-idˢ    = ~-ext λ { zero → refl ; (suc x) → refl }
η-lawˢ σ = ~-ext λ { zero → refl ; (suc x) → refl }

right-idˢ (` x)        = refl
right-idˢ (λ[ λσ ]x e) = cong (λ[_]x e) (comp-idᵣˢˢ λσ)
right-idˢ (e₁ · e₂)    = cong₂ _·_ (right-idˢ e₁) (right-idˢ e₂)
right-idˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idˢ t₁) (right-idˢ t₂)
right-idˢ ★            = refl

compositionalityˢˢ (` x)        σ₁ σ₂ = refl
compositionalityˢˢ (λ[ λσ ]x e) σ₁ σ₂ = cong (λ[_]x e) (associativityˢˢˢ λσ σ₁ σ₂)
compositionalityˢˢ (e₁ · e₂)    σ₁ σ₂ = cong₂ _·_ (compositionalityˢˢ e₁ σ₁ σ₂) (compositionalityˢˢ e₂ σ₁ σ₂)
compositionalityˢˢ (t₁ ⇒ t₂)    σ₁ σ₂ = cong₂ _⇒_ (compositionalityˢˢ t₁ σ₁ σ₂) (compositionalityˢˢ t₂ σ₁ σ₂)
compositionalityˢˢ ★            σ₁ σ₂ = refl

↑ᵗ : Sort → Sort
↑ᵗ expr = type
↑ᵗ type = kind
↑ᵗ kind = kind

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

wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s′ → S ⊢ s′
wk-drop-∈ zero     t = t ⋯ˢ wkˢ
wk-drop-∈ (suc x)  t = wk-drop-∈ x t ⋯ˢ wkˢ

lookup : Ctx S → S ∋ s → S ∶⊢ s
lookup Γ x = wk-drop-∈ x (Γ _ x)

_∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
Γ ∋ x ∶ t = lookup Γ x ≡ t

variable
  Γ Γ₁ Γ₂ Γ₃ Γ′ : Ctx S

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {Γ : Ctx S} {x : S ∋ s} {t : S ∶⊢ s} →
    Γ ∋ x ∶ t → 
    -------------
    Γ ⊢ (` x) ∶ t
  ⊢λ : {σ : S₁ →ˢ S₂} →
    (t ∷ₜ Γ) ⊢ e ∶ (t′ ⋯ˢ wkˢ) → 
    --------------------------
    Γ ⊢ (λ[ σ ]x e) ∶ (t ⇒ t′) 
  ⊢· : 
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    --------------------
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢★ : 
    ---------
    Γ ⊢ T ∶ ★ 

_∶_→ˢ_ : S₁ →ˢ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ˢ_ {S₁} {S₂} σ Γ₁ Γ₂ = 
  ∀ {s} (x : S₁ ∋ s) (t : S₁ ∶⊢ s) →
  Γ₁ ∋ x ∶ t → 
  Γ₂ ⊢ (x &ˢ σ) ∶ (t ⋯ˢ σ)


_⊢⋯_ : ∀ {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} 
    {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} {σ : S₁ →ˢ S₂} →
  Γ₁ ⊢ e ∶ t →
  σ ∶ Γ₁ →ˢ Γ₂ →
  Γ₂ ⊢ (e ⋯ˢ σ) ∶ (t ⋯ˢ σ)
⊢` x       ⊢⋯ ⊢σ = ⊢σ _ _ x
⊢λ ⊢e      ⊢⋯ ⊢σ = subst (_ ⊢ _ ∶_) {!   !} (⊢λ (⊢e ⊢⋯ {!   !}))
⊢· ⊢e₁ ⊢e₂ ⊢⋯ ⊢σ = ⊢· (⊢e₁ ⊢⋯ ⊢σ) (⊢e₂ ⊢⋯ ⊢σ)
⊢★         ⊢⋯ ⊢σ = ⊢★