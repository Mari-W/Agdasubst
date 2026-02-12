{-# OPTIONS --rewriting --double-check --local-confluence-check #-}
module scoped14 where

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
  Q R U : S ⊢[ q ] s

data _⊩[_]_ : Scope → Mode → Scope → Set where
  ε    : [] ⊩[ q ] S
  _,_  : S₁ ⊩[ q ] S₂ → S₂ ⊢[ q ] s → (s ∷ S₁) ⊩[ q ] S₂  

data _⊑_ : Mode → Mode → Set where
  rfl  : q ⊑ q
  v⊑t  : V ⊑ T

_⊔_ : Mode → Mode → Mode
V ⊔ r  =  r
T ⊔ r  =  T

⊑t   : q ⊑ T
v⊑   : V ⊑ q
⊑q⊔  : q ⊑ (q ⊔ r)
⊑⊔r  : r ⊑ (q ⊔ r)

⊔⊔  : q ⊔ (r ⊔ u) ≡ (q ⊔ r) ⊔ u
⊔v  : q ⊔ V ≡ q
⊔t  : q ⊔ T ≡ T

⊑t {V} = v⊑t
⊑t {T} = rfl

v⊑ {V} = rfl
v⊑ {T} = v⊑t

⊑q⊔ {V} = v⊑
⊑q⊔ {T} = rfl

⊑⊔r {q = V} = rfl
⊑⊔r {q = T} = ⊑t

⊔⊔ {V} = refl
⊔⊔ {T} = refl

⊔v {V} = refl
⊔v {T} = refl

⊔t {V} = refl
⊔t {T} = refl

{-# REWRITE ⊔⊔ ⊔v ⊔t #-}

tm⊑ : q ⊑ r → S ⊢[ q ] s → S ⊢[ r ] s
tm⊑ rfl x  = x
tm⊑ v⊑t i = ` i

-- [MW] behold: the main trick! hide dependence in instance resolution.
record Suc (q : Mode) : Set where
  field 
    wk : S ⊢[ q ] s → ∀ {s′} → (s′ ∷ S) ⊢[ q ] s

open Suc {{...}} renaming (wk to wk′)

_⁺_ : {{_ : Suc q}} → S₁ ⊩[ q ] S₂ → ∀ s → S₁ ⊩[ q ] (s ∷ S₂)
ε ⁺ A = ε
(xs , x) ⁺ A = (xs ⁺ A) , wk′ x

_^_ : {{_ : Suc q}} → S₁ ⊩[ q ] S₂ → ∀ s → (s ∷ S₁) ⊩[ q ] (s ∷ S₂)
xs ^ A =  (xs ⁺ A) , tm⊑ v⊑ zero


_[_] : {{_ : Suc r}} → S₁ ⊢[ q ] s → S₁ ⊩[ r ] S₂ → S₂ ⊢[ q ⊔ r ] s
zero         [ xs , x ]  = x
(suc i)      [ xs , x ]  = i [ xs ]
(` i)        [ xs ]  = tm⊑ ⊑t (i [ xs ])
(λx e)       [ xs ] = λx (e [ xs ^ _ ])
(Λα e)       [ xs ] = Λα (e [ xs ^ _ ])
(∀[α∶ k ] t) [ xs ] = ∀[α∶ k [ xs ] ] (t [ xs ^ _ ])
(e₁ · e₂)    [ xs ] = (e₁ [ xs ]) · (e₂ [ xs ])
(e • t)      [ xs ] = (e [ xs ]) • (t [ xs ])
(t₁ ⇒ t₂)    [ xs ] = (t₁ [ xs ]) ⇒ (t₂ [ xs ])
★            [ xs ] = ★


id-poly : {{_ : Suc q}} → S ⊩[ q ] S 
id-poly {S = []} = ε
id-poly {S = _ ∷ _} = id-poly ^ _

id : {{_ : Suc V}} → S ⊩[ V ] S
id = id-poly {q = V}

instance 
  V<T : Suc q 
  V<T {V} = record { wk = λ x → suc x } 
  -- the second uses the first clause.. 
  V<T {T} = record { wk = λ x → x [ id ⁺ _ ] } 

-- [MW] syntax 
suc[_] : ∀ q → S ⊢[ q ] s → ∀ s′ → (s′ ∷ S) ⊢[ q ] s
suc[_] _ = λ x _ → wk′ x

_∘_ : S₁ ⊩[ q ] S₂ → S₂ ⊩[ r ] S₃ → S₁ ⊩[ q ⊔ r ] S₃
ε ∘ ys         = ε
(xs , x) ∘ ys  = (xs ∘ ys) , (x [ ys ])

_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = S₁ ⊩[ T ] S₂ 

variable
  σ σ₁ σ₂ σ₃ : S₁ ⊩[ q ]  S₂ 

opaque 
  _⋯ˢ_ : S₁ ⊢[ q ] s → S₁ ⊩[ r ] S₂ → S₂ ⊢[ q ⊔ r ] s
  _⋯ˢ_ = _[_] 
  _;ˢˢ_ : S₁ ⊩[ q ] S₂ → S₂ ⊩[ r ] S₃ → S₁ ⊩[ q ⊔ r ] S₃
  _;ˢˢ_ = _∘_
  idˢ : S ⊩[ V ] S
  idˢ = id-poly
  wk : ∀ s → S ⊩[ V ] (s ∷ S)
  wk = _⁺_ id-poly
  _∙ˢ_ : S₂ ⊢[ T ] s → S₁ ⊩[ q ] S₂ → (s ∷ S₁) ⊩[ T ] S₂  
  xt ∙ˢ σ = {!   !} , xt
  _↑ˢ_ : S₁ ⊩[ q ] S₂ → ∀ s → (s ∷ S₁) ⊩[ q ] (s ∷ S₂)
  _↑ˢ_ = _^_

postulate
  compositionalityˢˢ      : 
    (Q ⋯ˢ σ₁) ⋯ˢ σ₂ ≡ (Q ⋯ˢ (σ₁ ;ˢˢ σ₂))                         -- closss
  wk-beta                 : x ⋯ˢ (wk s)       ≡ suc x                                     -- varshift1
  wk-beta-compˢ           : x ⋯ˢ (wk s ;ˢˢ σ) ≡ suc x ⋯ˢ σ                               -- varshift2s
  ext-beta-zeroˢ          : zero ⋯ˢ (t ∙ˢ σ)           ≡ t                               -- fvarconss
  lift-beta-zeroˢ         : zero ⋯ˢ (σ ↑ˢ s)           ≡ ` zero                          -- fvarlift2s
  lift-beta-zero-compˢˢ   : zero ⋯ˢ ((σ₁ ↑ˢ s) ;ˢˢ σ₂) ≡ zero ⋯ˢ σ₂                      -- fvarlift2ss
  ext-beta-sucˢ           : suc x ⋯ˢ (t ∙ˢ σ)  ≡ x ⋯ˢ σ                                  -- rvarconss 
  lift-beta-sucˢ          : suc x ⋯ˢ (σ ↑ˢ s)  ≡ x ⋯ˢ (σ ;ˢˢ wk s)                       -- rvarlift1s
  lift-beta-suc-compˢˢ    : suc x ⋯ˢ ((σ₁ ↑ˢ s) ;ˢˢ σ₂) ≡ x ⋯ˢ (σ₁ ;ˢˢ (wk s ;ˢˢ σ₂))    -- rvarlift2ss
  comp-assocˢˢˢ           : (σ₁ ;ˢˢ σ₂) ;ˢˢ σ₃  ≡ σ₁ ;ˢˢ (σ₂ ;ˢˢ σ₃)                     -- assenvsss
  distributivityˢˢ        : (t ∙ˢ σ₁) ;ˢˢ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ;ˢˢ σ₂))               -- mapenvss
  interactˢ               : wk s ;ˢˢ (t ∙ˢ σ) ≡ σ                                        -- shiftconss
  wk-liftˢ                : wk s ;ˢˢ (σ ↑ˢ s) ≡ σ ;ˢˢ wk s                               -- shiftlift1s
  wk-lift-compˢˢ          : wk s ;ˢˢ ((σ₁ ↑ˢ s) ;ˢˢ σ₂) ≡ σ₁ ;ˢˢ (wk s  ;ˢˢ σ₂)          -- shiftlift2ss  
  lift-dist-compˢˢ        : (σ₁ ↑ˢ s) ;ˢˢ (σ₂ ↑ˢ s) ≡ (σ₁ ;ˢˢ σ₂) ↑ˢ s                   -- lift1ss
  lift-dist-comp-compˢˢˢ  : (σ₁ ↑ˢ s) ;ˢˢ ((σ₂ ↑ˢ s) ;ˢˢ σ₃) ≡ ((σ₁ ;ˢˢ σ₂) ↑ˢ s) ;ˢˢ σ₃ -- lift2sss
  lift-extˢˢ              : (σ₁ ↑ˢ s) ;ˢˢ (t ∙ˢ σ₂) ≡ t ∙ˢ (σ₁ ;ˢˢ σ₂)                   -- liftenvrr
  comp-idᵣˢˢ              : σ ;ˢˢ idˢ  ≡ σ                                               -- idrss
  comp-idₗˢˢ              : idˢ ;ˢˢ σ  ≡ σ                                               -- idlss
  up-idˢ                  : idˢ {S = S} ↑ˢ s ≡ idˢ                                       -- liftids
  right-idˢ               : t ⋯ˢ idˢ         ≡ t                                         -- ids
  right-var-idˢ           : x ⋯ˢ idˢ         ≡  x                                       -- ids
  trav-1 : (` x)        ⋯ˢ σ ≡ x ⋯ˢ σ
  trav0 : (λx e)        ⋯ˢ σ ≡ λx (e ⋯ˢ (σ ↑ˢ _))
  trav1 : (Λα e)        ⋯ˢ σ ≡ Λα (e ⋯ˢ (σ ↑ˢ _))
  trav2 : (∀[α∶ k ] t)  ⋯ˢ σ ≡ ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  trav3 : (e₁ · e₂)     ⋯ˢ σ ≡ (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  trav4 : (e • t)       ⋯ˢ σ ≡ (e ⋯ˢ σ) • (t ⋯ˢ σ)
  trav5 : (t₁ ⇒ t₂)     ⋯ˢ σ ≡ (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  trav6 : ★             ⋯ˢ σ ≡ ★

{-# REWRITE 
  compositionalityˢˢ   
  wk-beta                           
  wk-beta-compˢ                   
  ext-beta-zeroˢ          
  lift-beta-zeroˢ         
  lift-beta-zero-compˢˢ
  ext-beta-sucˢ           
  lift-beta-sucˢ          
  lift-beta-suc-compˢˢ    
  comp-assocˢˢˢ           
  distributivityˢˢ        
  interactˢ                
  wk-liftˢ                
  wk-lift-compˢˢ          
  lift-dist-compˢˢ        
  lift-dist-comp-compˢˢˢ  
  lift-extˢˢ              
  comp-idᵣˢˢ              
  comp-idₗˢˢ              
  up-idˢ                       
  right-idˢ 
  right-var-idˢ            
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

--!! Wk 
weaken : S ⊢ s → (s′ ∷ S) ⊢ s

weaken {s′ = s} t = t ⋯ˢ wk s

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
-- _∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
-- 
-- _∶_→ᴿ_ {S₁} {S₂} ρ Γ₁ Γ₂ = ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) → (Γ₁ ∋ x ∶ t) → Γ₂ ∋ (x &ᴿ ρ) ∶ t ⋯ᴿ ρ 

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
--   ⊢wkᴿ : ∀ (Γ : Ctx S) (x : S ∋ s) t (t′ : S ∶⊢ s′) → Γ ∋ x ∶ t → (t′ ∷ₜ Γ) ∋ (suc x) ∶ (weaken t) 
-- ⊢wkᴿ _ _ _ _ refl = refl

-- ⊢↑ᴿ : ρ ∶ Γ₁ →ᴿ Γ₂ → (t : S₁ ∶⊢ s) → (ρ ↑ᴿ s) ∶ (t ∷ₜ Γ₁) →ᴿ ((t ⋯ᴿ ρ) ∷ₜ Γ₂)
-- ⊢↑ᴿ ⊢ρ _ _ (zero) _ refl = refl -- refl
-- ⊢↑ᴿ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ t _ (suc x) _ refl = ⊢wkᴿ Γ₂ (x &ᴿ ρ) (wk-drop-∈ x (Γ₁ _ x) ⋯ᴿ ρ) (t ⋯ᴿ ρ) (⊢ρ _ x _ refl)
-- 
--! RPT
-- _⊢⋯ᴿ_ : ∀ {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
--   ρ ∶ Γ₁ →ᴿ Γ₂ →
--   Γ₁ ⊢ e ∶ t →
--   Γ₂ ⊢ (e ⋯ᴿ ρ) ∶ (t ⋯ᴿ ρ)
-- ⊢ρ ⊢⋯ᴿ (⊢` ⊢x)    = 
--   ⊢` (⊢ρ _ _ _ ⊢x) 
-- ⊢ρ ⊢⋯ᴿ (⊢λ ⊢e)        = 
--   ⊢λ ((⊢↑ᴿ ⊢ρ _) ⊢⋯ᴿ ⊢e)
-- ⊢ρ ⊢⋯ᴿ (⊢Λ ⊢e)        =
--   ⊢Λ ((⊢↑ᴿ ⊢ρ _) ⊢⋯ᴿ ⊢e)
-- ⊢ρ ⊢⋯ᴿ (⊢· ⊢e₁ ⊢e₂)   = 
--   ⊢· (⊢ρ ⊢⋯ᴿ ⊢e₁) (⊢ρ ⊢⋯ᴿ ⊢e₂)
-- ⊢ρ ⊢⋯ᴿ (⊢• ⊢e ⊢t ⊢t') = 
--   {! ⊢• (⊢ρ ⊢⋯ᴿ ⊢e) (⊢ρ ⊢⋯ᴿ ⊢t) ((⊢↑ᴿ ⊢ρ _) ⊢⋯ᴿ ⊢t')  !}
-- ⊢ρ ⊢⋯ᴿ ⊢★             = 
--   ⊢★

⊢wkˢ : ∀ (Γ : Ctx S) (e : S ⊢ s) (t : S ∶⊢ s) (t′ : S ∶⊢ s′) → Γ ⊢ e ∶ t → (t′ ∷ₜ Γ) ⊢ weaken e ∶ weaken t 
⊢wkˢ Γ e t t' ⊢t = {!   !}

⊢↑ˢ : σ ∶ Γ₁ →ˢ Γ₂ → (t : S ∶⊢ s) → (σ ↑ˢ s) ∶ t ∷ₜ Γ₁ →ˢ ((t ⋯ˢ σ) ∷ₜ Γ₂)
⊢↑ˢ ⊢σ _ _ (zero) _ refl = ⊢` {!   !} 
⊢↑ˢ {σ = σ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢σ t _ (suc x) _ refl = {!   !} -- ⊢wkˢ Γ₂ (x ⋯ˢ σ) (wk-drop-∈ x (Γ₁ _ x) ⋯ˢ σ) (t ⋯ˢ σ) (⊢σ _ x _ refl)

_⊢⋯ˢ_ : ∀ {σ : S₁ →ˢ S₂} {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
  σ ∶ Γ₁ →ˢ Γ₂ →
  Γ₁ ⊢ e ∶ t →
  Γ₂ ⊢ (e ⋯ˢ σ) ∶ (t ⋯ˢ σ)
--! SPT
⊢σ ⊢⋯ˢ (⊢` ⊢x)                  = ⊢σ _ _ _ ⊢x 
_⊢⋯ˢ_ {σ = σ} ⊢σ (⊢λ ⊢e)        = {!   !} --  ⊢λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢e) 
_⊢⋯ˢ_ {σ = σ}  ⊢σ (⊢Λ ⊢e)       = {!   !} --  ⊢Λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} (⊢↑ˢ {σ = σ} ⊢σ _) ⊢e)
_⊢⋯ˢ_ {σ = σ} ⊢σ (⊢· ⊢e₁ ⊢e₂)   =
  ⊢· (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e₁) (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e₂)
_⊢⋯ˢ_ {σ = σ} ⊢σ (⊢• ⊢e ⊢t ⊢t') = {!   !}
  -- ⊢• (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢e) (_⊢⋯ˢ_ {σ = σ} ⊢σ ⊢t) 
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
subject-reduction (⊢· {e₂ = e₂} (⊢λ ⊢e₁) ⊢e₂) (β-λ v₂)        = {!   !} -- ⊢⋯ˢ_ {σ = e₂ ∙ˢ idˢ} (⊢[] ⊢e₂) ⊢e₁
subject-reduction (⊢• {t = t} (⊢Λ ⊢e) ⊢t ⊢t') β-Λ             = {!   !} -- ⊢⋯ˢ_ {σ = t ∙ˢ idˢ} (⊢[] ⊢t) ⊢e     
subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₁ e₁↪e)     = ⊢· (subject-reduction ⊢e₁ e₁↪e) ⊢e₂
subject-reduction (⊢· ⊢e₁ ⊢e₂)                (ξ-·₂ e₂↪e x)   = ⊢· ⊢e₁ (subject-reduction ⊢e₂ e₂↪e)          
subject-reduction (⊢• ⊢e ⊢t ⊢t')              (ξ-• e↪e')      = ⊢• (subject-reduction ⊢e e↪e') ⊢t ⊢t'  