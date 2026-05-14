{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module cbpv_bool where
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; module ≡-Reasoning)
open ≡-Reasoning

cong1 : ∀ {A1 A2 : Set} (f : A1 → A2) {a1 a2} →
  a1 ≡ a2 → f a1 ≡ f a2
cong1 f refl = refl

cong2 : ∀ {A1 A2 A3 : Set} (f : A1 → A2 → A3) {a1 a2 a3 a4} →
  a1 ≡ a2 → a3 ≡ a4 → f a1 a3 ≡ f a2 a4
cong2 f refl refl = refl

cong3 : ∀ {A1 A2 A3 A4 : Set} (f : A1 → A2 → A3 → A4) {a1 a2 a3 a4 a5 a6} →
  a1 ≡ a2 → a3 ≡ a4 → a5 ≡ a6 → f a1 a3 a5 ≡ f a2 a4 a6
cong3 f refl refl refl = refl

open import Data.List using (List; []; _∷_; _++_)

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

data Mode : Set where 
  V T : Mode

private variable
  m  : Mode

data Sort : Set where 
  tm vl Tm : Sort

Scope = List Sort

private variable 
  s s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort

data _⊢[_]_ : Scope → Mode → Sort → Set 

_⊢_ = _⊢[ T ]_
_∋_ = _⊢[ V ]_

data _⊢[_]_ where 
  zero : (s ∷ S) ∋ s
  suc  : S ∋ s → (s′ ∷ S) ∋ s
  var  : S ∋ s → S ⊢ s 

  lam     : (vl ∷ S) ⊢ tm → S ⊢ tm
  app     : S ⊢ tm → S ⊢ vl → S ⊢ tm
  creturn : S ⊢ vl → S ⊢ tm
  clet    : S ⊢ tm → (vl ∷ S) ⊢ tm → S ⊢ tm
  force   : S ⊢ vl → S ⊢ tm
  cif     : S ⊢ vl → S ⊢ tm → S ⊢ tm → S ⊢ tm
  true    : S ⊢ vl
  false   : S ⊢ vl
  thunk   : S ⊢ tm → S ⊢ vl
  Lam     : (Tm ∷ S) ⊢ Tm → S ⊢ Tm
  App     : S ⊢ Tm → S ⊢ Tm → S ⊢ Tm
  If      : S ⊢ Tm → S ⊢ Tm → S ⊢ Tm → S ⊢ Tm
  True    : S ⊢ Tm
  False   : S ⊢ Tm

private variable
  x x′     : S ∋ s
  t t′     : S ⊢ s
  x/t x/t′ : S ⊢[ m ] s

_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 

private variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂

opaque
  idᴿ : S →ᴿ S
  idᴿ _ x = x

  wkᴿ : ∀ s → S →ᴿ (s ∷ S)
  wkᴿ _ _ = suc

  _∘_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → 
    S₁ →ᴿ S₃
  (ρ₁ ∘ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

  _∙ᴿ_ :  S₂ ∋ s → S₁ →ᴿ S₂ → 
    (s ∷ S₁) →ᴿ S₂    
  (x ∙ᴿ ρ) _ zero = x
  (_ ∙ᴿ ρ) _ (suc x) = ρ _ x


_↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → 
  ((s ∷ S₁) →ᴿ (s ∷ S₂))
(ρ ↑ᴿ _) = zero ∙ᴿ (ρ ∘ (wkᴿ _))

_↑ᴿ*_ : (S₁ →ᴿ S₂) → ∀ S → ((S ++ S₁) →ᴿ (S ++ S₂))
ρ ↑ᴿ* []      = ρ
ρ ↑ᴿ* (s ∷ S) = (ρ ↑ᴿ* S) ↑ᴿ s

opaque
  _⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → 
    S₂ ⊢[ m ] s 
  _⋯ᴿ_ {m = V} x   ρ  = ρ _ x
  (var x)         ⋯ᴿ ρ = var (ρ _ x)

  (lam tm0)         ⋯ᴿ ρ = lam (tm0 ⋯ᴿ (ρ ↑ᴿ* _))
  (app tm0 vl0)     ⋯ᴿ ρ = app (tm0 ⋯ᴿ ρ) (vl0 ⋯ᴿ ρ)
  (creturn vl0)     ⋯ᴿ ρ = creturn (vl0 ⋯ᴿ ρ)
  (clet tm0 tm1)    ⋯ᴿ ρ = clet (tm0 ⋯ᴿ ρ) (tm1 ⋯ᴿ (ρ ↑ᴿ* _))
  (force vl0)       ⋯ᴿ ρ = force (vl0 ⋯ᴿ ρ)
  (cif vl0 tm0 tm1) ⋯ᴿ ρ = cif (vl0 ⋯ᴿ ρ) (tm0 ⋯ᴿ ρ) (tm1 ⋯ᴿ ρ)
  true              ⋯ᴿ ρ = true
  false             ⋯ᴿ ρ = false
  (thunk tm0)       ⋯ᴿ ρ = thunk (tm0 ⋯ᴿ ρ)
  (Lam Tm0)         ⋯ᴿ ρ = Lam (Tm0 ⋯ᴿ (ρ ↑ᴿ* _))
  (App Tm0 Tm1)     ⋯ᴿ ρ = App (Tm0 ⋯ᴿ ρ) (Tm1 ⋯ᴿ ρ)
  (If Tm0 Tm1 Tm2)  ⋯ᴿ ρ = If (Tm0 ⋯ᴿ ρ) (Tm1 ⋯ᴿ ρ) (Tm2 ⋯ᴿ ρ)
  True              ⋯ᴿ ρ = True
  False             ⋯ᴿ ρ = False

variable
  Tm0 Tm1 Tm2 : S ⊢ Tm
  tm0 tm1 : S ⊢ tm
  vl0 : S ⊢ vl

_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s 

variable
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂  

opaque
  ⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂ 
  ⟨ ρ ⟩ _ x = var (ρ _ x)

idˢ : S →ˢ S
idˢ = ⟨ idᴿ ⟩
{-# INLINE idˢ #-}

wkˢ : ∀ s → S →ˢ (s ∷ S)
wkˢ _ = ⟨ wkᴿ _ ⟩
{-# INLINE wkˢ #-}

opaque  
  unfolding _⋯ᴿ_ 
  _∙ˢ_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
  _∙ˢ_  t σ _ zero = t
  (t ∙ˢ σ) _ (suc x) = σ _ x 

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s =  (var zero) ∙ˢ λ _ x → (σ _ x) ⋯ᴿ wkᴿ _

_↑ˢ*_ : (S₁ →ˢ S₂) → ∀ S → ((S ++ S₁) →ˢ (S ++ S₂))
σ ↑ˢ* [] = σ
σ ↑ˢ* (s ∷ S) = (σ ↑ˢ* S) ↑ˢ s

opaque
  unfolding idᴿ _⋯ᴿ_ ⟨_⟩ _∙ˢ_
  _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
  _⋯ˢ_ {m = V} x σ = σ _ x
  (var x) ⋯ˢ σ = σ _ x

  (lam tm0)         ⋯ˢ σ = lam (tm0 ⋯ˢ (σ ↑ˢ* _))
  (app tm0 vl0)     ⋯ˢ σ = app (tm0 ⋯ˢ σ) (vl0 ⋯ˢ σ)
  (creturn vl0)     ⋯ˢ σ = creturn (vl0 ⋯ˢ σ)
  (clet tm0 tm1)    ⋯ˢ σ = clet (tm0 ⋯ˢ σ) (tm1 ⋯ˢ (σ ↑ˢ* _))
  (force vl0)       ⋯ˢ σ = force (vl0 ⋯ˢ σ)
  (cif vl0 tm0 tm1) ⋯ˢ σ = cif (vl0 ⋯ˢ σ) (tm0 ⋯ˢ σ) (tm1 ⋯ˢ σ)
  true              ⋯ˢ σ = true
  false             ⋯ˢ σ = false
  (thunk tm0)       ⋯ˢ σ = thunk (tm0 ⋯ˢ σ)
  (Lam Tm0)         ⋯ˢ σ = Lam (Tm0 ⋯ˢ (σ ↑ˢ* _))
  (App Tm0 Tm1)     ⋯ˢ σ = App (Tm0 ⋯ˢ σ) (Tm1 ⋯ˢ σ)
  (If Tm0 Tm1 Tm2)  ⋯ˢ σ = If (Tm0 ⋯ˢ σ) (Tm1 ⋯ˢ σ) (Tm2 ⋯ˢ σ)
  True              ⋯ˢ σ = True
  False             ⋯ˢ σ = False

  _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂

  def-∙ˢ-zero           : zero ⋯ˢ (t ∙ˢ σ)   ≡ t                             
  def-∙ˢ-suc            : suc x ⋯ˢ (t ∙ˢ σ)  ≡ x ⋯ˢ σ 
  def-⨟ : (x ⋯ˢ (σ₁ ⨟ σ₂)) ≡ ((x ⋯ˢ σ₁) ⋯ˢ σ₂)
  def-↑ˢ               : σ ↑ˢ s ≡ (var zero) ∙ˢ (σ ⨟ wkˢ _)

  def-id                : x ⋯ᴿ idᴿ ≡ x
  def-wkᴿ                : x ⋯ᴿ (wkᴿ s) ≡ suc x  
  def-∙ᴿ-zero           : zero ⋯ᴿ (x ∙ᴿ ρ)     ≡ x         
  def-∙ᴿ-suc            : (suc x) ⋯ᴿ (x′ ∙ᴿ ρ)  ≡ x ⋯ᴿ ρ      
  def-∘                 : x ⋯ᴿ (ρ₁ ∘ ρ₂) ≡ (x ⋯ᴿ ρ₁) ⋯ᴿ ρ₂

  assoc : (σ₁ ⨟ σ₂) ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  dist : (t ∙ˢ σ₁)  ⨟ σ₂  ≡ ((t ⋯ˢ σ₂) ∙ˢ (σ₁ ⨟ σ₂)) 
  interact                : wkˢ s ⨟ (t ∙ˢ σ) ≡ σ                                        
  comp-idᵣ                : σ ⨟ idˢ         ≡ σ                                               
  comp-idₗ                : idˢ ⨟ σ         ≡ σ                                               
  η-id    : (var (zero {s} {S})) ∙ˢ (wkˢ _)      ≡ idˢ
  η-law  : (zero ⋯ˢ σ) ∙ˢ (wkˢ _ ⨟ σ)        ≡ σ

  assocᴿ           : (ρ₁ ∘ ρ₂) ∘ ρ₃ ≡ ρ₁ ∘ (ρ₂ ∘ ρ₃)                     
  distᴿ : (x ∙ᴿ ρ₁)  ∘ ρ₂  ≡ ((x ⋯ᴿ ρ₂) ∙ᴿ (ρ₁ ∘ ρ₂)) 
  interactᴿ                : wkᴿ s ∘ (x ∙ᴿ ρ) ≡ ρ                                        
  comp-idᵣᴿ                : ρ ∘ idᴿ         ≡ ρ                                               
  comp-idₗᴿ                : idᴿ ∘ ρ         ≡ ρ                                               
  η-idᴿ    : (zero {s} {S}) ∙ᴿ (wkᴿ _)      ≡ idᴿ
  η-lawᴿ  : (zero ⋯ᴿ ρ) ∙ᴿ (wkᴿ _ ∘ ρ)        ≡ ρ

  right-id                : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ                   ≡ t   
  compositionalityᴿᴿ      : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ t ⋯ᴿ (ρ₁ ∘ ρ₂)     
  compositionalityᴿˢ      : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                                    
  compositionalityˢᴿ      : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ t ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (σ₁ ⨟ σ₂)


  inst-var           : (var x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  inst-var = refl

  instᴿ-var           : (var x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  instᴿ-var = refl

  instᴿ-lam     : (lam tm0) ⋯ᴿ ρ         ≡ lam (tm0 ⋯ᴿ (ρ ↑ᴿ* (vl ∷ [])))
  instᴿ-lam     = refl
  instᴿ-app     : (app tm0 vl0) ⋯ᴿ ρ     ≡ app (tm0 ⋯ᴿ ρ) (vl0 ⋯ᴿ ρ)
  instᴿ-app     = refl
  instᴿ-creturn : (creturn vl0) ⋯ᴿ ρ     ≡ creturn (vl0 ⋯ᴿ ρ)
  instᴿ-creturn = refl
  instᴿ-clet    : (clet tm0 tm1) ⋯ᴿ ρ    ≡ clet (tm0 ⋯ᴿ ρ) (tm1 ⋯ᴿ (ρ ↑ᴿ* (vl ∷ [])))
  instᴿ-clet    = refl
  instᴿ-force   : (force vl0) ⋯ᴿ ρ       ≡ force (vl0 ⋯ᴿ ρ)
  instᴿ-force   = refl
  instᴿ-cif     : (cif vl0 tm0 tm1) ⋯ᴿ ρ ≡ cif (vl0 ⋯ᴿ ρ) (tm0 ⋯ᴿ ρ) (tm1 ⋯ᴿ ρ)
  instᴿ-cif     = refl
  instᴿ-true    : true ⋯ᴿ ρ              ≡ true
  instᴿ-true    = refl
  instᴿ-false   : false ⋯ᴿ ρ             ≡ false
  instᴿ-false   = refl
  instᴿ-thunk   : (thunk tm0) ⋯ᴿ ρ       ≡ thunk (tm0 ⋯ᴿ ρ)
  instᴿ-thunk   = refl
  instᴿ-Lam     : (Lam Tm0) ⋯ᴿ ρ         ≡ Lam (Tm0 ⋯ᴿ (ρ ↑ᴿ* (Tm ∷ [])))
  instᴿ-Lam     = refl
  instᴿ-App     : (App Tm0 Tm1) ⋯ᴿ ρ     ≡ App (Tm0 ⋯ᴿ ρ) (Tm1 ⋯ᴿ ρ)
  instᴿ-App     = refl
  instᴿ-If      : (If Tm0 Tm1 Tm2) ⋯ᴿ ρ  ≡ If (Tm0 ⋯ᴿ ρ) (Tm1 ⋯ᴿ ρ) (Tm2 ⋯ᴿ ρ)
  instᴿ-If      = refl
  instᴿ-True    : True ⋯ᴿ ρ              ≡ True
  instᴿ-True    = refl
  instᴿ-False   : False ⋯ᴿ ρ             ≡ False
  instᴿ-False   = refl
  inst-lam     : (lam tm0) ⋯ˢ σ         ≡ lam (tm0 ⋯ˢ (σ ↑ˢ* (vl ∷ [])))
  inst-lam     = refl
  inst-app     : (app tm0 vl0) ⋯ˢ σ     ≡ app (tm0 ⋯ˢ σ) (vl0 ⋯ˢ σ)
  inst-app     = refl
  inst-creturn : (creturn vl0) ⋯ˢ σ     ≡ creturn (vl0 ⋯ˢ σ)
  inst-creturn = refl
  inst-clet    : (clet tm0 tm1) ⋯ˢ σ    ≡ clet (tm0 ⋯ˢ σ) (tm1 ⋯ˢ (σ ↑ˢ* (vl ∷ [])))
  inst-clet    = refl
  inst-force   : (force vl0) ⋯ˢ σ       ≡ force (vl0 ⋯ˢ σ)
  inst-force   = refl
  inst-cif     : (cif vl0 tm0 tm1) ⋯ˢ σ ≡ cif (vl0 ⋯ˢ σ) (tm0 ⋯ˢ σ) (tm1 ⋯ˢ σ)
  inst-cif     = refl
  inst-true    : true ⋯ˢ σ              ≡ true
  inst-true    = refl
  inst-false   : false ⋯ˢ σ             ≡ false
  inst-false   = refl
  inst-thunk   : (thunk tm0) ⋯ˢ σ       ≡ thunk (tm0 ⋯ˢ σ)
  inst-thunk   = refl
  inst-Lam     : (Lam Tm0) ⋯ˢ σ         ≡ Lam (Tm0 ⋯ˢ (σ ↑ˢ* (Tm ∷ [])))
  inst-Lam     = refl
  inst-App     : (App Tm0 Tm1) ⋯ˢ σ     ≡ App (Tm0 ⋯ˢ σ) (Tm1 ⋯ˢ σ)
  inst-App     = refl
  inst-If      : (If Tm0 Tm1 Tm2) ⋯ˢ σ  ≡ If (Tm0 ⋯ˢ σ) (Tm1 ⋯ˢ σ) (Tm2 ⋯ˢ σ)
  inst-If      = refl
  inst-True    : True ⋯ˢ σ              ≡ True
  inst-True    = refl
  inst-False   : False ⋯ˢ σ             ≡ False
  inst-False   = refl

  coincidence     : t ⋯ˢ ⟨ ρ ⟩ ≡ t ⋯ᴿ ρ
  coincidence-var : x ⋯ˢ ⟨ ρ ⟩ ≡ var (x ⋯ᴿ ρ)

  def-∙ˢ-zero = refl
  def-∙ˢ-suc  = refl
  def-↑ˢ {σ = σ} = cong1 ((var zero) ∙ˢ_) (sym (ext λ x → coincidence {t = (σ _ x)}))
  def-⨟      = refl

  def-id      = refl
  def-wkᴿ      = refl      
  def-∙ᴿ-zero = refl
  def-∙ᴿ-suc  = refl
  def-∘       = refl

  η-lawˢᴿ  : (var (zero ⋯ᴿ ρ)) ∙ˢ (wkˢ _ ⨟ ⟨ ρ ⟩)  ≡ ⟨ ρ ⟩
  η-lawˢᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-idˢ* : ∀ S → (idˢ {S = S₁} ↑ˢ* S) ≡ idˢ 
  lift-idˢ* []    = refl
  lift-idˢ* {S₁} (_ ∷ S) rewrite lift-idˢ* {S₁} S = η-lawˢᴿ

  right-idˢ               : ∀ (t : S ⊢ s) → t ⋯ˢ idˢ                   ≡ t 
  right-idˢ (var x)        = refl
  right-idˢ (lam tm0)         = cong1 lam (trans (cong1 (tm0 ⋯ˢ_) (lift-idˢ* (vl ∷ []))) (right-idˢ tm0))
  right-idˢ (app tm0 vl0)     = cong2 app (right-idˢ tm0) (right-idˢ vl0)
  right-idˢ (creturn vl0)     = cong1 creturn (right-idˢ vl0)
  right-idˢ (clet tm0 tm1)    = cong2 clet (right-idˢ tm0) (trans (cong1 (tm1 ⋯ˢ_) (lift-idˢ* (vl ∷ []))) (right-idˢ tm1))
  right-idˢ (force vl0)       = cong1 force (right-idˢ vl0)
  right-idˢ (cif vl0 tm0 tm1) = cong3 cif (right-idˢ vl0) (right-idˢ tm0) (right-idˢ tm1)
  right-idˢ true              = refl
  right-idˢ false             = refl
  right-idˢ (thunk tm0)       = cong1 thunk (right-idˢ tm0)
  right-idˢ (Lam Tm0)         = cong1 Lam (trans (cong1 (Tm0 ⋯ˢ_) (lift-idˢ* (Tm ∷ []))) (right-idˢ Tm0))
  right-idˢ (App Tm0 Tm1)     = cong2 App (right-idˢ Tm0) (right-idˢ Tm1)
  right-idˢ (If Tm0 Tm1 Tm2)  = cong3 If (right-idˢ Tm0) (right-idˢ Tm1) (right-idˢ Tm2)
  right-idˢ True              = refl
  right-idˢ False             = refl

  assoc {σ₁ = σ₁} = ext λ x → compositionalityˢˢ (σ₁ _ x) 
  dist = ext λ { zero → refl; (suc x) → refl }
  interact        = refl
  comp-idᵣ        = ext λ x → (right-idˢ _)
  comp-idₗ        = refl
  η-id            = ext λ { zero → refl; (suc x) → refl }
  η-law          = ext λ { zero → refl; (suc x) → refl }

  assocᴿ = refl
  distᴿ = ext λ { zero → refl; (suc x) → refl }
  interactᴿ = refl
  comp-idᵣᴿ = refl
  comp-idₗᴿ = refl
  η-idᴿ = ext λ { zero → refl; (suc x) → refl }
  η-lawᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-id : idᴿ {S = S} ↑ᴿ s ≡ idᴿ
  lift-id = ext λ { zero → refl; (suc x) → refl }

  lift-id* : ∀ S → (idᴿ {S = S₁} ↑ᴿ* S) ≡ idᴿ
  lift-id* []    = refl
  lift-id* {S₁}  (_ ∷ S) rewrite lift-id* {S₁} S = lift-id

  right-id (var x)        = refl
  right-id (lam tm0)         = cong1 lam (trans (cong1 (tm0 ⋯ᴿ_) (lift-id* (vl ∷ []))) (right-id tm0))
  right-id (app tm0 vl0)     = cong2 app (right-id tm0) (right-id vl0)
  right-id (creturn vl0)     = cong1 creturn (right-id vl0)
  right-id (clet tm0 tm1)    = cong2 clet (right-id tm0) (trans (cong1 (tm1 ⋯ᴿ_) (lift-id* (vl ∷ []))) (right-id tm1))
  right-id (force vl0)       = cong1 force (right-id vl0)
  right-id (cif vl0 tm0 tm1) = cong3 cif (right-id vl0) (right-id tm0) (right-id tm1)
  right-id true              = refl
  right-id false             = refl
  right-id (thunk tm0)       = cong1 thunk (right-id tm0)
  right-id (Lam Tm0)         = cong1 Lam (trans (cong1 (Tm0 ⋯ᴿ_) (lift-id* (Tm ∷ []))) (right-id Tm0))
  right-id (App Tm0 Tm1)     = cong2 App (right-id Tm0) (right-id Tm1)
  right-id (If Tm0 Tm1 Tm2)  = cong3 If (right-id Tm0) (right-id Tm1) (right-id Tm2)
  right-id True              = refl
  right-id False             = refl

  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ  (lam tm0)         = cong1 lam (trans (compositionalityᴿᴿ tm0) (cong1 (tm0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (vl ∷ []))))
  compositionalityᴿᴿ  (app tm0 vl0)     = cong2 app (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ vl0)
  compositionalityᴿᴿ  (creturn vl0)     = cong1 creturn (compositionalityᴿᴿ vl0)
  compositionalityᴿᴿ  (clet tm0 tm1)    = cong2 clet (compositionalityᴿᴿ tm0) (trans (compositionalityᴿᴿ tm1) (cong1 (tm1 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (vl ∷ []))))
  compositionalityᴿᴿ  (force vl0)       = cong1 force (compositionalityᴿᴿ vl0)
  compositionalityᴿᴿ  (cif vl0 tm0 tm1) = cong3 cif (compositionalityᴿᴿ vl0) (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ tm1)
  compositionalityᴿᴿ true               = refl
  compositionalityᴿᴿ false              = refl
  compositionalityᴿᴿ  (thunk tm0)       = cong1 thunk (compositionalityᴿᴿ tm0)
  compositionalityᴿᴿ  (Lam Tm0)         = cong1 Lam (trans (compositionalityᴿᴿ Tm0) (cong1 (Tm0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (Tm ∷ []))))
  compositionalityᴿᴿ  (App Tm0 Tm1)     = cong2 App (compositionalityᴿᴿ Tm0) (compositionalityᴿᴿ Tm1)
  compositionalityᴿᴿ  (If Tm0 Tm1 Tm2)  = cong3 If (compositionalityᴿᴿ Tm0) (compositionalityᴿᴿ Tm1) (compositionalityᴿᴿ Tm2)
  compositionalityᴿᴿ True               = refl
  compositionalityᴿᴿ False              = refl

  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ {σ₂ = σ₂} (_ ∷ S) = trans (lift-dist-compᴿˢ {σ₂ = σ₂ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} S))

  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ {σ₂ = σ₂} (lam tm0)         = cong1 lam (trans (compositionalityᴿˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (vl ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (app tm0 vl0)     = cong2 app (compositionalityᴿˢ tm0) (compositionalityᴿˢ vl0)
  compositionalityᴿˢ {σ₂ = σ₂} (creturn vl0)     = cong1 creturn (compositionalityᴿˢ vl0)
  compositionalityᴿˢ {σ₂ = σ₂} (clet tm0 tm1)    = cong2 clet (compositionalityᴿˢ tm0) (trans (compositionalityᴿˢ tm1) (cong1 (tm1 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (vl ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (force vl0)       = cong1 force (compositionalityᴿˢ vl0)
  compositionalityᴿˢ {σ₂ = σ₂} (cif vl0 tm0 tm1) = cong3 cif (compositionalityᴿˢ vl0) (compositionalityᴿˢ tm0) (compositionalityᴿˢ tm1)
  compositionalityᴿˢ true                        = refl
  compositionalityᴿˢ false                       = refl
  compositionalityᴿˢ {σ₂ = σ₂} (thunk tm0)       = cong1 thunk (compositionalityᴿˢ tm0)
  compositionalityᴿˢ {σ₂ = σ₂} (Lam Tm0)         = cong1 Lam (trans (compositionalityᴿˢ Tm0) (cong1 (Tm0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (Tm ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (App Tm0 Tm1)     = cong2 App (compositionalityᴿˢ Tm0) (compositionalityᴿˢ Tm1)
  compositionalityᴿˢ {σ₂ = σ₂} (If Tm0 Tm1 Tm2)  = cong3 If (compositionalityᴿˢ Tm0) (compositionalityᴿˢ Tm1) (compositionalityᴿˢ Tm2)
  compositionalityᴿˢ True                        = refl
  compositionalityᴿˢ False                       = refl

  lift-dist-compˢᴿ : ((σ₁ ↑ˢ s) ⨟ ⟨ ρ₂ ↑ᴿ s ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    (t ⋯ᴿ (wkᴿ _)) ⋯ˢ ⟨ ρ₂ ↑ᴿ _ ⟩ ≡⟨ coincidence {t = t ⋯ᴿ (wkᴿ _)} ⟩ 
    (t ⋯ᴿ (wkᴿ _)) ⋯ᴿ (ρ₂ ↑ᴿ _)   ≡⟨ compositionalityᴿᴿ t ⟩ 
    t ⋯ᴿ (wkᴿ _ ∘ (ρ₂ ↑ᴿ _))    ≡⟨ sym (compositionalityᴿᴿ t) ⟩ 
    (t ⋯ᴿ ρ₂) ⋯ᴿ wkᴿ _          ≡⟨ cong1 (_⋯ᴿ (wkᴿ _)) (sym (coincidence {t = t})) ⟩ 
    (t ⋯ˢ ⟨ ρ₂ ⟩) ⋯ᴿ wkᴿ _      ∎ }

  lift-dist-comp*ˢᴿ : ∀ S → ((σ₁ ↑ˢ* S) ⨟ ⟨ ρ₂ ↑ᴿ* S ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ* S )
  lift-dist-comp*ˢᴿ []      = refl 
  lift-dist-comp*ˢᴿ {σ₁ = σ₁} (_ ∷ S) =  trans (lift-dist-compˢᴿ {σ₁ = σ₁ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} S))
 
  compositionalityˢᴿ {σ₁ = σ₁} (var x)  = sym (coincidence {t = σ₁ _ x})
  compositionalityˢᴿ {σ₁ = σ₁} (lam tm0)         = cong1 lam (trans (compositionalityˢᴿ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (vl ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (app tm0 vl0)     = cong2 app (compositionalityˢᴿ tm0) (compositionalityˢᴿ vl0)
  compositionalityˢᴿ {σ₁ = σ₁} (creturn vl0)     = cong1 creturn (compositionalityˢᴿ vl0)
  compositionalityˢᴿ {σ₁ = σ₁} (clet tm0 tm1)    = cong2 clet (compositionalityˢᴿ tm0) (trans (compositionalityˢᴿ tm1) (cong1 (tm1 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (vl ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (force vl0)       = cong1 force (compositionalityˢᴿ vl0)
  compositionalityˢᴿ {σ₁ = σ₁} (cif vl0 tm0 tm1) = cong3 cif (compositionalityˢᴿ vl0) (compositionalityˢᴿ tm0) (compositionalityˢᴿ tm1)
  compositionalityˢᴿ true                        = refl
  compositionalityˢᴿ false                       = refl
  compositionalityˢᴿ {σ₁ = σ₁} (thunk tm0)       = cong1 thunk (compositionalityˢᴿ tm0)
  compositionalityˢᴿ {σ₁ = σ₁} (Lam Tm0)         = cong1 Lam (trans (compositionalityˢᴿ Tm0) (cong1 (Tm0 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (Tm ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (App Tm0 Tm1)     = cong2 App (compositionalityˢᴿ Tm0) (compositionalityˢᴿ Tm1)
  compositionalityˢᴿ {σ₁ = σ₁} (If Tm0 Tm1 Tm2)  = cong3 If (compositionalityˢᴿ Tm0) (compositionalityˢᴿ Tm1) (compositionalityˢᴿ Tm2)
  compositionalityˢᴿ True                        = refl
  compositionalityˢᴿ False                       = refl
  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    begin
    (t ⋯ᴿ (wkᴿ _)) ⋯ˢ (σ₂ ↑ˢ _)    ≡⟨ compositionalityᴿˢ t ⟩ 
    t ⋯ˢ (⟨ (wkᴿ _) ⟩ ⨟ (σ₂ ↑ˢ _)) ≡⟨ cong1 (t ⋯ˢ_) (ext λ x → sym (coincidence {t = σ₂ _ x})) ⟩   
    t ⋯ˢ (σ₂ ⨟ ⟨ (wkᴿ _) ⟩)        ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
    (t ⋯ˢ σ₂) ⋯ᴿ (wkᴿ _)           ∎ }
  
  lift-dist-comp*ˢˢ : ∀ S →  ((σ₁ ↑ˢ* S) ⨟ (σ₂ ↑ˢ* S)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ˢˢ []      = refl 
  lift-dist-comp*ˢˢ  {σ₁ = σ₁} {σ₂ = σ₂} (_ ∷ S) =  trans (lift-dist-compˢˢ {σ₁ = σ₁ ↑ˢ* S} {σ₂ = σ₂ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} S))

  compositionalityˢˢ (var x)  = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (lam tm0)         = cong1 lam (trans (compositionalityˢˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (vl ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (app tm0 vl0)     = cong2 app (compositionalityˢˢ tm0) (compositionalityˢˢ vl0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (creturn vl0)     = cong1 creturn (compositionalityˢˢ vl0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (clet tm0 tm1)    = cong2 clet (compositionalityˢˢ tm0) (trans (compositionalityˢˢ tm1) (cong1 (tm1 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (vl ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (force vl0)       = cong1 force (compositionalityˢˢ vl0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (cif vl0 tm0 tm1) = cong3 cif (compositionalityˢˢ vl0) (compositionalityˢˢ tm0) (compositionalityˢˢ tm1)
  compositionalityˢˢ true                                  = refl
  compositionalityˢˢ false                                 = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (thunk tm0)       = cong1 thunk (compositionalityˢˢ tm0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Lam Tm0)         = cong1 Lam (trans (compositionalityˢˢ Tm0) (cong1 (Tm0 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Tm ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (App Tm0 Tm1)     = cong2 App (compositionalityˢˢ Tm0) (compositionalityˢˢ Tm1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (If Tm0 Tm1 Tm2)  = cong3 If (compositionalityˢˢ Tm0) (compositionalityˢˢ Tm1) (compositionalityˢˢ Tm2)
  compositionalityˢˢ True                                  = refl
  compositionalityˢˢ False                                 = refl

  coincidence {t = t} {ρ = ρ} = 
    t ⋯ˢ (⟨ ρ ⟩ ⨟ idˢ) ≡⟨ sym (compositionalityᴿˢ t) ⟩ 
    (t ⋯ᴿ ρ) ⋯ˢ idˢ    ≡⟨ right-idˢ _ ⟩ 
    t ⋯ᴿ ρ             ∎

  coincidence-var = refl

{-# REWRITE
  def-∙ˢ-zero def-∙ˢ-suc def-↑ˢ def-⨟   
  assoc dist interact       
  comp-idᵣ comp-idₗ η-id η-law
  right-id         
  compositionalityᴿᴿ compositionalityᴿˢ
  compositionalityˢᴿ compositionalityˢˢ
  coincidence 

  inst-var instᴿ-var
  inst-lam instᴿ-lam
  inst-app instᴿ-app
  inst-creturn instᴿ-creturn
  inst-clet instᴿ-clet
  inst-force instᴿ-force
  inst-cif instᴿ-cif
  inst-true instᴿ-true
  inst-false instᴿ-false
  inst-thunk instᴿ-thunk
  inst-Lam instᴿ-Lam
  inst-App instᴿ-App
  inst-If instᴿ-If
  inst-True instᴿ-True
  inst-False instᴿ-False
  def-id def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-∘      
  assocᴿ distᴿ interactᴿ       
  comp-idᵣᴿ comp-idₗᴿ η-idᴿ η-lawᴿ
  coincidence-var
#-}
