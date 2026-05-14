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

variable
  x x′     : S ∋ s
  t t′     : S ⊢ s
  x/t x/t′ : S ⊢[ m ] s

--! Ren {
_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 

--! [
variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂
--! ]
idᴿ : S →ᴿ S
idᴿ _ x = x

wk : ∀ s → S →ᴿ (s ∷ S)
wk _ _ = suc

_∘_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
(ρ₁ ∘ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → 
  ((s ∷ S₁) →ᴿ (s ∷ S₂))
(ρ ↑ᴿ _) _ zero    = zero
(ρ ↑ᴿ _) _ (suc x) = suc (ρ _ x)

_↑ᴿ*_ : (S₁ →ᴿ S₂) → ∀ S → ((S ++ S₁) →ᴿ (S ++ S₂))
ρ ↑ᴿ* []      = ρ
ρ ↑ᴿ* (s ∷ S) = (ρ ↑ᴿ* S) ↑ᴿ s

_⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → 
  S₂ ⊢ s 
_⋯ᴿ_ {m = V} x   ρ  = var (ρ _ x)
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

⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂ 
⟨ ρ ⟩ _ x = var (ρ _ x)
{-# INLINE ⟨_⟩ #-}

wkˢ : ∀ s → S →ˢ (s ∷ S)
wkˢ _ = ⟨ wk _ ⟩
{-# INLINE wkˢ #-}

idˢ : S →ˢ S
idˢ _ = var
{-# INLINE idˢ #-}

opaque  
  _∙_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
  _∙_  t σ _ zero = t
  (t ∙ σ) _ (suc x) = σ _ x 

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s =  (var zero) ∙ λ s₁ x → (σ _ x) ⋯ᴿ wk _

_↑ˢ*_ : (S₁ →ˢ S₂) → ∀ S → ((S ++ S₁) →ˢ (S ++ S₂))
σ ↑ˢ* [] = σ
σ ↑ˢ* (s ∷ S) = (σ ↑ˢ* S) ↑ˢ s

opaque
  unfolding  _∙_ _↑ˢ_ 
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

  lift-id            : idᴿ {S = S} ↑ᴿ s ≡ idᴿ 
  def-∙-zero           : zero ⋯ˢ (t ∙ σ)   ≡ t                             
  def-∙-suc            : suc x ⋯ˢ (t ∙ σ)  ≡ x ⋯ˢ σ 
  def-↑ˢ               : σ ↑ˢ s ≡ (var zero) ∙ (σ ⨟ wkˢ _)
  def-⨟ : (x ⋯ˢ (σ₁ ⨟ σ₂)) ≡ ((x ⋯ˢ σ₁) ⋯ˢ σ₂)

  associativity           : (σ₁ ⨟ σ₂) ⨟ σ₃                      ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  distributivityˢ         : (t ∙ σ₁) ⨟ σ₂                       ≡ ((t ⋯ˢ σ₂) ∙ (σ₁ ⨟ σ₂)) 
  distributivityᴿ         : (t ∙ σ₁) ⨟ ⟨ ρ₂ ⟩                   ≡ ((t ⋯ᴿ ρ₂) ∙ (σ₁ ⨟ ⟨ ρ₂ ⟩)) 
  interact                : wkˢ s ⨟ (t ∙ σ)                     ≡ σ                                        
  comp-idᵣ                : σ ⨟ idˢ                             ≡ σ                                               
  comp-idₗ                : idˢ ⨟ σ                             ≡ σ                                               
  η-id                    : (var (zero {s = s} {S = S})) ∙ (wkˢ _)  ≡ idˢ
  η-lawˢ                  : (zero ⋯ˢ σ) ∙ (wkˢ _ ⨟ σ)           ≡ σ
  η-lawᴿ                  : (zero ⋯ᴿ ρ) ∙ ((wkˢ _ ⨟ ⟨ ρ ⟩))     ≡ ⟨ ρ ⟩

  right-id                : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ                   ≡ t   
  compositionalityᴿᴿ      : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ t ⋯ᴿ (ρ₁ ∘ ρ₂)     
  compositionalityᴿˢ      : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                                    
  compositionalityˢᴿ      : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ t ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ t ⋯ˢ (σ₁ ⨟ σ₂)


  traversal-var           : (var x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  traversal-var = refl

  traversal-lam     : (lam tm0) ⋯ˢ σ         ≡ lam (tm0 ⋯ˢ (σ ↑ˢ* (vl ∷ [])))
  traversal-lam     = refl
  traversal-app     : (app tm0 vl0) ⋯ˢ σ     ≡ app (tm0 ⋯ˢ σ) (vl0 ⋯ˢ σ)
  traversal-app     = refl
  traversal-creturn : (creturn vl0) ⋯ˢ σ     ≡ creturn (vl0 ⋯ˢ σ)
  traversal-creturn = refl
  traversal-clet    : (clet tm0 tm1) ⋯ˢ σ    ≡ clet (tm0 ⋯ˢ σ) (tm1 ⋯ˢ (σ ↑ˢ* (vl ∷ [])))
  traversal-clet    = refl
  traversal-force   : (force vl0) ⋯ˢ σ       ≡ force (vl0 ⋯ˢ σ)
  traversal-force   = refl
  traversal-cif     : (cif vl0 tm0 tm1) ⋯ˢ σ ≡ cif (vl0 ⋯ˢ σ) (tm0 ⋯ˢ σ) (tm1 ⋯ˢ σ)
  traversal-cif     = refl
  traversal-true    : true ⋯ˢ σ              ≡ true
  traversal-true    = refl
  traversal-false   : false ⋯ˢ σ             ≡ false
  traversal-false   = refl
  traversal-thunk   : (thunk tm0) ⋯ˢ σ       ≡ thunk (tm0 ⋯ˢ σ)
  traversal-thunk   = refl
  traversal-Lam     : (Lam Tm0) ⋯ˢ σ         ≡ Lam (Tm0 ⋯ˢ (σ ↑ˢ* (Tm ∷ [])))
  traversal-Lam     = refl
  traversal-App     : (App Tm0 Tm1) ⋯ˢ σ     ≡ App (Tm0 ⋯ˢ σ) (Tm1 ⋯ˢ σ)
  traversal-App     = refl
  traversal-If      : (If Tm0 Tm1 Tm2) ⋯ˢ σ  ≡ If (Tm0 ⋯ˢ σ) (Tm1 ⋯ˢ σ) (Tm2 ⋯ˢ σ)
  traversal-If      = refl
  traversal-True    : True ⋯ˢ σ              ≡ True
  traversal-True    = refl
  traversal-False   : False ⋯ˢ σ             ≡ False
  traversal-False   = refl

  coincidence              : {x/t : S ⊢[ m ] s} → x/t ⋯ˢ ⟨ ρ ⟩ ≡ x/t ⋯ᴿ ρ
  coincidence-fold         : x/t ⋯ˢ (⟨ ρ ↑ᴿ s ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))  ≡ x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩)


  lift-id = ext λ { zero → refl; (suc x) → refl }

  def-∙-zero = refl
  def-∙-suc  = refl
  def-↑ˢ     = cong1 ((var zero) ∙_) (sym (ext λ x → coincidence))
  def-⨟      = refl

  lift-idˢ* : ∀ S → (idˢ {S = S₁} ↑ˢ* S) ≡ idˢ 
  lift-idˢ* []    = refl
  lift-idˢ* {S₁} (_ ∷ S) rewrite lift-idˢ* {S₁} S = η-lawᴿ

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

  associativity {σ₁ = σ₁} = ext λ x → compositionalityˢˢ (σ₁ _ x) 
  distributivityˢ = ext λ { zero → refl; (suc x) → refl }
  distributivityᴿ = ext λ { zero → coincidence; (suc x) → refl }
  interact        = refl
  comp-idᵣ        = ext λ x → (right-idˢ _)
  comp-idₗ        = refl
  η-id            = ext λ { zero → refl; (suc x) → refl }
  η-lawˢ          = ext λ { zero → refl; (suc x) → refl }
  η-lawᴿ          = ext λ { zero → refl; (suc x) → refl }

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
  compositionalityᴿᴿ (lam tm0)         = cong1 lam (trans (compositionalityᴿᴿ tm0) (cong1 (tm0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (vl ∷ []))))
  compositionalityᴿᴿ (app tm0 vl0)     = cong2 app (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ vl0)
  compositionalityᴿᴿ (creturn vl0)     = cong1 creturn (compositionalityᴿᴿ vl0)
  compositionalityᴿᴿ (clet tm0 tm1)    = cong2 clet (compositionalityᴿᴿ tm0) (trans (compositionalityᴿᴿ tm1) (cong1 (tm1 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (vl ∷ []))))
  compositionalityᴿᴿ (force vl0)       = cong1 force (compositionalityᴿᴿ vl0)
  compositionalityᴿᴿ (cif vl0 tm0 tm1) = cong3 cif (compositionalityᴿᴿ vl0) (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ tm1)
  compositionalityᴿᴿ true              = refl
  compositionalityᴿᴿ false             = refl
  compositionalityᴿᴿ (thunk tm0)       = cong1 thunk (compositionalityᴿᴿ tm0)
  compositionalityᴿᴿ (Lam Tm0)         = cong1 Lam (trans (compositionalityᴿᴿ Tm0) (cong1 (Tm0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (Tm ∷ []))))
  compositionalityᴿᴿ (App Tm0 Tm1)     = cong2 App (compositionalityᴿᴿ Tm0) (compositionalityᴿᴿ Tm1)
  compositionalityᴿᴿ (If Tm0 Tm1 Tm2)  = cong3 If (compositionalityᴿᴿ Tm0) (compositionalityᴿᴿ Tm1) (compositionalityᴿᴿ Tm2)
  compositionalityᴿᴿ True              = refl
  compositionalityᴿᴿ False             = refl
  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ (_ ∷ S) = trans lift-dist-compᴿˢ (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ S))

  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ (lam tm0)         = cong1 lam (trans (compositionalityᴿˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (vl ∷ []))))
  compositionalityᴿˢ (app tm0 vl0)     = cong2 app (compositionalityᴿˢ tm0) (compositionalityᴿˢ vl0)
  compositionalityᴿˢ (creturn vl0)     = cong1 creturn (compositionalityᴿˢ vl0)
  compositionalityᴿˢ (clet tm0 tm1)    = cong2 clet (compositionalityᴿˢ tm0) (trans (compositionalityᴿˢ tm1) (cong1 (tm1 ⋯ˢ_) (lift-dist-comp*ᴿˢ (vl ∷ []))))
  compositionalityᴿˢ (force vl0)       = cong1 force (compositionalityᴿˢ vl0)
  compositionalityᴿˢ (cif vl0 tm0 tm1) = cong3 cif (compositionalityᴿˢ vl0) (compositionalityᴿˢ tm0) (compositionalityᴿˢ tm1)
  compositionalityᴿˢ true              = refl
  compositionalityᴿˢ false             = refl
  compositionalityᴿˢ (thunk tm0)       = cong1 thunk (compositionalityᴿˢ tm0)
  compositionalityᴿˢ (Lam Tm0)         = cong1 Lam (trans (compositionalityᴿˢ Tm0) (cong1 (Tm0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (Tm ∷ []))))
  compositionalityᴿˢ (App Tm0 Tm1)     = cong2 App (compositionalityᴿˢ Tm0) (compositionalityᴿˢ Tm1)
  compositionalityᴿˢ (If Tm0 Tm1 Tm2)  = cong3 If (compositionalityᴿˢ Tm0) (compositionalityᴿˢ Tm1) (compositionalityᴿˢ Tm2)
  compositionalityᴿˢ True              = refl
  compositionalityᴿˢ False             = refl
  lift-dist-compˢᴿ : ((σ₁ ↑ˢ s) ⨟ ⟨ ρ₂ ↑ᴿ s ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    (t ⋯ᴿ (wk _)) ⋯ˢ ⟨ ρ₂ ↑ᴿ _ ⟩ ≡⟨ coincidence ⟩ 
    (t ⋯ᴿ (wk _)) ⋯ᴿ (ρ₂ ↑ᴿ _)   ≡⟨ compositionalityᴿᴿ t ⟩ 
    t ⋯ᴿ (wk _ ∘ (ρ₂ ↑ᴿ _))    ≡⟨ sym (compositionalityᴿᴿ t) ⟩ 
    (t ⋯ᴿ ρ₂) ⋯ᴿ wk _          ≡⟨ cong1 (_⋯ᴿ (wk _)) (sym coincidence) ⟩ 
    (t ⋯ˢ ⟨ ρ₂ ⟩) ⋯ᴿ wk _      ∎ }

  lift-dist-comp*ˢᴿ : ∀ S → ((σ₁ ↑ˢ* S) ⨟ ⟨ ρ₂ ↑ᴿ* S ⟩) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ↑ˢ* S )
  lift-dist-comp*ˢᴿ []      = refl 
  lift-dist-comp*ˢᴿ (_ ∷ S) =  trans lift-dist-compˢᴿ (cong1 (_↑ˢ _) (lift-dist-comp*ˢᴿ S))
 
  compositionalityˢᴿ (var x)  = sym coincidence
  compositionalityˢᴿ (lam tm0)         = cong1 lam (trans (compositionalityˢᴿ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (vl ∷ []))))
  compositionalityˢᴿ (app tm0 vl0)     = cong2 app (compositionalityˢᴿ tm0) (compositionalityˢᴿ vl0)
  compositionalityˢᴿ (creturn vl0)     = cong1 creturn (compositionalityˢᴿ vl0)
  compositionalityˢᴿ (clet tm0 tm1)    = cong2 clet (compositionalityˢᴿ tm0) (trans (compositionalityˢᴿ tm1) (cong1 (tm1 ⋯ˢ_) (lift-dist-comp*ˢᴿ (vl ∷ []))))
  compositionalityˢᴿ (force vl0)       = cong1 force (compositionalityˢᴿ vl0)
  compositionalityˢᴿ (cif vl0 tm0 tm1) = cong3 cif (compositionalityˢᴿ vl0) (compositionalityˢᴿ tm0) (compositionalityˢᴿ tm1)
  compositionalityˢᴿ true              = refl
  compositionalityˢᴿ false             = refl
  compositionalityˢᴿ (thunk tm0)       = cong1 thunk (compositionalityˢᴿ tm0)
  compositionalityˢᴿ (Lam Tm0)         = cong1 Lam (trans (compositionalityˢᴿ Tm0) (cong1 (Tm0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (Tm ∷ []))))
  compositionalityˢᴿ (App Tm0 Tm1)     = cong2 App (compositionalityˢᴿ Tm0) (compositionalityˢᴿ Tm1)
  compositionalityˢᴿ (If Tm0 Tm1 Tm2)  = cong3 If (compositionalityˢᴿ Tm0) (compositionalityˢᴿ Tm1) (compositionalityˢᴿ Tm2)
  compositionalityˢᴿ True              = refl
  compositionalityˢᴿ False             = refl
  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    begin
    (t ⋯ᴿ (wk _)) ⋯ˢ (σ₂ ↑ˢ _)    ≡⟨ compositionalityᴿˢ t ⟩ 
    t ⋯ˢ (⟨ (wk _) ⟩ ⨟ (σ₂ ↑ˢ _)) ≡⟨ cong1 (t ⋯ˢ_) (ext λ y → sym coincidence) ⟩   
    t ⋯ˢ (σ₂ ⨟ ⟨ (wk _) ⟩)        ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
    (t ⋯ˢ σ₂) ⋯ᴿ (wk _)           ∎ }
  
  lift-dist-comp*ˢˢ : ∀ S →  ((σ₁ ↑ˢ* S) ⨟ (σ₂ ↑ˢ* S)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ˢˢ []      = refl 
  lift-dist-comp*ˢˢ (_ ∷ S) =  trans lift-dist-compˢˢ (cong1 (_↑ˢ _) (lift-dist-comp*ˢˢ S))

  compositionalityˢˢ (var x)  = refl
  compositionalityˢˢ (lam tm0)         = cong1 lam (trans (compositionalityˢˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢˢ (vl ∷ []))))
  compositionalityˢˢ (app tm0 vl0)     = cong2 app (compositionalityˢˢ tm0) (compositionalityˢˢ vl0)
  compositionalityˢˢ (creturn vl0)     = cong1 creturn (compositionalityˢˢ vl0)
  compositionalityˢˢ (clet tm0 tm1)    = cong2 clet (compositionalityˢˢ tm0) (trans (compositionalityˢˢ tm1) (cong1 (tm1 ⋯ˢ_) (lift-dist-comp*ˢˢ (vl ∷ []))))
  compositionalityˢˢ (force vl0)       = cong1 force (compositionalityˢˢ vl0)
  compositionalityˢˢ (cif vl0 tm0 tm1) = cong3 cif (compositionalityˢˢ vl0) (compositionalityˢˢ tm0) (compositionalityˢˢ tm1)
  compositionalityˢˢ true              = refl
  compositionalityˢˢ false             = refl
  compositionalityˢˢ (thunk tm0)       = cong1 thunk (compositionalityˢˢ tm0)
  compositionalityˢˢ (Lam Tm0)         = cong1 Lam (trans (compositionalityˢˢ Tm0) (cong1 (Tm0 ⋯ˢ_) (lift-dist-comp*ˢˢ (Tm ∷ []))))
  compositionalityˢˢ (App Tm0 Tm1)     = cong2 App (compositionalityˢˢ Tm0) (compositionalityˢˢ Tm1)
  compositionalityˢˢ (If Tm0 Tm1 Tm2)  = cong3 If (compositionalityˢˢ Tm0) (compositionalityˢˢ Tm1) (compositionalityˢˢ Tm2)
  compositionalityˢˢ True              = refl
  compositionalityˢˢ False             = refl
  coincidence {m = V} = refl
  coincidence {m = T} {ρ = ρ} {x/t = x/t} = 
    x/t ⋯ˢ (⟨ ρ ⟩ ⨟ idˢ) ≡⟨ sym (compositionalityᴿˢ x/t) ⟩ 
    (x/t ⋯ᴿ ρ) ⋯ˢ idˢ    ≡⟨ right-idˢ _ ⟩ 
    x/t ⋯ᴿ ρ             ∎

  coincidence-fold {x/t = x/t} {ρ = ρ} {x/t′ = x/t′} = 
    (x/t ⋯ˢ (⟨ ρ ↑ᴿ _ ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))) ≡⟨ cong1 (x/t ⋯ˢ_) (ext λ { zero → refl; (suc x) → refl }) ⟩ 
    (x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩))              ∎

{-# REWRITE
  lift-id def-∙-zero def-∙-suc def-↑ˢ def-⨟
  associativity distributivityˢ distributivityᴿ interact
  comp-idᵣ comp-idₗ η-id η-lawˢ η-lawᴿ
  traversal-var traversal-lam traversal-app traversal-creturn traversal-clet traversal-force traversal-cif traversal-true traversal-false traversal-thunk traversal-Lam traversal-App traversal-If traversal-True traversal-False
  right-id
  compositionalityᴿˢ compositionalityᴿᴿ
  compositionalityˢᴿ compositionalityˢˢ
  coincidence coincidence-fold
#-}
