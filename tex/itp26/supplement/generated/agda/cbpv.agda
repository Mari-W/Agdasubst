{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module cbpv where
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
  valtype comptype value comp bool : Sort

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

  zeroo  : S ⊢ valtype
  one    : S ⊢ valtype
  U      : S ⊢ comptype → S ⊢ valtype
  Sigma  : S ⊢ valtype → S ⊢ valtype → S ⊢ valtype
  cross  : S ⊢ valtype → S ⊢ valtype → S ⊢ valtype
  cone   : S ⊢ comptype
  F      : S ⊢ valtype → S ⊢ comptype
  Pi     : S ⊢ comptype → S ⊢ comptype → S ⊢ comptype
  arrow  : S ⊢ valtype → S ⊢ comptype → S ⊢ comptype
  u      : S ⊢ value
  pair   : S ⊢ value → S ⊢ value → S ⊢ value
  inj    : S ⊢ bool → S ⊢ value → S ⊢ value
  thunk  : S ⊢ comp → S ⊢ value
  cu     : S ⊢ comp
  force  : S ⊢ value → S ⊢ comp
  lambda : (value ∷ S) ⊢ comp → S ⊢ comp
  app    : S ⊢ comp → S ⊢ value → S ⊢ comp
  tuple  : S ⊢ comp → S ⊢ comp → S ⊢ comp
  ret    : S ⊢ value → S ⊢ comp
  letin  : S ⊢ comp → (value ∷ S) ⊢ comp → S ⊢ comp
  proj   : S ⊢ bool → S ⊢ comp → S ⊢ comp
  caseZ  : S ⊢ value → S ⊢ comp
  caseS  : S ⊢ value → (value ∷ S) ⊢ comp → (value ∷ S) ⊢ comp → S ⊢ comp
  caseP  : S ⊢ value → (value ∷ value ∷ S) ⊢ comp → S ⊢ comp

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

zeroo                      ⋯ᴿ ρ = zeroo
one                        ⋯ᴿ ρ = one
(U comptype0)              ⋯ᴿ ρ = U (comptype0 ⋯ᴿ ρ)
(Sigma valtype0 valtype1)  ⋯ᴿ ρ = Sigma (valtype0 ⋯ᴿ ρ) (valtype1 ⋯ᴿ ρ)
(cross valtype0 valtype1)  ⋯ᴿ ρ = cross (valtype0 ⋯ᴿ ρ) (valtype1 ⋯ᴿ ρ)
cone                       ⋯ᴿ ρ = cone
(F valtype0)               ⋯ᴿ ρ = F (valtype0 ⋯ᴿ ρ)
(Pi comptype0 comptype1)   ⋯ᴿ ρ = Pi (comptype0 ⋯ᴿ ρ) (comptype1 ⋯ᴿ ρ)
(arrow valtype0 comptype0) ⋯ᴿ ρ = arrow (valtype0 ⋯ᴿ ρ) (comptype0 ⋯ᴿ ρ)
u                          ⋯ᴿ ρ = u
(pair value0 value1)       ⋯ᴿ ρ = pair (value0 ⋯ᴿ ρ) (value1 ⋯ᴿ ρ)
(inj bool0 value0)         ⋯ᴿ ρ = inj (bool0 ⋯ᴿ ρ) (value0 ⋯ᴿ ρ)
(thunk comp0)              ⋯ᴿ ρ = thunk (comp0 ⋯ᴿ ρ)
cu                         ⋯ᴿ ρ = cu
(force value0)             ⋯ᴿ ρ = force (value0 ⋯ᴿ ρ)
(lambda comp0)             ⋯ᴿ ρ = lambda (comp0 ⋯ᴿ (ρ ↑ᴿ* _))
(app comp0 value0)         ⋯ᴿ ρ = app (comp0 ⋯ᴿ ρ) (value0 ⋯ᴿ ρ)
(tuple comp0 comp1)        ⋯ᴿ ρ = tuple (comp0 ⋯ᴿ ρ) (comp1 ⋯ᴿ ρ)
(ret value0)               ⋯ᴿ ρ = ret (value0 ⋯ᴿ ρ)
(letin comp0 comp1)        ⋯ᴿ ρ = letin (comp0 ⋯ᴿ ρ) (comp1 ⋯ᴿ (ρ ↑ᴿ* _))
(proj bool0 comp0)         ⋯ᴿ ρ = proj (bool0 ⋯ᴿ ρ) (comp0 ⋯ᴿ ρ)
(caseZ value0)             ⋯ᴿ ρ = caseZ (value0 ⋯ᴿ ρ)
(caseS value0 comp0 comp1) ⋯ᴿ ρ = caseS (value0 ⋯ᴿ ρ) (comp0 ⋯ᴿ (ρ ↑ᴿ* _)) (comp1 ⋯ᴿ (ρ ↑ᴿ* _))
(caseP value0 comp0)       ⋯ᴿ ρ = caseP (value0 ⋯ᴿ ρ) (comp0 ⋯ᴿ (ρ ↑ᴿ* _))

variable
  bool0 : S ⊢ bool
  comp0 comp1 : S ⊢ comp
  comptype0 comptype1 : S ⊢ comptype
  valtype0 valtype1 : S ⊢ valtype
  value0 value1 : S ⊢ value

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

  zeroo                      ⋯ˢ σ = zeroo
  one                        ⋯ˢ σ = one
  (U comptype0)              ⋯ˢ σ = U (comptype0 ⋯ˢ σ)
  (Sigma valtype0 valtype1)  ⋯ˢ σ = Sigma (valtype0 ⋯ˢ σ) (valtype1 ⋯ˢ σ)
  (cross valtype0 valtype1)  ⋯ˢ σ = cross (valtype0 ⋯ˢ σ) (valtype1 ⋯ˢ σ)
  cone                       ⋯ˢ σ = cone
  (F valtype0)               ⋯ˢ σ = F (valtype0 ⋯ˢ σ)
  (Pi comptype0 comptype1)   ⋯ˢ σ = Pi (comptype0 ⋯ˢ σ) (comptype1 ⋯ˢ σ)
  (arrow valtype0 comptype0) ⋯ˢ σ = arrow (valtype0 ⋯ˢ σ) (comptype0 ⋯ˢ σ)
  u                          ⋯ˢ σ = u
  (pair value0 value1)       ⋯ˢ σ = pair (value0 ⋯ˢ σ) (value1 ⋯ˢ σ)
  (inj bool0 value0)         ⋯ˢ σ = inj (bool0 ⋯ˢ σ) (value0 ⋯ˢ σ)
  (thunk comp0)              ⋯ˢ σ = thunk (comp0 ⋯ˢ σ)
  cu                         ⋯ˢ σ = cu
  (force value0)             ⋯ˢ σ = force (value0 ⋯ˢ σ)
  (lambda comp0)             ⋯ˢ σ = lambda (comp0 ⋯ˢ (σ ↑ˢ* _))
  (app comp0 value0)         ⋯ˢ σ = app (comp0 ⋯ˢ σ) (value0 ⋯ˢ σ)
  (tuple comp0 comp1)        ⋯ˢ σ = tuple (comp0 ⋯ˢ σ) (comp1 ⋯ˢ σ)
  (ret value0)               ⋯ˢ σ = ret (value0 ⋯ˢ σ)
  (letin comp0 comp1)        ⋯ˢ σ = letin (comp0 ⋯ˢ σ) (comp1 ⋯ˢ (σ ↑ˢ* _))
  (proj bool0 comp0)         ⋯ˢ σ = proj (bool0 ⋯ˢ σ) (comp0 ⋯ˢ σ)
  (caseZ value0)             ⋯ˢ σ = caseZ (value0 ⋯ˢ σ)
  (caseS value0 comp0 comp1) ⋯ˢ σ = caseS (value0 ⋯ˢ σ) (comp0 ⋯ˢ (σ ↑ˢ* _)) (comp1 ⋯ˢ (σ ↑ˢ* _))
  (caseP value0 comp0)       ⋯ˢ σ = caseP (value0 ⋯ˢ σ) (comp0 ⋯ˢ (σ ↑ˢ* _))

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

  traversal-zeroo  : zeroo ⋯ˢ σ                      ≡ zeroo
  traversal-zeroo  = refl
  traversal-one    : one ⋯ˢ σ                        ≡ one
  traversal-one    = refl
  traversal-U      : (U comptype0) ⋯ˢ σ              ≡ U (comptype0 ⋯ˢ σ)
  traversal-U      = refl
  traversal-Sigma  : (Sigma valtype0 valtype1) ⋯ˢ σ  ≡ Sigma (valtype0 ⋯ˢ σ) (valtype1 ⋯ˢ σ)
  traversal-Sigma  = refl
  traversal-cross  : (cross valtype0 valtype1) ⋯ˢ σ  ≡ cross (valtype0 ⋯ˢ σ) (valtype1 ⋯ˢ σ)
  traversal-cross  = refl
  traversal-cone   : cone ⋯ˢ σ                       ≡ cone
  traversal-cone   = refl
  traversal-F      : (F valtype0) ⋯ˢ σ               ≡ F (valtype0 ⋯ˢ σ)
  traversal-F      = refl
  traversal-Pi     : (Pi comptype0 comptype1) ⋯ˢ σ   ≡ Pi (comptype0 ⋯ˢ σ) (comptype1 ⋯ˢ σ)
  traversal-Pi     = refl
  traversal-arrow  : (arrow valtype0 comptype0) ⋯ˢ σ ≡ arrow (valtype0 ⋯ˢ σ) (comptype0 ⋯ˢ σ)
  traversal-arrow  = refl
  traversal-u      : u ⋯ˢ σ                          ≡ u
  traversal-u      = refl
  traversal-pair   : (pair value0 value1) ⋯ˢ σ       ≡ pair (value0 ⋯ˢ σ) (value1 ⋯ˢ σ)
  traversal-pair   = refl
  traversal-inj    : (inj bool0 value0) ⋯ˢ σ         ≡ inj (bool0 ⋯ˢ σ) (value0 ⋯ˢ σ)
  traversal-inj    = refl
  traversal-thunk  : (thunk comp0) ⋯ˢ σ              ≡ thunk (comp0 ⋯ˢ σ)
  traversal-thunk  = refl
  traversal-cu     : cu ⋯ˢ σ                         ≡ cu
  traversal-cu     = refl
  traversal-force  : (force value0) ⋯ˢ σ             ≡ force (value0 ⋯ˢ σ)
  traversal-force  = refl
  traversal-lambda : (lambda comp0) ⋯ˢ σ             ≡ lambda (comp0 ⋯ˢ (σ ↑ˢ* (value ∷ [])))
  traversal-lambda = refl
  traversal-app    : (app comp0 value0) ⋯ˢ σ         ≡ app (comp0 ⋯ˢ σ) (value0 ⋯ˢ σ)
  traversal-app    = refl
  traversal-tuple  : (tuple comp0 comp1) ⋯ˢ σ        ≡ tuple (comp0 ⋯ˢ σ) (comp1 ⋯ˢ σ)
  traversal-tuple  = refl
  traversal-ret    : (ret value0) ⋯ˢ σ               ≡ ret (value0 ⋯ˢ σ)
  traversal-ret    = refl
  traversal-letin  : (letin comp0 comp1) ⋯ˢ σ        ≡ letin (comp0 ⋯ˢ σ) (comp1 ⋯ˢ (σ ↑ˢ* (value ∷ [])))
  traversal-letin  = refl
  traversal-proj   : (proj bool0 comp0) ⋯ˢ σ         ≡ proj (bool0 ⋯ˢ σ) (comp0 ⋯ˢ σ)
  traversal-proj   = refl
  traversal-caseZ  : (caseZ value0) ⋯ˢ σ             ≡ caseZ (value0 ⋯ˢ σ)
  traversal-caseZ  = refl
  traversal-caseS  : (caseS value0 comp0 comp1) ⋯ˢ σ ≡ caseS (value0 ⋯ˢ σ) (comp0 ⋯ˢ (σ ↑ˢ* (value ∷ []))) (comp1 ⋯ˢ (σ ↑ˢ* (value ∷ [])))
  traversal-caseS  = refl
  traversal-caseP  : (caseP value0 comp0) ⋯ˢ σ       ≡ caseP (value0 ⋯ˢ σ) (comp0 ⋯ˢ (σ ↑ˢ* (value ∷ value ∷ [])))
  traversal-caseP  = refl

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

  right-idˢ zeroo                      = refl
  right-idˢ one                        = refl
  right-idˢ (U comptype0)              = cong1 U (right-idˢ comptype0)
  right-idˢ (Sigma valtype0 valtype1)  = cong2 Sigma (right-idˢ valtype0) (right-idˢ valtype1)
  right-idˢ (cross valtype0 valtype1)  = cong2 cross (right-idˢ valtype0) (right-idˢ valtype1)
  right-idˢ cone                       = refl
  right-idˢ (F valtype0)               = cong1 F (right-idˢ valtype0)
  right-idˢ (Pi comptype0 comptype1)   = cong2 Pi (right-idˢ comptype0) (right-idˢ comptype1)
  right-idˢ (arrow valtype0 comptype0) = cong2 arrow (right-idˢ valtype0) (right-idˢ comptype0)
  right-idˢ u                          = refl
  right-idˢ (pair value0 value1)       = cong2 pair (right-idˢ value0) (right-idˢ value1)
  right-idˢ (inj bool0 value0)         = cong2 inj (right-idˢ bool0) (right-idˢ value0)
  right-idˢ (thunk comp0)              = cong1 thunk (right-idˢ comp0)
  right-idˢ cu                         = refl
  right-idˢ (force value0)             = cong1 force (right-idˢ value0)
  right-idˢ (lambda comp0)             = cong1 lambda (trans (cong1 (comp0 ⋯ˢ_) (lift-idˢ* (value ∷ []))) (right-idˢ comp0))
  right-idˢ (app comp0 value0)         = cong2 app (right-idˢ comp0) (right-idˢ value0)
  right-idˢ (tuple comp0 comp1)        = cong2 tuple (right-idˢ comp0) (right-idˢ comp1)
  right-idˢ (ret value0)               = cong1 ret (right-idˢ value0)
  right-idˢ (letin comp0 comp1)        = cong2 letin (right-idˢ comp0) (trans (cong1 (comp1 ⋯ˢ_) (lift-idˢ* (value ∷ []))) (right-idˢ comp1))
  right-idˢ (proj bool0 comp0)         = cong2 proj (right-idˢ bool0) (right-idˢ comp0)
  right-idˢ (caseZ value0)             = cong1 caseZ (right-idˢ value0)
  right-idˢ (caseS value0 comp0 comp1) = cong3 caseS (right-idˢ value0) (trans (cong1 (comp0 ⋯ˢ_) (lift-idˢ* (value ∷ []))) (right-idˢ comp0)) (trans (cong1 (comp1 ⋯ˢ_) (lift-idˢ* (value ∷ []))) (right-idˢ comp1))
  right-idˢ (caseP value0 comp0)       = cong2 caseP (right-idˢ value0) (trans (cong1 (comp0 ⋯ˢ_) (lift-idˢ* (value ∷ value ∷ []))) (right-idˢ comp0))

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

  right-id zeroo                      = refl
  right-id one                        = refl
  right-id (U comptype0)              = cong1 U (right-id comptype0)
  right-id (Sigma valtype0 valtype1)  = cong2 Sigma (right-id valtype0) (right-id valtype1)
  right-id (cross valtype0 valtype1)  = cong2 cross (right-id valtype0) (right-id valtype1)
  right-id cone                       = refl
  right-id (F valtype0)               = cong1 F (right-id valtype0)
  right-id (Pi comptype0 comptype1)   = cong2 Pi (right-id comptype0) (right-id comptype1)
  right-id (arrow valtype0 comptype0) = cong2 arrow (right-id valtype0) (right-id comptype0)
  right-id u                          = refl
  right-id (pair value0 value1)       = cong2 pair (right-id value0) (right-id value1)
  right-id (inj bool0 value0)         = cong2 inj (right-id bool0) (right-id value0)
  right-id (thunk comp0)              = cong1 thunk (right-id comp0)
  right-id cu                         = refl
  right-id (force value0)             = cong1 force (right-id value0)
  right-id (lambda comp0)             = cong1 lambda (trans (cong1 (comp0 ⋯ᴿ_) (lift-id* (value ∷ []))) (right-id comp0))
  right-id (app comp0 value0)         = cong2 app (right-id comp0) (right-id value0)
  right-id (tuple comp0 comp1)        = cong2 tuple (right-id comp0) (right-id comp1)
  right-id (ret value0)               = cong1 ret (right-id value0)
  right-id (letin comp0 comp1)        = cong2 letin (right-id comp0) (trans (cong1 (comp1 ⋯ᴿ_) (lift-id* (value ∷ []))) (right-id comp1))
  right-id (proj bool0 comp0)         = cong2 proj (right-id bool0) (right-id comp0)
  right-id (caseZ value0)             = cong1 caseZ (right-id value0)
  right-id (caseS value0 comp0 comp1) = cong3 caseS (right-id value0) (trans (cong1 (comp0 ⋯ᴿ_) (lift-id* (value ∷ []))) (right-id comp0)) (trans (cong1 (comp1 ⋯ᴿ_) (lift-id* (value ∷ []))) (right-id comp1))
  right-id (caseP value0 comp0)       = cong2 caseP (right-id value0) (trans (cong1 (comp0 ⋯ᴿ_) (lift-id* (value ∷ value ∷ []))) (right-id comp0))
  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ zeroo                      = refl
  compositionalityᴿᴿ one                        = refl
  compositionalityᴿᴿ (U comptype0)              = cong1 U (compositionalityᴿᴿ comptype0)
  compositionalityᴿᴿ (Sigma valtype0 valtype1)  = cong2 Sigma (compositionalityᴿᴿ valtype0) (compositionalityᴿᴿ valtype1)
  compositionalityᴿᴿ (cross valtype0 valtype1)  = cong2 cross (compositionalityᴿᴿ valtype0) (compositionalityᴿᴿ valtype1)
  compositionalityᴿᴿ cone                       = refl
  compositionalityᴿᴿ (F valtype0)               = cong1 F (compositionalityᴿᴿ valtype0)
  compositionalityᴿᴿ (Pi comptype0 comptype1)   = cong2 Pi (compositionalityᴿᴿ comptype0) (compositionalityᴿᴿ comptype1)
  compositionalityᴿᴿ (arrow valtype0 comptype0) = cong2 arrow (compositionalityᴿᴿ valtype0) (compositionalityᴿᴿ comptype0)
  compositionalityᴿᴿ u                          = refl
  compositionalityᴿᴿ (pair value0 value1)       = cong2 pair (compositionalityᴿᴿ value0) (compositionalityᴿᴿ value1)
  compositionalityᴿᴿ (inj bool0 value0)         = cong2 inj (compositionalityᴿᴿ bool0) (compositionalityᴿᴿ value0)
  compositionalityᴿᴿ (thunk comp0)              = cong1 thunk (compositionalityᴿᴿ comp0)
  compositionalityᴿᴿ cu                         = refl
  compositionalityᴿᴿ (force value0)             = cong1 force (compositionalityᴿᴿ value0)
  compositionalityᴿᴿ (lambda comp0)             = cong1 lambda (trans (compositionalityᴿᴿ comp0) (cong1 (comp0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (value ∷ []))))
  compositionalityᴿᴿ (app comp0 value0)         = cong2 app (compositionalityᴿᴿ comp0) (compositionalityᴿᴿ value0)
  compositionalityᴿᴿ (tuple comp0 comp1)        = cong2 tuple (compositionalityᴿᴿ comp0) (compositionalityᴿᴿ comp1)
  compositionalityᴿᴿ (ret value0)               = cong1 ret (compositionalityᴿᴿ value0)
  compositionalityᴿᴿ (letin comp0 comp1)        = cong2 letin (compositionalityᴿᴿ comp0) (trans (compositionalityᴿᴿ comp1) (cong1 (comp1 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (value ∷ []))))
  compositionalityᴿᴿ (proj bool0 comp0)         = cong2 proj (compositionalityᴿᴿ bool0) (compositionalityᴿᴿ comp0)
  compositionalityᴿᴿ (caseZ value0)             = cong1 caseZ (compositionalityᴿᴿ value0)
  compositionalityᴿᴿ (caseS value0 comp0 comp1) = cong3 caseS (compositionalityᴿᴿ value0) (trans (compositionalityᴿᴿ comp0) (cong1 (comp0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (value ∷ [])))) (trans (compositionalityᴿᴿ comp1) (cong1 (comp1 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (value ∷ []))))
  compositionalityᴿᴿ (caseP value0 comp0)       = cong2 caseP (compositionalityᴿᴿ value0) (trans (compositionalityᴿᴿ comp0) (cong1 (comp0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (value ∷ value ∷ []))))
  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ (_ ∷ S) = trans lift-dist-compᴿˢ (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ S))

  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ zeroo                      = refl
  compositionalityᴿˢ one                        = refl
  compositionalityᴿˢ (U comptype0)              = cong1 U (compositionalityᴿˢ comptype0)
  compositionalityᴿˢ (Sigma valtype0 valtype1)  = cong2 Sigma (compositionalityᴿˢ valtype0) (compositionalityᴿˢ valtype1)
  compositionalityᴿˢ (cross valtype0 valtype1)  = cong2 cross (compositionalityᴿˢ valtype0) (compositionalityᴿˢ valtype1)
  compositionalityᴿˢ cone                       = refl
  compositionalityᴿˢ (F valtype0)               = cong1 F (compositionalityᴿˢ valtype0)
  compositionalityᴿˢ (Pi comptype0 comptype1)   = cong2 Pi (compositionalityᴿˢ comptype0) (compositionalityᴿˢ comptype1)
  compositionalityᴿˢ (arrow valtype0 comptype0) = cong2 arrow (compositionalityᴿˢ valtype0) (compositionalityᴿˢ comptype0)
  compositionalityᴿˢ u                          = refl
  compositionalityᴿˢ (pair value0 value1)       = cong2 pair (compositionalityᴿˢ value0) (compositionalityᴿˢ value1)
  compositionalityᴿˢ (inj bool0 value0)         = cong2 inj (compositionalityᴿˢ bool0) (compositionalityᴿˢ value0)
  compositionalityᴿˢ (thunk comp0)              = cong1 thunk (compositionalityᴿˢ comp0)
  compositionalityᴿˢ cu                         = refl
  compositionalityᴿˢ (force value0)             = cong1 force (compositionalityᴿˢ value0)
  compositionalityᴿˢ (lambda comp0)             = cong1 lambda (trans (compositionalityᴿˢ comp0) (cong1 (comp0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (value ∷ []))))
  compositionalityᴿˢ (app comp0 value0)         = cong2 app (compositionalityᴿˢ comp0) (compositionalityᴿˢ value0)
  compositionalityᴿˢ (tuple comp0 comp1)        = cong2 tuple (compositionalityᴿˢ comp0) (compositionalityᴿˢ comp1)
  compositionalityᴿˢ (ret value0)               = cong1 ret (compositionalityᴿˢ value0)
  compositionalityᴿˢ (letin comp0 comp1)        = cong2 letin (compositionalityᴿˢ comp0) (trans (compositionalityᴿˢ comp1) (cong1 (comp1 ⋯ˢ_) (lift-dist-comp*ᴿˢ (value ∷ []))))
  compositionalityᴿˢ (proj bool0 comp0)         = cong2 proj (compositionalityᴿˢ bool0) (compositionalityᴿˢ comp0)
  compositionalityᴿˢ (caseZ value0)             = cong1 caseZ (compositionalityᴿˢ value0)
  compositionalityᴿˢ (caseS value0 comp0 comp1) = cong3 caseS (compositionalityᴿˢ value0) (trans (compositionalityᴿˢ comp0) (cong1 (comp0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (value ∷ [])))) (trans (compositionalityᴿˢ comp1) (cong1 (comp1 ⋯ˢ_) (lift-dist-comp*ᴿˢ (value ∷ []))))
  compositionalityᴿˢ (caseP value0 comp0)       = cong2 caseP (compositionalityᴿˢ value0) (trans (compositionalityᴿˢ comp0) (cong1 (comp0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (value ∷ value ∷ []))))
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
  compositionalityˢᴿ zeroo                      = refl
  compositionalityˢᴿ one                        = refl
  compositionalityˢᴿ (U comptype0)              = cong1 U (compositionalityˢᴿ comptype0)
  compositionalityˢᴿ (Sigma valtype0 valtype1)  = cong2 Sigma (compositionalityˢᴿ valtype0) (compositionalityˢᴿ valtype1)
  compositionalityˢᴿ (cross valtype0 valtype1)  = cong2 cross (compositionalityˢᴿ valtype0) (compositionalityˢᴿ valtype1)
  compositionalityˢᴿ cone                       = refl
  compositionalityˢᴿ (F valtype0)               = cong1 F (compositionalityˢᴿ valtype0)
  compositionalityˢᴿ (Pi comptype0 comptype1)   = cong2 Pi (compositionalityˢᴿ comptype0) (compositionalityˢᴿ comptype1)
  compositionalityˢᴿ (arrow valtype0 comptype0) = cong2 arrow (compositionalityˢᴿ valtype0) (compositionalityˢᴿ comptype0)
  compositionalityˢᴿ u                          = refl
  compositionalityˢᴿ (pair value0 value1)       = cong2 pair (compositionalityˢᴿ value0) (compositionalityˢᴿ value1)
  compositionalityˢᴿ (inj bool0 value0)         = cong2 inj (compositionalityˢᴿ bool0) (compositionalityˢᴿ value0)
  compositionalityˢᴿ (thunk comp0)              = cong1 thunk (compositionalityˢᴿ comp0)
  compositionalityˢᴿ cu                         = refl
  compositionalityˢᴿ (force value0)             = cong1 force (compositionalityˢᴿ value0)
  compositionalityˢᴿ (lambda comp0)             = cong1 lambda (trans (compositionalityˢᴿ comp0) (cong1 (comp0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (value ∷ []))))
  compositionalityˢᴿ (app comp0 value0)         = cong2 app (compositionalityˢᴿ comp0) (compositionalityˢᴿ value0)
  compositionalityˢᴿ (tuple comp0 comp1)        = cong2 tuple (compositionalityˢᴿ comp0) (compositionalityˢᴿ comp1)
  compositionalityˢᴿ (ret value0)               = cong1 ret (compositionalityˢᴿ value0)
  compositionalityˢᴿ (letin comp0 comp1)        = cong2 letin (compositionalityˢᴿ comp0) (trans (compositionalityˢᴿ comp1) (cong1 (comp1 ⋯ˢ_) (lift-dist-comp*ˢᴿ (value ∷ []))))
  compositionalityˢᴿ (proj bool0 comp0)         = cong2 proj (compositionalityˢᴿ bool0) (compositionalityˢᴿ comp0)
  compositionalityˢᴿ (caseZ value0)             = cong1 caseZ (compositionalityˢᴿ value0)
  compositionalityˢᴿ (caseS value0 comp0 comp1) = cong3 caseS (compositionalityˢᴿ value0) (trans (compositionalityˢᴿ comp0) (cong1 (comp0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (value ∷ [])))) (trans (compositionalityˢᴿ comp1) (cong1 (comp1 ⋯ˢ_) (lift-dist-comp*ˢᴿ (value ∷ []))))
  compositionalityˢᴿ (caseP value0 comp0)       = cong2 caseP (compositionalityˢᴿ value0) (trans (compositionalityˢᴿ comp0) (cong1 (comp0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (value ∷ value ∷ []))))
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
  compositionalityˢˢ zeroo                      = refl
  compositionalityˢˢ one                        = refl
  compositionalityˢˢ (U comptype0)              = cong1 U (compositionalityˢˢ comptype0)
  compositionalityˢˢ (Sigma valtype0 valtype1)  = cong2 Sigma (compositionalityˢˢ valtype0) (compositionalityˢˢ valtype1)
  compositionalityˢˢ (cross valtype0 valtype1)  = cong2 cross (compositionalityˢˢ valtype0) (compositionalityˢˢ valtype1)
  compositionalityˢˢ cone                       = refl
  compositionalityˢˢ (F valtype0)               = cong1 F (compositionalityˢˢ valtype0)
  compositionalityˢˢ (Pi comptype0 comptype1)   = cong2 Pi (compositionalityˢˢ comptype0) (compositionalityˢˢ comptype1)
  compositionalityˢˢ (arrow valtype0 comptype0) = cong2 arrow (compositionalityˢˢ valtype0) (compositionalityˢˢ comptype0)
  compositionalityˢˢ u                          = refl
  compositionalityˢˢ (pair value0 value1)       = cong2 pair (compositionalityˢˢ value0) (compositionalityˢˢ value1)
  compositionalityˢˢ (inj bool0 value0)         = cong2 inj (compositionalityˢˢ bool0) (compositionalityˢˢ value0)
  compositionalityˢˢ (thunk comp0)              = cong1 thunk (compositionalityˢˢ comp0)
  compositionalityˢˢ cu                         = refl
  compositionalityˢˢ (force value0)             = cong1 force (compositionalityˢˢ value0)
  compositionalityˢˢ (lambda comp0)             = cong1 lambda (trans (compositionalityˢˢ comp0) (cong1 (comp0 ⋯ˢ_) (lift-dist-comp*ˢˢ (value ∷ []))))
  compositionalityˢˢ (app comp0 value0)         = cong2 app (compositionalityˢˢ comp0) (compositionalityˢˢ value0)
  compositionalityˢˢ (tuple comp0 comp1)        = cong2 tuple (compositionalityˢˢ comp0) (compositionalityˢˢ comp1)
  compositionalityˢˢ (ret value0)               = cong1 ret (compositionalityˢˢ value0)
  compositionalityˢˢ (letin comp0 comp1)        = cong2 letin (compositionalityˢˢ comp0) (trans (compositionalityˢˢ comp1) (cong1 (comp1 ⋯ˢ_) (lift-dist-comp*ˢˢ (value ∷ []))))
  compositionalityˢˢ (proj bool0 comp0)         = cong2 proj (compositionalityˢˢ bool0) (compositionalityˢˢ comp0)
  compositionalityˢˢ (caseZ value0)             = cong1 caseZ (compositionalityˢˢ value0)
  compositionalityˢˢ (caseS value0 comp0 comp1) = cong3 caseS (compositionalityˢˢ value0) (trans (compositionalityˢˢ comp0) (cong1 (comp0 ⋯ˢ_) (lift-dist-comp*ˢˢ (value ∷ [])))) (trans (compositionalityˢˢ comp1) (cong1 (comp1 ⋯ˢ_) (lift-dist-comp*ˢˢ (value ∷ []))))
  compositionalityˢˢ (caseP value0 comp0)       = cong2 caseP (compositionalityˢˢ value0) (trans (compositionalityˢˢ comp0) (cong1 (comp0 ⋯ˢ_) (lift-dist-comp*ˢˢ (value ∷ value ∷ []))))
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
  traversal-var traversal-zeroo traversal-one traversal-U traversal-Sigma traversal-cross traversal-cone traversal-F traversal-Pi traversal-arrow traversal-u traversal-pair traversal-inj traversal-thunk traversal-cu traversal-force traversal-lambda traversal-app traversal-tuple traversal-ret traversal-letin traversal-proj traversal-caseZ traversal-caseS traversal-caseP
  right-id
  compositionalityᴿˢ compositionalityᴿᴿ
  compositionalityˢᴿ compositionalityˢˢ
  coincidence coincidence-fold
#-}
