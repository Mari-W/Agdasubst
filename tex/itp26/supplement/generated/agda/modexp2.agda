{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module modexp2 where
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
  ty exp bool nat : Sort

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

  arr       : S ⊢ ty → S ⊢ ty → S ⊢ ty
  ab        : S ⊢ ty → (exp ∷ S) ⊢ exp → S ⊢ exp
  app       : S ⊢ exp → S ⊢ exp → S ⊢ exp
  boolTy    : S ⊢ ty
  constBool : S ⊢ bool → S ⊢ exp
  If        : S ⊢ exp → S ⊢ exp → S ⊢ exp → S ⊢ exp
  natTy     : S ⊢ ty
  plus      : S ⊢ exp → S ⊢ exp → S ⊢ exp
  constNat  : S ⊢ nat → S ⊢ exp
  natCase   : S ⊢ exp → S ⊢ exp → (exp ∷ S) ⊢ exp → S ⊢ exp
  sum       : S ⊢ ty → S ⊢ ty → S ⊢ ty
  sumCase   : S ⊢ exp → (exp ∷ S) ⊢ exp → (exp ∷ S) ⊢ exp → S ⊢ exp
  inl       : S ⊢ exp → S ⊢ exp
  inr       : S ⊢ exp → S ⊢ exp

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

  (arr ty0 ty1)            ⋯ᴿ ρ = arr (ty0 ⋯ᴿ ρ) (ty1 ⋯ᴿ ρ)
  (ab ty0 exp0)            ⋯ᴿ ρ = ab (ty0 ⋯ᴿ ρ) (exp0 ⋯ᴿ (ρ ↑ᴿ* _))
  (app exp0 exp1)          ⋯ᴿ ρ = app (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ)
  boolTy                   ⋯ᴿ ρ = boolTy
  (constBool bool0)        ⋯ᴿ ρ = constBool (bool0 ⋯ᴿ ρ)
  (If exp0 exp1 exp2)      ⋯ᴿ ρ = If (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ) (exp2 ⋯ᴿ ρ)
  natTy                    ⋯ᴿ ρ = natTy
  (plus exp0 exp1)         ⋯ᴿ ρ = plus (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ)
  (constNat nat0)          ⋯ᴿ ρ = constNat (nat0 ⋯ᴿ ρ)
  (natCase exp0 exp1 exp2) ⋯ᴿ ρ = natCase (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ) (exp2 ⋯ᴿ (ρ ↑ᴿ* _))
  (sum ty0 ty1)            ⋯ᴿ ρ = sum (ty0 ⋯ᴿ ρ) (ty1 ⋯ᴿ ρ)
  (sumCase exp0 exp1 exp2) ⋯ᴿ ρ = sumCase (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ (ρ ↑ᴿ* _)) (exp2 ⋯ᴿ (ρ ↑ᴿ* _))
  (inl exp0)               ⋯ᴿ ρ = inl (exp0 ⋯ᴿ ρ)
  (inr exp0)               ⋯ᴿ ρ = inr (exp0 ⋯ᴿ ρ)

variable
  bool0 : S ⊢ bool
  exp0 exp1 exp2 : S ⊢ exp
  nat0 : S ⊢ nat
  ty0 ty1 : S ⊢ ty

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

  (arr ty0 ty1)            ⋯ˢ σ = arr (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  (ab ty0 exp0)            ⋯ˢ σ = ab (ty0 ⋯ˢ σ) (exp0 ⋯ˢ (σ ↑ˢ* _))
  (app exp0 exp1)          ⋯ˢ σ = app (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  boolTy                   ⋯ˢ σ = boolTy
  (constBool bool0)        ⋯ˢ σ = constBool (bool0 ⋯ˢ σ)
  (If exp0 exp1 exp2)      ⋯ˢ σ = If (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ) (exp2 ⋯ˢ σ)
  natTy                    ⋯ˢ σ = natTy
  (plus exp0 exp1)         ⋯ˢ σ = plus (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  (constNat nat0)          ⋯ˢ σ = constNat (nat0 ⋯ˢ σ)
  (natCase exp0 exp1 exp2) ⋯ˢ σ = natCase (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ) (exp2 ⋯ˢ (σ ↑ˢ* _))
  (sum ty0 ty1)            ⋯ˢ σ = sum (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  (sumCase exp0 exp1 exp2) ⋯ˢ σ = sumCase (exp0 ⋯ˢ σ) (exp1 ⋯ˢ (σ ↑ˢ* _)) (exp2 ⋯ˢ (σ ↑ˢ* _))
  (inl exp0)               ⋯ˢ σ = inl (exp0 ⋯ˢ σ)
  (inr exp0)               ⋯ˢ σ = inr (exp0 ⋯ˢ σ)

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

  instᴿ-arr       : (arr ty0 ty1) ⋯ᴿ ρ            ≡ arr (ty0 ⋯ᴿ ρ) (ty1 ⋯ᴿ ρ)
  instᴿ-arr       = refl
  instᴿ-ab        : (ab ty0 exp0) ⋯ᴿ ρ            ≡ ab (ty0 ⋯ᴿ ρ) (exp0 ⋯ᴿ (ρ ↑ᴿ* (exp ∷ [])))
  instᴿ-ab        = refl
  instᴿ-app       : (app exp0 exp1) ⋯ᴿ ρ          ≡ app (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ)
  instᴿ-app       = refl
  instᴿ-boolTy    : boolTy ⋯ᴿ ρ                   ≡ boolTy
  instᴿ-boolTy    = refl
  instᴿ-constBool : (constBool bool0) ⋯ᴿ ρ        ≡ constBool (bool0 ⋯ᴿ ρ)
  instᴿ-constBool = refl
  instᴿ-If        : (If exp0 exp1 exp2) ⋯ᴿ ρ      ≡ If (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ) (exp2 ⋯ᴿ ρ)
  instᴿ-If        = refl
  instᴿ-natTy     : natTy ⋯ᴿ ρ                    ≡ natTy
  instᴿ-natTy     = refl
  instᴿ-plus      : (plus exp0 exp1) ⋯ᴿ ρ         ≡ plus (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ)
  instᴿ-plus      = refl
  instᴿ-constNat  : (constNat nat0) ⋯ᴿ ρ          ≡ constNat (nat0 ⋯ᴿ ρ)
  instᴿ-constNat  = refl
  instᴿ-natCase   : (natCase exp0 exp1 exp2) ⋯ᴿ ρ ≡ natCase (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ ρ) (exp2 ⋯ᴿ (ρ ↑ᴿ* (exp ∷ [])))
  instᴿ-natCase   = refl
  instᴿ-sum       : (sum ty0 ty1) ⋯ᴿ ρ            ≡ sum (ty0 ⋯ᴿ ρ) (ty1 ⋯ᴿ ρ)
  instᴿ-sum       = refl
  instᴿ-sumCase   : (sumCase exp0 exp1 exp2) ⋯ᴿ ρ ≡ sumCase (exp0 ⋯ᴿ ρ) (exp1 ⋯ᴿ (ρ ↑ᴿ* (exp ∷ []))) (exp2 ⋯ᴿ (ρ ↑ᴿ* (exp ∷ [])))
  instᴿ-sumCase   = refl
  instᴿ-inl       : (inl exp0) ⋯ᴿ ρ               ≡ inl (exp0 ⋯ᴿ ρ)
  instᴿ-inl       = refl
  instᴿ-inr       : (inr exp0) ⋯ᴿ ρ               ≡ inr (exp0 ⋯ᴿ ρ)
  instᴿ-inr       = refl
  inst-arr       : (arr ty0 ty1) ⋯ˢ σ            ≡ arr (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  inst-arr       = refl
  inst-ab        : (ab ty0 exp0) ⋯ˢ σ            ≡ ab (ty0 ⋯ˢ σ) (exp0 ⋯ˢ (σ ↑ˢ* (exp ∷ [])))
  inst-ab        = refl
  inst-app       : (app exp0 exp1) ⋯ˢ σ          ≡ app (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  inst-app       = refl
  inst-boolTy    : boolTy ⋯ˢ σ                   ≡ boolTy
  inst-boolTy    = refl
  inst-constBool : (constBool bool0) ⋯ˢ σ        ≡ constBool (bool0 ⋯ˢ σ)
  inst-constBool = refl
  inst-If        : (If exp0 exp1 exp2) ⋯ˢ σ      ≡ If (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ) (exp2 ⋯ˢ σ)
  inst-If        = refl
  inst-natTy     : natTy ⋯ˢ σ                    ≡ natTy
  inst-natTy     = refl
  inst-plus      : (plus exp0 exp1) ⋯ˢ σ         ≡ plus (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  inst-plus      = refl
  inst-constNat  : (constNat nat0) ⋯ˢ σ          ≡ constNat (nat0 ⋯ˢ σ)
  inst-constNat  = refl
  inst-natCase   : (natCase exp0 exp1 exp2) ⋯ˢ σ ≡ natCase (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ) (exp2 ⋯ˢ (σ ↑ˢ* (exp ∷ [])))
  inst-natCase   = refl
  inst-sum       : (sum ty0 ty1) ⋯ˢ σ            ≡ sum (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  inst-sum       = refl
  inst-sumCase   : (sumCase exp0 exp1 exp2) ⋯ˢ σ ≡ sumCase (exp0 ⋯ˢ σ) (exp1 ⋯ˢ (σ ↑ˢ* (exp ∷ []))) (exp2 ⋯ˢ (σ ↑ˢ* (exp ∷ [])))
  inst-sumCase   = refl
  inst-inl       : (inl exp0) ⋯ˢ σ               ≡ inl (exp0 ⋯ˢ σ)
  inst-inl       = refl
  inst-inr       : (inr exp0) ⋯ˢ σ               ≡ inr (exp0 ⋯ˢ σ)
  inst-inr       = refl

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
  right-idˢ (arr ty0 ty1)            = cong2 arr (right-idˢ ty0) (right-idˢ ty1)
  right-idˢ (ab ty0 exp0)            = cong2 ab (right-idˢ ty0) (trans (cong1 (exp0 ⋯ˢ_) (lift-idˢ* (exp ∷ []))) (right-idˢ exp0))
  right-idˢ (app exp0 exp1)          = cong2 app (right-idˢ exp0) (right-idˢ exp1)
  right-idˢ boolTy                   = refl
  right-idˢ (constBool bool0)        = cong1 constBool (right-idˢ bool0)
  right-idˢ (If exp0 exp1 exp2)      = cong3 If (right-idˢ exp0) (right-idˢ exp1) (right-idˢ exp2)
  right-idˢ natTy                    = refl
  right-idˢ (plus exp0 exp1)         = cong2 plus (right-idˢ exp0) (right-idˢ exp1)
  right-idˢ (constNat nat0)          = cong1 constNat (right-idˢ nat0)
  right-idˢ (natCase exp0 exp1 exp2) = cong3 natCase (right-idˢ exp0) (right-idˢ exp1) (trans (cong1 (exp2 ⋯ˢ_) (lift-idˢ* (exp ∷ []))) (right-idˢ exp2))
  right-idˢ (sum ty0 ty1)            = cong2 sum (right-idˢ ty0) (right-idˢ ty1)
  right-idˢ (sumCase exp0 exp1 exp2) = cong3 sumCase (right-idˢ exp0) (trans (cong1 (exp1 ⋯ˢ_) (lift-idˢ* (exp ∷ []))) (right-idˢ exp1)) (trans (cong1 (exp2 ⋯ˢ_) (lift-idˢ* (exp ∷ []))) (right-idˢ exp2))
  right-idˢ (inl exp0)               = cong1 inl (right-idˢ exp0)
  right-idˢ (inr exp0)               = cong1 inr (right-idˢ exp0)

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
  right-id (arr ty0 ty1)            = cong2 arr (right-id ty0) (right-id ty1)
  right-id (ab ty0 exp0)            = cong2 ab (right-id ty0) (trans (cong1 (exp0 ⋯ᴿ_) (lift-id* (exp ∷ []))) (right-id exp0))
  right-id (app exp0 exp1)          = cong2 app (right-id exp0) (right-id exp1)
  right-id boolTy                   = refl
  right-id (constBool bool0)        = cong1 constBool (right-id bool0)
  right-id (If exp0 exp1 exp2)      = cong3 If (right-id exp0) (right-id exp1) (right-id exp2)
  right-id natTy                    = refl
  right-id (plus exp0 exp1)         = cong2 plus (right-id exp0) (right-id exp1)
  right-id (constNat nat0)          = cong1 constNat (right-id nat0)
  right-id (natCase exp0 exp1 exp2) = cong3 natCase (right-id exp0) (right-id exp1) (trans (cong1 (exp2 ⋯ᴿ_) (lift-id* (exp ∷ []))) (right-id exp2))
  right-id (sum ty0 ty1)            = cong2 sum (right-id ty0) (right-id ty1)
  right-id (sumCase exp0 exp1 exp2) = cong3 sumCase (right-id exp0) (trans (cong1 (exp1 ⋯ᴿ_) (lift-id* (exp ∷ []))) (right-id exp1)) (trans (cong1 (exp2 ⋯ᴿ_) (lift-id* (exp ∷ []))) (right-id exp2))
  right-id (inl exp0)               = cong1 inl (right-id exp0)
  right-id (inr exp0)               = cong1 inr (right-id exp0)

  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ  (arr ty0 ty1)            = cong2 arr (compositionalityᴿᴿ ty0) (compositionalityᴿᴿ ty1)
  compositionalityᴿᴿ  (ab ty0 exp0)            = cong2 ab (compositionalityᴿᴿ ty0) (trans (compositionalityᴿᴿ exp0) (cong1 (exp0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (exp ∷ []))))
  compositionalityᴿᴿ  (app exp0 exp1)          = cong2 app (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1)
  compositionalityᴿᴿ boolTy                    = refl
  compositionalityᴿᴿ  (constBool bool0)        = cong1 constBool (compositionalityᴿᴿ bool0)
  compositionalityᴿᴿ  (If exp0 exp1 exp2)      = cong3 If (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1) (compositionalityᴿᴿ exp2)
  compositionalityᴿᴿ natTy                     = refl
  compositionalityᴿᴿ  (plus exp0 exp1)         = cong2 plus (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1)
  compositionalityᴿᴿ  (constNat nat0)          = cong1 constNat (compositionalityᴿᴿ nat0)
  compositionalityᴿᴿ  (natCase exp0 exp1 exp2) = cong3 natCase (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1) (trans (compositionalityᴿᴿ exp2) (cong1 (exp2 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (exp ∷ []))))
  compositionalityᴿᴿ  (sum ty0 ty1)            = cong2 sum (compositionalityᴿᴿ ty0) (compositionalityᴿᴿ ty1)
  compositionalityᴿᴿ  (sumCase exp0 exp1 exp2) = cong3 sumCase (compositionalityᴿᴿ exp0) (trans (compositionalityᴿᴿ exp1) (cong1 (exp1 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (exp ∷ [])))) (trans (compositionalityᴿᴿ exp2) (cong1 (exp2 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (exp ∷ []))))
  compositionalityᴿᴿ  (inl exp0)               = cong1 inl (compositionalityᴿᴿ exp0)
  compositionalityᴿᴿ  (inr exp0)               = cong1 inr (compositionalityᴿᴿ exp0)

  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ {σ₂ = σ₂} (_ ∷ S) = trans (lift-dist-compᴿˢ {σ₂ = σ₂ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} S))

  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ {σ₂ = σ₂} (arr ty0 ty1)            = cong2 arr (compositionalityᴿˢ ty0) (compositionalityᴿˢ ty1)
  compositionalityᴿˢ {σ₂ = σ₂} (ab ty0 exp0)            = cong2 ab (compositionalityᴿˢ ty0) (trans (compositionalityᴿˢ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (exp ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (app exp0 exp1)          = cong2 app (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1)
  compositionalityᴿˢ boolTy                             = refl
  compositionalityᴿˢ {σ₂ = σ₂} (constBool bool0)        = cong1 constBool (compositionalityᴿˢ bool0)
  compositionalityᴿˢ {σ₂ = σ₂} (If exp0 exp1 exp2)      = cong3 If (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1) (compositionalityᴿˢ exp2)
  compositionalityᴿˢ natTy                              = refl
  compositionalityᴿˢ {σ₂ = σ₂} (plus exp0 exp1)         = cong2 plus (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1)
  compositionalityᴿˢ {σ₂ = σ₂} (constNat nat0)          = cong1 constNat (compositionalityᴿˢ nat0)
  compositionalityᴿˢ {σ₂ = σ₂} (natCase exp0 exp1 exp2) = cong3 natCase (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1) (trans (compositionalityᴿˢ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (exp ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (sum ty0 ty1)            = cong2 sum (compositionalityᴿˢ ty0) (compositionalityᴿˢ ty1)
  compositionalityᴿˢ {σ₂ = σ₂} (sumCase exp0 exp1 exp2) = cong3 sumCase (compositionalityᴿˢ exp0) (trans (compositionalityᴿˢ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (exp ∷ [])))) (trans (compositionalityᴿˢ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (exp ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (inl exp0)               = cong1 inl (compositionalityᴿˢ exp0)
  compositionalityᴿˢ {σ₂ = σ₂} (inr exp0)               = cong1 inr (compositionalityᴿˢ exp0)

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
  compositionalityˢᴿ {σ₁ = σ₁} (arr ty0 ty1)            = cong2 arr (compositionalityˢᴿ ty0) (compositionalityˢᴿ ty1)
  compositionalityˢᴿ {σ₁ = σ₁} (ab ty0 exp0)            = cong2 ab (compositionalityˢᴿ ty0) (trans (compositionalityˢᴿ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (exp ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (app exp0 exp1)          = cong2 app (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1)
  compositionalityˢᴿ boolTy                             = refl
  compositionalityˢᴿ {σ₁ = σ₁} (constBool bool0)        = cong1 constBool (compositionalityˢᴿ bool0)
  compositionalityˢᴿ {σ₁ = σ₁} (If exp0 exp1 exp2)      = cong3 If (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1) (compositionalityˢᴿ exp2)
  compositionalityˢᴿ natTy                              = refl
  compositionalityˢᴿ {σ₁ = σ₁} (plus exp0 exp1)         = cong2 plus (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1)
  compositionalityˢᴿ {σ₁ = σ₁} (constNat nat0)          = cong1 constNat (compositionalityˢᴿ nat0)
  compositionalityˢᴿ {σ₁ = σ₁} (natCase exp0 exp1 exp2) = cong3 natCase (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1) (trans (compositionalityˢᴿ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (exp ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (sum ty0 ty1)            = cong2 sum (compositionalityˢᴿ ty0) (compositionalityˢᴿ ty1)
  compositionalityˢᴿ {σ₁ = σ₁} (sumCase exp0 exp1 exp2) = cong3 sumCase (compositionalityˢᴿ exp0) (trans (compositionalityˢᴿ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (exp ∷ [])))) (trans (compositionalityˢᴿ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (exp ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (inl exp0)               = cong1 inl (compositionalityˢᴿ exp0)
  compositionalityˢᴿ {σ₁ = σ₁} (inr exp0)               = cong1 inr (compositionalityˢᴿ exp0)
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
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (arr ty0 ty1)            = cong2 arr (compositionalityˢˢ ty0) (compositionalityˢˢ ty1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (ab ty0 exp0)            = cong2 ab (compositionalityˢˢ ty0) (trans (compositionalityˢˢ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (exp ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (app exp0 exp1)          = cong2 app (compositionalityˢˢ exp0) (compositionalityˢˢ exp1)
  compositionalityˢˢ boolTy                                       = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (constBool bool0)        = cong1 constBool (compositionalityˢˢ bool0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (If exp0 exp1 exp2)      = cong3 If (compositionalityˢˢ exp0) (compositionalityˢˢ exp1) (compositionalityˢˢ exp2)
  compositionalityˢˢ natTy                                        = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (plus exp0 exp1)         = cong2 plus (compositionalityˢˢ exp0) (compositionalityˢˢ exp1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (constNat nat0)          = cong1 constNat (compositionalityˢˢ nat0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (natCase exp0 exp1 exp2) = cong3 natCase (compositionalityˢˢ exp0) (compositionalityˢˢ exp1) (trans (compositionalityˢˢ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (exp ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (sum ty0 ty1)            = cong2 sum (compositionalityˢˢ ty0) (compositionalityˢˢ ty1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (sumCase exp0 exp1 exp2) = cong3 sumCase (compositionalityˢˢ exp0) (trans (compositionalityˢˢ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (exp ∷ [])))) (trans (compositionalityˢˢ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (exp ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (inl exp0)               = cong1 inl (compositionalityˢˢ exp0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (inr exp0)               = cong1 inr (compositionalityˢˢ exp0)

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
  inst-arr instᴿ-arr
  inst-ab instᴿ-ab
  inst-app instᴿ-app
  inst-boolTy instᴿ-boolTy
  inst-constBool instᴿ-constBool
  inst-If instᴿ-If
  inst-natTy instᴿ-natTy
  inst-plus instᴿ-plus
  inst-constNat instᴿ-constNat
  inst-natCase instᴿ-natCase
  inst-sum instᴿ-sum
  inst-sumCase instᴿ-sumCase
  inst-inl instᴿ-inl
  inst-inr instᴿ-inr
  def-id def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-∘      
  assocᴿ distᴿ interactᴿ       
  comp-idᵣᴿ comp-idₗᴿ η-idᴿ η-lawᴿ
  coincidence-var
#-}
