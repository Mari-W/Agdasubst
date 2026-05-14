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

  traversal-arr       : (arr ty0 ty1) ⋯ˢ σ            ≡ arr (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  traversal-arr       = refl
  traversal-ab        : (ab ty0 exp0) ⋯ˢ σ            ≡ ab (ty0 ⋯ˢ σ) (exp0 ⋯ˢ (σ ↑ˢ* (exp ∷ [])))
  traversal-ab        = refl
  traversal-app       : (app exp0 exp1) ⋯ˢ σ          ≡ app (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  traversal-app       = refl
  traversal-boolTy    : boolTy ⋯ˢ σ                   ≡ boolTy
  traversal-boolTy    = refl
  traversal-constBool : (constBool bool0) ⋯ˢ σ        ≡ constBool (bool0 ⋯ˢ σ)
  traversal-constBool = refl
  traversal-If        : (If exp0 exp1 exp2) ⋯ˢ σ      ≡ If (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ) (exp2 ⋯ˢ σ)
  traversal-If        = refl
  traversal-natTy     : natTy ⋯ˢ σ                    ≡ natTy
  traversal-natTy     = refl
  traversal-plus      : (plus exp0 exp1) ⋯ˢ σ         ≡ plus (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ)
  traversal-plus      = refl
  traversal-constNat  : (constNat nat0) ⋯ˢ σ          ≡ constNat (nat0 ⋯ˢ σ)
  traversal-constNat  = refl
  traversal-natCase   : (natCase exp0 exp1 exp2) ⋯ˢ σ ≡ natCase (exp0 ⋯ˢ σ) (exp1 ⋯ˢ σ) (exp2 ⋯ˢ (σ ↑ˢ* (exp ∷ [])))
  traversal-natCase   = refl
  traversal-sum       : (sum ty0 ty1) ⋯ˢ σ            ≡ sum (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  traversal-sum       = refl
  traversal-sumCase   : (sumCase exp0 exp1 exp2) ⋯ˢ σ ≡ sumCase (exp0 ⋯ˢ σ) (exp1 ⋯ˢ (σ ↑ˢ* (exp ∷ []))) (exp2 ⋯ˢ (σ ↑ˢ* (exp ∷ [])))
  traversal-sumCase   = refl
  traversal-inl       : (inl exp0) ⋯ˢ σ               ≡ inl (exp0 ⋯ˢ σ)
  traversal-inl       = refl
  traversal-inr       : (inr exp0) ⋯ˢ σ               ≡ inr (exp0 ⋯ˢ σ)
  traversal-inr       = refl

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
  compositionalityᴿᴿ (arr ty0 ty1)            = cong2 arr (compositionalityᴿᴿ ty0) (compositionalityᴿᴿ ty1)
  compositionalityᴿᴿ (ab ty0 exp0)            = cong2 ab (compositionalityᴿᴿ ty0) (trans (compositionalityᴿᴿ exp0) (cong1 (exp0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (exp ∷ []))))
  compositionalityᴿᴿ (app exp0 exp1)          = cong2 app (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1)
  compositionalityᴿᴿ boolTy                   = refl
  compositionalityᴿᴿ (constBool bool0)        = cong1 constBool (compositionalityᴿᴿ bool0)
  compositionalityᴿᴿ (If exp0 exp1 exp2)      = cong3 If (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1) (compositionalityᴿᴿ exp2)
  compositionalityᴿᴿ natTy                    = refl
  compositionalityᴿᴿ (plus exp0 exp1)         = cong2 plus (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1)
  compositionalityᴿᴿ (constNat nat0)          = cong1 constNat (compositionalityᴿᴿ nat0)
  compositionalityᴿᴿ (natCase exp0 exp1 exp2) = cong3 natCase (compositionalityᴿᴿ exp0) (compositionalityᴿᴿ exp1) (trans (compositionalityᴿᴿ exp2) (cong1 (exp2 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (exp ∷ []))))
  compositionalityᴿᴿ (sum ty0 ty1)            = cong2 sum (compositionalityᴿᴿ ty0) (compositionalityᴿᴿ ty1)
  compositionalityᴿᴿ (sumCase exp0 exp1 exp2) = cong3 sumCase (compositionalityᴿᴿ exp0) (trans (compositionalityᴿᴿ exp1) (cong1 (exp1 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (exp ∷ [])))) (trans (compositionalityᴿᴿ exp2) (cong1 (exp2 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (exp ∷ []))))
  compositionalityᴿᴿ (inl exp0)               = cong1 inl (compositionalityᴿᴿ exp0)
  compositionalityᴿᴿ (inr exp0)               = cong1 inr (compositionalityᴿᴿ exp0)
  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ (_ ∷ S) = trans lift-dist-compᴿˢ (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ S))

  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ (arr ty0 ty1)            = cong2 arr (compositionalityᴿˢ ty0) (compositionalityᴿˢ ty1)
  compositionalityᴿˢ (ab ty0 exp0)            = cong2 ab (compositionalityᴿˢ ty0) (trans (compositionalityᴿˢ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (exp ∷ []))))
  compositionalityᴿˢ (app exp0 exp1)          = cong2 app (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1)
  compositionalityᴿˢ boolTy                   = refl
  compositionalityᴿˢ (constBool bool0)        = cong1 constBool (compositionalityᴿˢ bool0)
  compositionalityᴿˢ (If exp0 exp1 exp2)      = cong3 If (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1) (compositionalityᴿˢ exp2)
  compositionalityᴿˢ natTy                    = refl
  compositionalityᴿˢ (plus exp0 exp1)         = cong2 plus (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1)
  compositionalityᴿˢ (constNat nat0)          = cong1 constNat (compositionalityᴿˢ nat0)
  compositionalityᴿˢ (natCase exp0 exp1 exp2) = cong3 natCase (compositionalityᴿˢ exp0) (compositionalityᴿˢ exp1) (trans (compositionalityᴿˢ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ᴿˢ (exp ∷ []))))
  compositionalityᴿˢ (sum ty0 ty1)            = cong2 sum (compositionalityᴿˢ ty0) (compositionalityᴿˢ ty1)
  compositionalityᴿˢ (sumCase exp0 exp1 exp2) = cong3 sumCase (compositionalityᴿˢ exp0) (trans (compositionalityᴿˢ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ᴿˢ (exp ∷ [])))) (trans (compositionalityᴿˢ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ᴿˢ (exp ∷ []))))
  compositionalityᴿˢ (inl exp0)               = cong1 inl (compositionalityᴿˢ exp0)
  compositionalityᴿˢ (inr exp0)               = cong1 inr (compositionalityᴿˢ exp0)
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
  compositionalityˢᴿ (arr ty0 ty1)            = cong2 arr (compositionalityˢᴿ ty0) (compositionalityˢᴿ ty1)
  compositionalityˢᴿ (ab ty0 exp0)            = cong2 ab (compositionalityˢᴿ ty0) (trans (compositionalityˢᴿ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (exp ∷ []))))
  compositionalityˢᴿ (app exp0 exp1)          = cong2 app (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1)
  compositionalityˢᴿ boolTy                   = refl
  compositionalityˢᴿ (constBool bool0)        = cong1 constBool (compositionalityˢᴿ bool0)
  compositionalityˢᴿ (If exp0 exp1 exp2)      = cong3 If (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1) (compositionalityˢᴿ exp2)
  compositionalityˢᴿ natTy                    = refl
  compositionalityˢᴿ (plus exp0 exp1)         = cong2 plus (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1)
  compositionalityˢᴿ (constNat nat0)          = cong1 constNat (compositionalityˢᴿ nat0)
  compositionalityˢᴿ (natCase exp0 exp1 exp2) = cong3 natCase (compositionalityˢᴿ exp0) (compositionalityˢᴿ exp1) (trans (compositionalityˢᴿ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ˢᴿ (exp ∷ []))))
  compositionalityˢᴿ (sum ty0 ty1)            = cong2 sum (compositionalityˢᴿ ty0) (compositionalityˢᴿ ty1)
  compositionalityˢᴿ (sumCase exp0 exp1 exp2) = cong3 sumCase (compositionalityˢᴿ exp0) (trans (compositionalityˢᴿ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ˢᴿ (exp ∷ [])))) (trans (compositionalityˢᴿ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ˢᴿ (exp ∷ []))))
  compositionalityˢᴿ (inl exp0)               = cong1 inl (compositionalityˢᴿ exp0)
  compositionalityˢᴿ (inr exp0)               = cong1 inr (compositionalityˢᴿ exp0)
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
  compositionalityˢˢ (arr ty0 ty1)            = cong2 arr (compositionalityˢˢ ty0) (compositionalityˢˢ ty1)
  compositionalityˢˢ (ab ty0 exp0)            = cong2 ab (compositionalityˢˢ ty0) (trans (compositionalityˢˢ exp0) (cong1 (exp0 ⋯ˢ_) (lift-dist-comp*ˢˢ (exp ∷ []))))
  compositionalityˢˢ (app exp0 exp1)          = cong2 app (compositionalityˢˢ exp0) (compositionalityˢˢ exp1)
  compositionalityˢˢ boolTy                   = refl
  compositionalityˢˢ (constBool bool0)        = cong1 constBool (compositionalityˢˢ bool0)
  compositionalityˢˢ (If exp0 exp1 exp2)      = cong3 If (compositionalityˢˢ exp0) (compositionalityˢˢ exp1) (compositionalityˢˢ exp2)
  compositionalityˢˢ natTy                    = refl
  compositionalityˢˢ (plus exp0 exp1)         = cong2 plus (compositionalityˢˢ exp0) (compositionalityˢˢ exp1)
  compositionalityˢˢ (constNat nat0)          = cong1 constNat (compositionalityˢˢ nat0)
  compositionalityˢˢ (natCase exp0 exp1 exp2) = cong3 natCase (compositionalityˢˢ exp0) (compositionalityˢˢ exp1) (trans (compositionalityˢˢ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ˢˢ (exp ∷ []))))
  compositionalityˢˢ (sum ty0 ty1)            = cong2 sum (compositionalityˢˢ ty0) (compositionalityˢˢ ty1)
  compositionalityˢˢ (sumCase exp0 exp1 exp2) = cong3 sumCase (compositionalityˢˢ exp0) (trans (compositionalityˢˢ exp1) (cong1 (exp1 ⋯ˢ_) (lift-dist-comp*ˢˢ (exp ∷ [])))) (trans (compositionalityˢˢ exp2) (cong1 (exp2 ⋯ˢ_) (lift-dist-comp*ˢˢ (exp ∷ []))))
  compositionalityˢˢ (inl exp0)               = cong1 inl (compositionalityˢˢ exp0)
  compositionalityˢˢ (inr exp0)               = cong1 inr (compositionalityˢˢ exp0)
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
  traversal-var traversal-arr traversal-ab traversal-app traversal-boolTy traversal-constBool traversal-If traversal-natTy traversal-plus traversal-constNat traversal-natCase traversal-sum traversal-sumCase traversal-inl traversal-inr
  right-id
  compositionalityᴿˢ compositionalityᴿᴿ
  compositionalityˢᴿ compositionalityˢˢ
  coincidence coincidence-fold
#-}
