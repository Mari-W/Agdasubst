{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module sysf_cbv where
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

open import Data.List using (List; []; _∷_; _++_)

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

data Mode : Set where 
  V T : Mode

private variable
  m  : Mode

data Sort : Set where 
  ty tm vl : Sort

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

  arr  : S ⊢ ty → S ⊢ ty → S ⊢ ty
  all  : (ty ∷ S) ⊢ ty → S ⊢ ty
  app  : S ⊢ tm → S ⊢ tm → S ⊢ tm
  tapp : S ⊢ tm → S ⊢ ty → S ⊢ tm
  vt   : S ⊢ vl → S ⊢ tm
  lam  : S ⊢ ty → (vl ∷ S) ⊢ tm → S ⊢ vl
  tlam : (ty ∷ S) ⊢ tm → S ⊢ vl

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

  (arr ty0 ty1)  ⋯ᴿ ρ = arr (ty0 ⋯ᴿ ρ) (ty1 ⋯ᴿ ρ)
  (all ty0)      ⋯ᴿ ρ = all (ty0 ⋯ᴿ (ρ ↑ᴿ* _))
  (app tm0 tm1)  ⋯ᴿ ρ = app (tm0 ⋯ᴿ ρ) (tm1 ⋯ᴿ ρ)
  (tapp tm0 ty0) ⋯ᴿ ρ = tapp (tm0 ⋯ᴿ ρ) (ty0 ⋯ᴿ ρ)
  (vt vl0)       ⋯ᴿ ρ = vt (vl0 ⋯ᴿ ρ)
  (lam ty0 tm0)  ⋯ᴿ ρ = lam (ty0 ⋯ᴿ ρ) (tm0 ⋯ᴿ (ρ ↑ᴿ* _))
  (tlam tm0)     ⋯ᴿ ρ = tlam (tm0 ⋯ᴿ (ρ ↑ᴿ* _))

variable
  tm0 tm1 : S ⊢ tm
  ty0 ty1 : S ⊢ ty
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

  (arr ty0 ty1)  ⋯ˢ σ = arr (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  (all ty0)      ⋯ˢ σ = all (ty0 ⋯ˢ (σ ↑ˢ* _))
  (app tm0 tm1)  ⋯ˢ σ = app (tm0 ⋯ˢ σ) (tm1 ⋯ˢ σ)
  (tapp tm0 ty0) ⋯ˢ σ = tapp (tm0 ⋯ˢ σ) (ty0 ⋯ˢ σ)
  (vt vl0)       ⋯ˢ σ = vt (vl0 ⋯ˢ σ)
  (lam ty0 tm0)  ⋯ˢ σ = lam (ty0 ⋯ˢ σ) (tm0 ⋯ˢ (σ ↑ˢ* _))
  (tlam tm0)     ⋯ˢ σ = tlam (tm0 ⋯ˢ (σ ↑ˢ* _))

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

  instᴿ-arr  : (arr ty0 ty1) ⋯ᴿ ρ  ≡ arr (ty0 ⋯ᴿ ρ) (ty1 ⋯ᴿ ρ)
  instᴿ-arr  = refl
  instᴿ-all  : (all ty0) ⋯ᴿ ρ      ≡ all (ty0 ⋯ᴿ (ρ ↑ᴿ* (ty ∷ [])))
  instᴿ-all  = refl
  instᴿ-app  : (app tm0 tm1) ⋯ᴿ ρ  ≡ app (tm0 ⋯ᴿ ρ) (tm1 ⋯ᴿ ρ)
  instᴿ-app  = refl
  instᴿ-tapp : (tapp tm0 ty0) ⋯ᴿ ρ ≡ tapp (tm0 ⋯ᴿ ρ) (ty0 ⋯ᴿ ρ)
  instᴿ-tapp = refl
  instᴿ-vt   : (vt vl0) ⋯ᴿ ρ       ≡ vt (vl0 ⋯ᴿ ρ)
  instᴿ-vt   = refl
  instᴿ-lam  : (lam ty0 tm0) ⋯ᴿ ρ  ≡ lam (ty0 ⋯ᴿ ρ) (tm0 ⋯ᴿ (ρ ↑ᴿ* (vl ∷ [])))
  instᴿ-lam  = refl
  instᴿ-tlam : (tlam tm0) ⋯ᴿ ρ     ≡ tlam (tm0 ⋯ᴿ (ρ ↑ᴿ* (ty ∷ [])))
  instᴿ-tlam = refl
  inst-arr  : (arr ty0 ty1) ⋯ˢ σ  ≡ arr (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  inst-arr  = refl
  inst-all  : (all ty0) ⋯ˢ σ      ≡ all (ty0 ⋯ˢ (σ ↑ˢ* (ty ∷ [])))
  inst-all  = refl
  inst-app  : (app tm0 tm1) ⋯ˢ σ  ≡ app (tm0 ⋯ˢ σ) (tm1 ⋯ˢ σ)
  inst-app  = refl
  inst-tapp : (tapp tm0 ty0) ⋯ˢ σ ≡ tapp (tm0 ⋯ˢ σ) (ty0 ⋯ˢ σ)
  inst-tapp = refl
  inst-vt   : (vt vl0) ⋯ˢ σ       ≡ vt (vl0 ⋯ˢ σ)
  inst-vt   = refl
  inst-lam  : (lam ty0 tm0) ⋯ˢ σ  ≡ lam (ty0 ⋯ˢ σ) (tm0 ⋯ˢ (σ ↑ˢ* (vl ∷ [])))
  inst-lam  = refl
  inst-tlam : (tlam tm0) ⋯ˢ σ     ≡ tlam (tm0 ⋯ˢ (σ ↑ˢ* (ty ∷ [])))
  inst-tlam = refl

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
  right-idˢ (arr ty0 ty1)  = cong2 arr (right-idˢ ty0) (right-idˢ ty1)
  right-idˢ (all ty0)      = cong1 all (trans (cong1 (ty0 ⋯ˢ_) (lift-idˢ* (ty ∷ []))) (right-idˢ ty0))
  right-idˢ (app tm0 tm1)  = cong2 app (right-idˢ tm0) (right-idˢ tm1)
  right-idˢ (tapp tm0 ty0) = cong2 tapp (right-idˢ tm0) (right-idˢ ty0)
  right-idˢ (vt vl0)       = cong1 vt (right-idˢ vl0)
  right-idˢ (lam ty0 tm0)  = cong2 lam (right-idˢ ty0) (trans (cong1 (tm0 ⋯ˢ_) (lift-idˢ* (vl ∷ []))) (right-idˢ tm0))
  right-idˢ (tlam tm0)     = cong1 tlam (trans (cong1 (tm0 ⋯ˢ_) (lift-idˢ* (ty ∷ []))) (right-idˢ tm0))

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
  right-id (arr ty0 ty1)  = cong2 arr (right-id ty0) (right-id ty1)
  right-id (all ty0)      = cong1 all (trans (cong1 (ty0 ⋯ᴿ_) (lift-id* (ty ∷ []))) (right-id ty0))
  right-id (app tm0 tm1)  = cong2 app (right-id tm0) (right-id tm1)
  right-id (tapp tm0 ty0) = cong2 tapp (right-id tm0) (right-id ty0)
  right-id (vt vl0)       = cong1 vt (right-id vl0)
  right-id (lam ty0 tm0)  = cong2 lam (right-id ty0) (trans (cong1 (tm0 ⋯ᴿ_) (lift-id* (vl ∷ []))) (right-id tm0))
  right-id (tlam tm0)     = cong1 tlam (trans (cong1 (tm0 ⋯ᴿ_) (lift-id* (ty ∷ []))) (right-id tm0))

  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ  (arr ty0 ty1)  = cong2 arr (compositionalityᴿᴿ ty0) (compositionalityᴿᴿ ty1)
  compositionalityᴿᴿ  (all ty0)      = cong1 all (trans (compositionalityᴿᴿ ty0) (cong1 (ty0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (ty ∷ []))))
  compositionalityᴿᴿ  (app tm0 tm1)  = cong2 app (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ tm1)
  compositionalityᴿᴿ  (tapp tm0 ty0) = cong2 tapp (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ ty0)
  compositionalityᴿᴿ  (vt vl0)       = cong1 vt (compositionalityᴿᴿ vl0)
  compositionalityᴿᴿ  (lam ty0 tm0)  = cong2 lam (compositionalityᴿᴿ ty0) (trans (compositionalityᴿᴿ tm0) (cong1 (tm0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (vl ∷ []))))
  compositionalityᴿᴿ  (tlam tm0)     = cong1 tlam (trans (compositionalityᴿᴿ tm0) (cong1 (tm0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ  (ty ∷ []))))

  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ {σ₂ = σ₂} (_ ∷ S) = trans (lift-dist-compᴿˢ {σ₂ = σ₂ ↑ˢ* S}) (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} S))

  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ {σ₂ = σ₂} (arr ty0 ty1)  = cong2 arr (compositionalityᴿˢ ty0) (compositionalityᴿˢ ty1)
  compositionalityᴿˢ {σ₂ = σ₂} (all ty0)      = cong1 all (trans (compositionalityᴿˢ ty0) (cong1 (ty0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (ty ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (app tm0 tm1)  = cong2 app (compositionalityᴿˢ tm0) (compositionalityᴿˢ tm1)
  compositionalityᴿˢ {σ₂ = σ₂} (tapp tm0 ty0) = cong2 tapp (compositionalityᴿˢ tm0) (compositionalityᴿˢ ty0)
  compositionalityᴿˢ {σ₂ = σ₂} (vt vl0)       = cong1 vt (compositionalityᴿˢ vl0)
  compositionalityᴿˢ {σ₂ = σ₂} (lam ty0 tm0)  = cong2 lam (compositionalityᴿˢ ty0) (trans (compositionalityᴿˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (vl ∷ []))))
  compositionalityᴿˢ {σ₂ = σ₂} (tlam tm0)     = cong1 tlam (trans (compositionalityᴿˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ᴿˢ {σ₂ = σ₂} (ty ∷ []))))

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
  compositionalityˢᴿ {σ₁ = σ₁} (arr ty0 ty1)  = cong2 arr (compositionalityˢᴿ ty0) (compositionalityˢᴿ ty1)
  compositionalityˢᴿ {σ₁ = σ₁} (all ty0)      = cong1 all (trans (compositionalityˢᴿ ty0) (cong1 (ty0 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (ty ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (app tm0 tm1)  = cong2 app (compositionalityˢᴿ tm0) (compositionalityˢᴿ tm1)
  compositionalityˢᴿ {σ₁ = σ₁} (tapp tm0 ty0) = cong2 tapp (compositionalityˢᴿ tm0) (compositionalityˢᴿ ty0)
  compositionalityˢᴿ {σ₁ = σ₁} (vt vl0)       = cong1 vt (compositionalityˢᴿ vl0)
  compositionalityˢᴿ {σ₁ = σ₁} (lam ty0 tm0)  = cong2 lam (compositionalityˢᴿ ty0) (trans (compositionalityˢᴿ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (vl ∷ []))))
  compositionalityˢᴿ {σ₁ = σ₁} (tlam tm0)     = cong1 tlam (trans (compositionalityˢᴿ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢᴿ {σ₁ = σ₁} (ty ∷ []))))
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
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (arr ty0 ty1)  = cong2 arr (compositionalityˢˢ ty0) (compositionalityˢˢ ty1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (all ty0)      = cong1 all (trans (compositionalityˢˢ ty0) (cong1 (ty0 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (ty ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (app tm0 tm1)  = cong2 app (compositionalityˢˢ tm0) (compositionalityˢˢ tm1)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (tapp tm0 ty0) = cong2 tapp (compositionalityˢˢ tm0) (compositionalityˢˢ ty0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (vt vl0)       = cong1 vt (compositionalityˢˢ vl0)
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (lam ty0 tm0)  = cong2 lam (compositionalityˢˢ ty0) (trans (compositionalityˢˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (vl ∷ []))))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (tlam tm0)     = cong1 tlam (trans (compositionalityˢˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (ty ∷ []))))

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
  inst-all instᴿ-all
  inst-app instᴿ-app
  inst-tapp instᴿ-tapp
  inst-vt instᴿ-vt
  inst-lam instᴿ-lam
  inst-tlam instᴿ-tlam
  def-id def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-∘      
  assocᴿ distᴿ interactᴿ       
  comp-idᵣᴿ comp-idₗᴿ η-idᴿ η-lawᴿ
  coincidence-var
#-}
