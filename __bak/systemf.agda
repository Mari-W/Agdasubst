{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module systemf where
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
  ty tm : Sort

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
  lam  : S ⊢ ty → (tm ∷ S) ⊢ tm → S ⊢ tm
  tapp : S ⊢ tm → S ⊢ ty → S ⊢ tm
  tlam : (ty ∷ S) ⊢ tm → S ⊢ tm
  lol  : (ty ∷ ty ∷ ty ∷ S) ⊢ ty → S ⊢ tm

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

(arr ty0 ty1)  ⋯ᴿ ρ = arr (ty0 ⋯ᴿ ρ) (ty1 ⋯ᴿ ρ)
(all ty0)      ⋯ᴿ ρ = all (ty0 ⋯ᴿ (ρ ↑ᴿ* _))
(app tm0 tm1)  ⋯ᴿ ρ = app (tm0 ⋯ᴿ ρ) (tm1 ⋯ᴿ ρ)
(lam ty0 tm0)  ⋯ᴿ ρ = lam (ty0 ⋯ᴿ ρ) (tm0 ⋯ᴿ (ρ ↑ᴿ* _))
(tapp tm0 ty0) ⋯ᴿ ρ = tapp (tm0 ⋯ᴿ ρ) (ty0 ⋯ᴿ ρ)
(tlam tm0)     ⋯ᴿ ρ = tlam (tm0 ⋯ᴿ (ρ ↑ᴿ* _))
(lol ty0)      ⋯ᴿ ρ = lol (ty0 ⋯ᴿ (ρ ↑ᴿ* _))

variable
  tm0 tm1 : S ⊢ tm
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

  (arr ty0 ty1)  ⋯ˢ σ = arr (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  (all ty0)      ⋯ˢ σ = all (ty0 ⋯ˢ (σ ↑ˢ* _))
  (app tm0 tm1)  ⋯ˢ σ = app (tm0 ⋯ˢ σ) (tm1 ⋯ˢ σ)
  (lam ty0 tm0)  ⋯ˢ σ = lam (ty0 ⋯ˢ σ) (tm0 ⋯ˢ (σ ↑ˢ* _))
  (tapp tm0 ty0) ⋯ˢ σ = tapp (tm0 ⋯ˢ σ) (ty0 ⋯ˢ σ)
  (tlam tm0)     ⋯ˢ σ = tlam (tm0 ⋯ˢ (σ ↑ˢ* _))
  (lol ty0)      ⋯ˢ σ = lol (ty0 ⋯ˢ (σ ↑ˢ* _))

  _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂

  beta-lift-id            : idᴿ {S = S} ↑ᴿ s ≡ idᴿ 

  beta-ext-zero           : zero ⋯ˢ (t ∙ σ)   ≡ t                             
  beta-ext-suc            : suc x ⋯ˢ (t ∙ σ)  ≡ x ⋯ˢ σ 
  beta-lift               : σ ↑ˢ s            ≡ (var zero) ∙ (σ ⨟ wkˢ _)

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
  compositionalityᴿˢ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ x/t ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                    
  compositionalityᴿᴿ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ x/t ⋯ᴿ (ρ₁ ∘ ρ₂)                     
  compositionalityˢᴿ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ x/t ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ x/t ⋯ˢ (σ₁ ⨟ σ₂)


  traversal-var           : (var x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  traversal-var = refl

  traversal-arr  : (arr ty0 ty1) ⋯ˢ σ  ≡ arr (ty0 ⋯ˢ σ) (ty1 ⋯ˢ σ)
  traversal-arr  = refl
  traversal-all  : (all ty0) ⋯ˢ σ      ≡ all (ty0 ⋯ˢ (σ ↑ˢ* (ty ∷ [])))
  traversal-all  = refl
  traversal-app  : (app tm0 tm1) ⋯ˢ σ  ≡ app (tm0 ⋯ˢ σ) (tm1 ⋯ˢ σ)
  traversal-app  = refl
  traversal-lam  : (lam ty0 tm0) ⋯ˢ σ  ≡ lam (ty0 ⋯ˢ σ) (tm0 ⋯ˢ (σ ↑ˢ* (tm ∷ [])))
  traversal-lam  = refl
  traversal-tapp : (tapp tm0 ty0) ⋯ˢ σ ≡ tapp (tm0 ⋯ˢ σ) (ty0 ⋯ˢ σ)
  traversal-tapp = refl
  traversal-tlam : (tlam tm0) ⋯ˢ σ     ≡ tlam (tm0 ⋯ˢ (σ ↑ˢ* (ty ∷ [])))
  traversal-tlam = refl
  traversal-lol  : (lol ty0) ⋯ˢ σ      ≡ lol (ty0 ⋯ˢ (σ ↑ˢ* (ty ∷ ty ∷ ty ∷ [])))
  traversal-lol  = refl

  coincidence              : x/t ⋯ˢ ⟨ ρ ⟩                                  ≡ x/t ⋯ᴿ ρ
  coincidence-fold         : x/t ⋯ˢ (⟨ ρ ↑ᴿ s ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))  ≡ x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩)


  beta-lift-id = ext λ { zero → refl; (suc x) → refl }

  beta-ext-zero = refl
  beta-ext-suc  = refl
  beta-lift     = cong1 ((var zero) ∙_) (sym (ext λ x → coincidence))

  beta-lift-idˢ* : ∀ S → (idˢ {S = S₁} ↑ˢ* S) ≡ idˢ 
  beta-lift-idˢ* []    = refl
  beta-lift-idˢ* {S₁} (_ ∷ S) rewrite beta-lift-idˢ* {S₁} S = η-lawᴿ

  right-idˢ               : ∀ (t : S ⊢ s) → t ⋯ˢ idˢ                   ≡ t 
  right-idˢ (var x)        = refl

  right-idˢ (arr ty0 ty1)  = cong2 arr (right-idˢ ty0) (right-idˢ ty1)
  right-idˢ (all ty0)      = cong1 all (trans (cong1 (ty0 ⋯ˢ_) (beta-lift-idˢ* (ty ∷ []))) (right-idˢ ty0))
  right-idˢ (app tm0 tm1)  = cong2 app (right-idˢ tm0) (right-idˢ tm1)
  right-idˢ (lam ty0 tm0)  = cong2 lam (right-idˢ ty0) (trans (cong1 (tm0 ⋯ˢ_) (beta-lift-idˢ* (tm ∷ []))) (right-idˢ tm0))
  right-idˢ (tapp tm0 ty0) = cong2 tapp (right-idˢ tm0) (right-idˢ ty0)
  right-idˢ (tlam tm0)     = cong1 tlam (trans (cong1 (tm0 ⋯ˢ_) (beta-lift-idˢ* (ty ∷ []))) (right-idˢ tm0))
  right-idˢ (lol ty0)      = cong1 lol (trans (cong1 (ty0 ⋯ˢ_) (beta-lift-idˢ* (ty ∷ ty ∷ ty ∷ []))) (right-idˢ ty0))

  associativity {σ₁ = σ₁} = ext λ x → compositionalityˢˢ (σ₁ _ x) 
  distributivityˢ = ext λ { zero → refl; (suc x) → refl }
  distributivityᴿ = ext λ { zero → coincidence; (suc x) → refl }
  interact        = refl
  comp-idᵣ        = ext λ x → (right-idˢ _)
  comp-idₗ        = refl
  η-id            = ext λ { zero → refl; (suc x) → refl }
  η-lawˢ          = ext λ { zero → refl; (suc x) → refl }
  η-lawᴿ          = ext λ { zero → refl; (suc x) → refl }

  beta-lift-id* : ∀ S → (idᴿ {S = S₁} ↑ᴿ* S) ≡ idᴿ
  beta-lift-id* []    = refl
  beta-lift-id* {S₁}  (_ ∷ S) rewrite beta-lift-id* {S₁} S = beta-lift-id

  right-id (var x)        = refl

  right-id (arr ty0 ty1)  = cong2 arr (right-id ty0) (right-id ty1)
  right-id (all ty0)      = cong1 all (trans (cong1 (ty0 ⋯ᴿ_) (beta-lift-id* (ty ∷ []))) (right-id ty0))
  right-id (app tm0 tm1)  = cong2 app (right-id tm0) (right-id tm1)
  right-id (lam ty0 tm0)  = cong2 lam (right-id ty0) (trans (cong1 (tm0 ⋯ᴿ_) (beta-lift-id* (tm ∷ []))) (right-id tm0))
  right-id (tapp tm0 ty0) = cong2 tapp (right-id tm0) (right-id ty0)
  right-id (tlam tm0)     = cong1 tlam (trans (cong1 (tm0 ⋯ᴿ_) (beta-lift-id* (ty ∷ []))) (right-id tm0))
  right-id (lol ty0)      = cong1 lol (trans (cong1 (ty0 ⋯ᴿ_) (beta-lift-id* (ty ∷ ty ∷ ty ∷ []))) (right-id ty0))
  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿᴿ : ∀ S → ((ρ₁ ↑ᴿ* S) ∘ (ρ₂ ↑ᴿ* S)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ* S)
  lift-dist-comp*ᴿᴿ []      = refl 
  lift-dist-comp*ᴿᴿ (_ ∷ S) = trans lift-dist-compᴿᴿ (cong1 (_↑ᴿ _) (lift-dist-comp*ᴿᴿ S))

  compositionalityᴿᴿ {m = V} x  = refl
  compositionalityᴿᴿ (var x)  = refl
  compositionalityᴿᴿ (arr ty0 ty1)  = cong2 arr (compositionalityᴿᴿ ty0) (compositionalityᴿᴿ ty1)
  compositionalityᴿᴿ (all ty0)      = cong1 all (trans (compositionalityᴿᴿ ty0) (cong1 (ty0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (ty ∷ []))))
  compositionalityᴿᴿ (app tm0 tm1)  = cong2 app (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ tm1)
  compositionalityᴿᴿ (lam ty0 tm0)  = cong2 lam (compositionalityᴿᴿ ty0) (trans (compositionalityᴿᴿ tm0) (cong1 (tm0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (tm ∷ []))))
  compositionalityᴿᴿ (tapp tm0 ty0) = cong2 tapp (compositionalityᴿᴿ tm0) (compositionalityᴿᴿ ty0)
  compositionalityᴿᴿ (tlam tm0)     = cong1 tlam (trans (compositionalityᴿᴿ tm0) (cong1 (tm0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (ty ∷ []))))
  compositionalityᴿᴿ (lol ty0)      = cong1 lol (trans (compositionalityᴿᴿ ty0) (cong1 (ty0 ⋯ᴿ_) (lift-dist-comp*ᴿᴿ (ty ∷ ty ∷ ty ∷ []))))
  lift-dist-compᴿˢ : (⟨ ρ₁ ↑ᴿ s ⟩ ⨟ (σ₂ ↑ˢ s)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }

  lift-dist-comp*ᴿˢ : ∀ S → (⟨ (ρ₁ ↑ᴿ* S) ⟩ ⨟ (σ₂ ↑ˢ* S)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ* S)
  lift-dist-comp*ᴿˢ []      = refl 
  lift-dist-comp*ᴿˢ (_ ∷ S) = trans lift-dist-compᴿˢ (cong1 (_↑ˢ _) (lift-dist-comp*ᴿˢ S))

  compositionalityᴿˢ {m = V} x  = refl
  compositionalityᴿˢ (var x)  = refl
  compositionalityᴿˢ (arr ty0 ty1)  = cong2 arr (compositionalityᴿˢ ty0) (compositionalityᴿˢ ty1)
  compositionalityᴿˢ (all ty0)      = cong1 all (trans (compositionalityᴿˢ ty0) (cong1 (ty0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (ty ∷ []))))
  compositionalityᴿˢ (app tm0 tm1)  = cong2 app (compositionalityᴿˢ tm0) (compositionalityᴿˢ tm1)
  compositionalityᴿˢ (lam ty0 tm0)  = cong2 lam (compositionalityᴿˢ ty0) (trans (compositionalityᴿˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (tm ∷ []))))
  compositionalityᴿˢ (tapp tm0 ty0) = cong2 tapp (compositionalityᴿˢ tm0) (compositionalityᴿˢ ty0)
  compositionalityᴿˢ (tlam tm0)     = cong1 tlam (trans (compositionalityᴿˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (ty ∷ []))))
  compositionalityᴿˢ (lol ty0)      = cong1 lol (trans (compositionalityᴿˢ ty0) (cong1 (ty0 ⋯ˢ_) (lift-dist-comp*ᴿˢ (ty ∷ ty ∷ ty ∷ []))))
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
 
  compositionalityˢᴿ {m = V} x  = sym coincidence
  compositionalityˢᴿ (var x)  = sym coincidence
  compositionalityˢᴿ (arr ty0 ty1)  = cong2 arr (compositionalityˢᴿ ty0) (compositionalityˢᴿ ty1)
  compositionalityˢᴿ (all ty0)      = cong1 all (trans (compositionalityˢᴿ ty0) (cong1 (ty0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (ty ∷ []))))
  compositionalityˢᴿ (app tm0 tm1)  = cong2 app (compositionalityˢᴿ tm0) (compositionalityˢᴿ tm1)
  compositionalityˢᴿ (lam ty0 tm0)  = cong2 lam (compositionalityˢᴿ ty0) (trans (compositionalityˢᴿ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (tm ∷ []))))
  compositionalityˢᴿ (tapp tm0 ty0) = cong2 tapp (compositionalityˢᴿ tm0) (compositionalityˢᴿ ty0)
  compositionalityˢᴿ (tlam tm0)     = cong1 tlam (trans (compositionalityˢᴿ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (ty ∷ []))))
  compositionalityˢᴿ (lol ty0)      = cong1 lol (trans (compositionalityˢᴿ ty0) (cong1 (ty0 ⋯ˢ_) (lift-dist-comp*ˢᴿ (ty ∷ ty ∷ ty ∷ []))))
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

  compositionalityˢˢ {m = V} x  = sym coincidence
  compositionalityˢˢ (var x)  = sym coincidence
  compositionalityˢˢ (arr ty0 ty1)  = cong2 arr (compositionalityˢˢ ty0) (compositionalityˢˢ ty1)
  compositionalityˢˢ (all ty0)      = cong1 all (trans (compositionalityˢˢ ty0) (cong1 (ty0 ⋯ˢ_) (lift-dist-comp*ˢˢ (ty ∷ []))))
  compositionalityˢˢ (app tm0 tm1)  = cong2 app (compositionalityˢˢ tm0) (compositionalityˢˢ tm1)
  compositionalityˢˢ (lam ty0 tm0)  = cong2 lam (compositionalityˢˢ ty0) (trans (compositionalityˢˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢˢ (tm ∷ []))))
  compositionalityˢˢ (tapp tm0 ty0) = cong2 tapp (compositionalityˢˢ tm0) (compositionalityˢˢ ty0)
  compositionalityˢˢ (tlam tm0)     = cong1 tlam (trans (compositionalityˢˢ tm0) (cong1 (tm0 ⋯ˢ_) (lift-dist-comp*ˢˢ (ty ∷ []))))
  compositionalityˢˢ (lol ty0)      = cong1 lol (trans (compositionalityˢˢ ty0) (cong1 (ty0 ⋯ˢ_) (lift-dist-comp*ˢˢ (ty ∷ ty ∷ ty ∷ []))))
  coincidence {x/t = x/t} {ρ = ρ} = 
    x/t ⋯ˢ (⟨ ρ ⟩ ⨟ idˢ) ≡⟨ sym (compositionalityᴿˢ x/t) ⟩ 
    (x/t ⋯ᴿ ρ) ⋯ˢ idˢ    ≡⟨ right-idˢ _ ⟩ 
    x/t ⋯ᴿ ρ             ∎

  coincidence-fold {x/t = x/t} {ρ = ρ} {x/t′ = x/t′} = 
    (x/t ⋯ˢ (⟨ ρ ↑ᴿ _ ⟩ ⨟ ((x/t′ ⋯ᴿ ρ) ∙ idˢ))) ≡⟨ cong1 (x/t ⋯ˢ_) (ext λ { zero → refl; (suc x) → refl }) ⟩ 
    (x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩))              ∎

{-# REWRITE
  beta-lift-id beta-ext-zero beta-ext-suc beta-lift
  associativity distributivityˢ distributivityᴿ interact
  comp-idᵣ comp-idₗ η-id η-lawˢ η-lawᴿ
  traversal-var traversal-arr traversal-all traversal-app traversal-lam traversal-tapp traversal-tlam traversal-lol
  right-id
  compositionalityᴿˢ compositionalityᴿᴿ
  compositionalityˢᴿ compositionalityˢˢ
  coincidence coincidence-fold
#-}