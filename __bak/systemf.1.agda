{-# OPTIONS --rewriting --double-check --local-confluence-check #-}
module systemf where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Data.List using (List; []; _∷_; drop)

-- we rely on fun-ext.. 
-- with a little more effort this is not neccessary
-- <insert reference>
ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

-- replace this with numbers
data Sort : Set where 
  type : Sort 

variable 
  s s₁ s₂ s′ : Sort 
  S S₁ S₂ S₃ S₄ : List Sort

Scope = List Sort

-- 
data Mode : Set where
  V T : Mode

variable
  m  : Mode

-- syntax is uniform for variables and term 
-- we can separate these definitions if neccessary
data _⊢[_]_ : Scope → Mode → Sort → Set 

_⊢_ = _⊢[ T ]_
_∋_ = _⊢[ V ]_

data _⊢[_]_ where 
  zero : (s ∷ S) ∋ s
  suc  : S ∋ s → (s′ ∷ S) ∋ s
  `_   : S ∋ s → S ⊢ s 
  ∀α_  : (type ∷ S) ⊢ type → S ⊢ type
  _⇒_  : S ⊢ type → S ⊢ type → S ⊢ type

variable
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s
  x/t x/t′ : S ⊢[ m ] s

-- substitution are functions that with 
-- primitive operations that reduce
_→ᴿ_ : Scope → Scope → Set
S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s 

variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂

idᴿ : S →ᴿ S
idᴿ _ x = x

_↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → ((s ∷ S₁) →ᴿ (s ∷ S₂))
(ρ ↑ᴿ _) _ zero    = zero
(ρ ↑ᴿ _) _ (suc x) = suc (ρ _ x) 

_∘_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
(ρ₁ ∘ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

wk : ∀ s → S →ᴿ (s ∷ S)
wk _ _ = suc

_⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → S₂ ⊢[ T ] s 
_⋯ᴿ_ {m = V} x   ρ = ` ρ _ x
(` x)         ⋯ᴿ ρ = ` ρ _ x
(∀α t)        ⋯ᴿ ρ = ∀α (t ⋯ᴿ (ρ ↑ᴿ _))
(t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)

_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s 

variable
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂  

-- just helpers! 
-- {-# inline -#} so that agda does not say we rewrite 
-- on reducing symbols..
⟪_⟫ : S₁ →ᴿ S₂ → S₁ →ˢ S₂ 
⟪ ρ ⟫ _ x = ` ρ _ x
{-# INLINE ⟪_⟫ #-}

wkˢ : ∀ s → S →ˢ (s ∷ S)
wkˢ _ _ x = ` suc x
{-# INLINE wkˢ #-}

idˢ : S →ˢ S
idˢ _ = `_
{-# INLINE idˢ #-}

-- the primitives for substitution must be opaque!
-- otherwise we cannot rewrite on them (even if inlined..)
-- since the violate the rewrite rule rules 
-- ask me for an example for where it breaks if neccessary!
opaque
  -- σₛ­ₚ calculus with first class renamings
  
  -- syntax
  _∙_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂    
  _∙_  t σ _ zero = t
  (t ∙ σ) _ (suc x) = σ _ x 

  -- instantiation is defined on both terms and 
  -- variables at the same time, this is important 
  -- so we can rewrite on variable lookup
  -- (introducing an extra lookup operator would 
  -- i guess be possible, but also introduces noise 
  -- in the laws)

  _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s =  (` zero) ∙ λ s₁ x → (σ _ x) ⋯ᴿ (wk _)

  _⋯ˢ_ {m = V} x σ = σ _ x
  (` x) ⋯ˢ σ = σ _ x
  (∀α t)        ⋯ˢ σ = ∀α (t ⋯ˢ (σ ↑ˢ _))
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)

  _;_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ; σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂

  -- rewrite system
  -- you probably shouldnt care too much about 
  -- the spcific system here, it just "the same as in autosubst" 
  -- namely the σₛₚ calculus
  
  -- importantly: it is locally confluent and terminating
  -- (not complete in presence of first class renamings)
  -- <insert reference>
  -- thus valid rewrite rules 

  -- more importantly, we do not 
  -- (by convention, currently not enforced) use (σ _ x) 
  -- to lookup a variable in a substittution, 
  -- but rather use the blocking symbol x ⋯ˢ σ
  -- on which we can rewrite the sigma laws!

  -- first-class renamings 
  beta-lift-id            : idᴿ {S = S} ↑ᴿ s ≡ idᴿ 

  -- beta laws
  beta-ext-zero           : zero ⋯ˢ (t ∙ σ)   ≡ t                             
  beta-ext-suc            : suc x ⋯ˢ (t ∙ σ)  ≡ x ⋯ˢ σ 
  beta-lift               : σ ↑ˢ s            ≡ (` zero) ∙ (σ ; wkˢ _)

  -- interaction laws
  associativity           : (σ₁ ; σ₂) ; σ₃                      ≡ σ₁ ; (σ₂ ; σ₃)                     
  distributivity         : (t ∙ σ₁) ; σ₂                       ≡ ((t ⋯ˢ σ₂) ∙ (σ₁ ; σ₂)) 
  distributivityᴿ         : (t ∙ σ₁) ; ⟪ ρ₂ ⟫                   ≡ ((t ⋯ᴿ ρ₂) ∙ (σ₁ ; ⟪ ρ₂ ⟫)) 
  interact                : wkˢ s ; (t ∙ σ)                     ≡ σ                                        
  comp-idᵣ                : σ ; idˢ                             ≡ σ                                               
  comp-idₗ                : idˢ ; σ                             ≡ σ                                               
  η-id                    : (` zero {s = s} {S = S}) ∙ (wkˢ _)  ≡ idˢ
  η-lawˢ                  : (zero  ⋯ˢ σ) ∙ (wkˢ _ ; σ)          ≡ σ
  η-lawᴿ                  : (zero ⋯ᴿ ρ) ∙ ((wkˢ _ ; ⟪ ρ ⟫))     ≡ ⟪ ρ ⟫

  -- monad laws
  right-idˢ               : ∀ (t : S ⊢ s) → t ⋯ˢ idˢ                   ≡ t      
  right-id               : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ                   ≡ t   
  compositionalityᴿˢ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ x/t ⋯ˢ (⟪ ρ₁ ⟫ ; σ₂)                    
  compositionalityᴿᴿ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ x/t ⋯ᴿ (ρ₁ ∘ ρ₂)                     
  compositionalityˢᴿ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ x/t ⋯ˢ (σ₁ ; ⟪ ρ₂ ⟫)                         
  compositionalityˢˢ      : ∀ (x/t : S ⊢[ m ] s) → (x/t ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ x/t ⋯ˢ (σ₁ ; σ₂)

  -- traveral laws
  traversal-x             : (` x)         ⋯ˢ σ  ≡ x ⋯ˢ σ
  traversal-∀             : (∀α t)        ⋯ˢ σ  ≡ ∀α (t ⋯ˢ (σ ↑ˢ _))
  traversal-⇒             : (t₁ ⇒ t₂)     ⋯ˢ σ  ≡ (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)

  -- coincidence laws
  coincidence              : x/t ⋯ˢ ⟪ ρ ⟫                                  ≡ x/t  ⋯ᴿ ρ
  coincidence-fold         : x/t ⋯ˢ (⟪ ρ ↑ᴿ s ⟫ ; ((x/t′ ⋯ᴿ ρ) ∙ idˢ))  ≡ x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟪ ρ ⟫)

  -- proofs 

  -- the proofs are standard 
  -- <insert reference> 

  beta-lift-id = ext λ { zero → refl; (suc x) → refl }

  beta-ext-zero = refl
  beta-ext-suc  = refl
  beta-lift     = cong ((` zero) ∙_) (sym (ext λ x → coincidence))

  associativity {σ₁ = σ₁} = ext λ x → compositionalityˢˢ (σ₁ _ x) 
  distributivity = ext λ { zero → refl; (suc x) → refl }
  distributivityᴿ = ext λ { zero → coincidence; (suc x) → refl }
  interact        = refl
  comp-idᵣ        = ext λ x → (right-idˢ _)
  comp-idₗ        = refl
  η-id            = ext λ { zero → refl; (suc x) → refl }
  η-lawˢ          = ext λ { zero → refl; (suc x) → refl }
  η-lawᴿ          = ext λ { zero → refl; (suc x) → refl }

  right-id (` x)        = refl
  right-id (∀α t)       = cong ∀α_ (trans (cong (t ⋯ᴿ_) beta-lift-id) (right-id t))
  right-id (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-id t₁) (right-id t₂)

  right-idˢ (` x)        = refl
  right-idˢ (∀α t)       = cong ∀α_ (trans (cong (t ⋯ˢ_) η-id) (right-idˢ t))
  right-idˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idˢ t₁) (right-idˢ t₂)

  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }
  compositionalityᴿᴿ {m = V}             x            = refl
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (` x)        = refl
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (∀α t)       = cong ∀α_ (trans (compositionalityᴿᴿ t) (cong (t ⋯ᴿ_) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)

  lift-dist-compᴿˢ : (⟪ ρ₁ ↑ᴿ s ⟫ ; (σ₂ ↑ˢ s)) ≡ ((⟪ ρ₁ ⟫ ; σ₂) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }
  compositionalityᴿˢ {m = V}              x            = refl
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (` x)        = refl
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (∀α t)       = cong ∀α_ (trans (compositionalityᴿˢ t) (cong (t ⋯ˢ_) lift-dist-compᴿˢ))
  compositionalityᴿˢ {ρ₁ = ρ₁}  {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿˢ t₁) (compositionalityᴿˢ t₂)

  lift-dist-compˢᴿ : ((σ₁ ↑ˢ s) ; ⟪ ρ₂ ↑ᴿ s ⟫) ≡ ((σ₁ ; ⟪ ρ₂ ⟫) ↑ˢ s)
  lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    (t ⋯ᴿ (wk _)) ⋯ˢ ⟪ ρ₂ ↑ᴿ _ ⟫ ≡⟨ coincidence ⟩ 
    (t ⋯ᴿ (wk _)) ⋯ᴿ (ρ₂ ↑ᴿ _)   ≡⟨ compositionalityᴿᴿ t ⟩ 
    t ⋯ᴿ ((wk _) ∘ (ρ₂ ↑ᴿ _))    ≡⟨ sym (compositionalityᴿᴿ t) ⟩ 
    (t ⋯ᴿ ρ₂) ⋯ᴿ (wk _)          ≡⟨ cong (_⋯ᴿ (wk _)) (sym coincidence) ⟩ 
    (t ⋯ˢ ⟪ ρ₂ ⟫) ⋯ᴿ (wk _)      ∎ }
  compositionalityˢᴿ {m = V}              x            = sym coincidence
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (` x)         = sym coincidence
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (∀α t)        = cong ∀α_ (trans (compositionalityˢᴿ t) (cong (t ⋯ˢ_) lift-dist-compˢᴿ))
  compositionalityˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)     = cong₂ _⇒_ (compositionalityˢᴿ t₁) (compositionalityˢᴿ t₂)

  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ; (σ₂ ↑ˢ s)) ≡ ((σ₁ ; σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) → 
    let t = σ₁ _ x in
    begin
    (t ⋯ᴿ (wk _)) ⋯ˢ (σ₂ ↑ˢ _)    ≡⟨ compositionalityᴿˢ t ⟩ 
    t ⋯ˢ (⟪ (wk _) ⟫ ; (σ₂ ↑ˢ _)) ≡⟨ cong (t ⋯ˢ_) (ext λ y → sym coincidence) ⟩   
    t ⋯ˢ (σ₂ ; ⟪ (wk _) ⟫)        ≡⟨ sym (compositionalityˢᴿ t) ⟩ 
    (t ⋯ˢ σ₂) ⋯ᴿ (wk _)           ∎ }
  compositionalityˢˢ {m = V}              x           = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (` x)        = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (∀α t)       = cong ∀α_ (trans (compositionalityˢˢ t) (cong (t ⋯ˢ_) lift-dist-compˢˢ))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢˢ t₁) (compositionalityˢˢ t₂)
    

  traversal-x = refl
  traversal-∀ = refl
  traversal-⇒ = refl
  
  coincidence {x/t = x/t} {ρ = ρ} = 
    x/t ⋯ˢ (⟪ ρ ⟫ ; idˢ) ≡⟨ sym (compositionalityᴿˢ x/t) ⟩ 
    (x/t ⋯ᴿ ρ) ⋯ˢ idˢ    ≡⟨ right-idˢ _ ⟩ 
    x/t ⋯ᴿ ρ             ∎

  coincidence-fold {x/t = x/t} {ρ = ρ} {x/t′ = x/t′} = 
    (x/t ⋯ˢ (⟪ ρ ↑ᴿ _ ⟫ ; ((x/t′ ⋯ᴿ ρ) ∙ idˢ))) ≡⟨ cong (x/t ⋯ˢ_) (ext λ { zero → refl; (suc x) → refl }) ⟩ 
    (x/t ⋯ˢ ((x/t′ ⋯ᴿ ρ) ∙ ⟪ ρ ⟫))              ∎

{-# REWRITE 
  beta-lift-id

  beta-ext-zero 
  beta-ext-suc  
  beta-lift     

  associativity  
  distributivity
  interact       
  comp-idᵣ       
  comp-idₗ       
  η-id           
  η-lawˢ         
  η-lawᴿ      
      
  right-id         
  compositionalityᴿˢ
  compositionalityᴿᴿ
  compositionalityˢᴿ
  compositionalityˢˢ

  traversal-x
  traversal-∀
  traversal-⇒

  coincidence      
  coincidence-fold 
#-}

weaken : S ⊢ s → (s′ ∷ S) ⊢ s
weaken t = t ⋯ᴿ (wk _)


_[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
t [ t′ ] = t ⋯ˢ (t′ ∙ idˢ) 

-- Typing ----------------------------------------------------------------------

data Ctx : Scope → Set where
  ∅      : Ctx []
  _⸴_    : Ctx S → S ⊢ type → Ctx S          
  _⸴★   : Ctx S → Ctx (type ∷ S) 

variable 
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' : Ctx S

data _⊩[_]_ : {S : Scope} → Ctx S → Mode → S ⊢ type → Set

_⊩_ : {S : Scope} → Ctx S → S ⊢ type → Set
Γ ⊩ t = Γ ⊩[ T ] t 
_∈_ : {S : Scope} → S ⊢ type → Ctx S → Set
t ∈ Γ =  Γ ⊩[ V ] t

data _⊩[_]_ where
  zero  : t ∈ (Γ ⸴ t)
  suc   : t ∈ Γ → t ∈ (Γ ⸴ t′)
  suc★  : t ∈ Γ → (weaken t) ∈ (Γ ⸴★)

  `_    : t ∈ Γ → 
          Γ ⊩ t
  λx_   : (Γ ⸴ t₁) ⊩ t₂ → 
          Γ ⊩ (t₁ ⇒ t₂) 
  Λα_   : ∀ {Γ : Ctx S} {t : (type ∷ S) ⊢ type} → (Γ ⸴★) ⊩ t → 
          Γ ⊩ (∀α t)
  _·_   : Γ ⊩ (t₁ ⇒ t₂) → Γ ⊩ t₁ → 
          Γ ⊩ t₂
  _•_   : Γ ⊩ (∀α t) → (t' : S ⊢ type) → 
          Γ ⊩ (t [ t' ])
_⇒ᴿ[_]_ : Ctx S₁ → (S₁ →ᴿ S₂) → Ctx S₂ → Set
Γ₁ ⇒ᴿ[ ρ ] Γ₂ = ∀ t → t ∈ Γ₁ → (t ⋯ᴿ ρ) ∈ Γ₂

Wk : Γ ⇒ᴿ[ idᴿ ] (Γ ⸴ t) 
Wk _ = suc

wk* : Γ ⇒ᴿ[ (wk _) ] (Γ ⸴★) 
wk* _ x = suc★ x 

_⊚_ : (Γ₁ ⇒ᴿ[ ρ₁ ] Γ₂) → (Γ₂ ⇒ᴿ[ ρ₂ ] Γ₃) → (Γ₁ ⇒ᴿ[ ρ₁ ∘ ρ₂ ] Γ₃)
(ρ₁ ⊚ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_⇑ᴿ_ : (Γ₁ ⇒ᴿ[ ρ ] Γ₂) → ∀ t → (Γ₁ ⸴ t) ⇒ᴿ[ ρ ] (Γ₂ ⸴ (t ⋯ᴿ ρ))
(ρ ⇑ᴿ t) _ zero    = zero
(ρ ⇑ᴿ t) _ (suc x) = suc (ρ _ x)

_↑ᴿ* : (Γ₁ ⇒ᴿ[ ρ ] Γ₂) → (Γ₁ ⸴★) ⇒ᴿ[ ρ ↑ᴿ type ] (Γ₂ ⸴★)
(ρ ↑ᴿ*) _ (suc★ x) = suc★ (ρ _ x)
  
_⋯ᴿ[_]_ : {t : S₁ ⊢ type} {Γ₂ : Ctx S₂} → 
  Γ₁ ⊩[ m ] t → (ρ* : S₁ →ᴿ S₂) → (Γ₁ ⇒ᴿ[ ρ* ] Γ₂) → Γ₂ ⊩ (t ⋯ᴿ ρ*)
_⋯ᴿ[_]_ {m = V}  x ρ* ρ = ` (ρ _ x)
(` x)      ⋯ᴿ[ ρ* ] ρ = ` (ρ _ x)
(λx e)     ⋯ᴿ[ ρ* ] ρ = λx (e ⋯ᴿ[ ρ* ] (ρ ⇑ᴿ _))
(Λα e)     ⋯ᴿ[ ρ* ] ρ = Λα (e ⋯ᴿ[ ρ* ↑ᴿ _ ] (ρ ↑ᴿ*))
(e₁ · e₂)  ⋯ᴿ[ ρ* ] ρ = (e₁ ⋯ᴿ[ ρ* ] ρ) · (e₂ ⋯ᴿ[ ρ* ] ρ)
(e • t′)   ⋯ᴿ[ ρ* ] ρ = (e ⋯ᴿ[ ρ* ] ρ) • (t′ ⋯ᴿ ρ*)

Weaken : Γ ⊩ t → (Γ ⸴ t′) ⊩ t
Weaken e = e ⋯ᴿ[ idᴿ ] Wk
  
weaken* : Γ ⊩ t → (Γ ⸴★) ⊩ (weaken t)
weaken* e = e ⋯ᴿ[ wk _ ] wk*

opaque
  _⇒ˢ[_]_ : Ctx S₁ → (S₁ →ˢ S₂) → Ctx S₂ → Set
  Γ₁ ⇒ˢ[ σ ] Γ₂ = ∀ t → t ∈ Γ₁ → Γ₂ ⊩ (t ⋯ˢ σ)

  Idˢ : Γ ⇒ˢ[ idˢ ] Γ
  Idˢ _ x = ` x

  _◦_ : Γ₂ ⊩ (t ⋯ˢ σ) → (Γ₁ ⇒ˢ[ σ ] Γ₂) → 
          (Γ₁ ⸴ t) ⇒ˢ[ σ ] Γ₂
  (e ◦ _) _ zero    = e
  (_ ◦ σ) _ (suc x) = σ _ x

  _∙*_ : (t : S₂ ⊢ type) → (Γ₁ ⇒ˢ[ σ ] Γ₂) → (Γ₁ ⸴★) ⇒ˢ[ t ∙ σ ] Γ₂
  (t ∙* σ) _ (suc★ x) = (σ _ x)

  _⇑ˢ_ : (Γ₁ ⇒ˢ[ σ ] Γ₂) → ∀ t → (Γ₁ ⸴ t) ⇒ˢ[ σ ] (Γ₂ ⸴ (t ⋯ˢ σ))
  _⇑ˢ_ {σ = σ*} σ t = _◦_ {σ = σ*} (` zero) λ _ x → (σ _ x) ⋯ᴿ[ idᴿ ] Wk

  _⇑ˢ★ : (Γ₁ ⇒ˢ[ σ ] Γ₂) → (Γ₁ ⸴★) ⇒ˢ[ σ ↑ˢ type ] (Γ₂ ⸴★)
  _⇑ˢ★ {σ = σ*} σ = _∙*_ {σ = σ* ; wkˢ _} (` zero) λ _ x → (σ _ x) ⋯ᴿ[ wk _ ] wk*

  _⋯ˢ[_]_ : {t : S₁ ⊢ type} {Γ₂ : Ctx S₂} → 
    Γ₁ ⊩[ m ] t → (σ* : S₁ →ˢ S₂) → (σ : Γ₁ ⇒ˢ[ σ* ] Γ₂) → Γ₂ ⊩ (t ⋯ˢ σ*)
  _⋯ˢ[_]_ {m = V} x σ* σ = (σ _ x)
  (` x)      ⋯ˢ[ σ* ] σ = σ _ x
  (λx e)     ⋯ˢ[ σ* ] σ = λx (e ⋯ˢ[ σ* ] (_⇑ˢ_ {σ = σ*} σ _))
  (Λα e)     ⋯ˢ[ σ* ] σ = Λα (e ⋯ˢ[ σ* ↑ˢ _ ] (_⇑ˢ★ {σ = σ*} σ))
  (e₁ · e₂)  ⋯ˢ[ σ* ] σ = (e₁ ⋯ˢ[ σ* ] σ) · (e₂ ⋯ˢ[ σ* ] σ)
  (e • t′)   ⋯ˢ[ σ* ] σ = (e ⋯ˢ[ σ* ] σ) • (t′ ⋯ˢ σ*)

  _⨟_ : (Γ₁ ⇒ˢ[ σ₁ ] Γ₂) → (Γ₂ ⇒ˢ[ σ₂ ] Γ₃) → 
    (Γ₁ ⇒ˢ[ σ₁ ; σ₂ ] Γ₃)
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ[ _ ] σ₂

  _⟦_⟧ : (Γ ⸴ t′) ⊩ t → Γ ⊩ t′ → Γ ⊩ t
  e ⟦ e′ ⟧ = e ⋯ˢ[ idˢ ] (_◦_ {σ = idˢ} e′  Idˢ)

  _[_]* : {t : (type ∷ S) ⊢ type} → (Γ ⸴★) ⊩ t → (t′ : S ⊢ type) → Γ ⊩ (t [ t′ ])
  e [ t′ ]* = e ⋯ˢ[ t′ ∙ idˢ ] (t′ ∙* Idˢ)



-- PROVE HERE AGAIN THE SIGMA CALCULUS LAWS AND REWRITE THEM (AGAIN!!) 
-- this would also be a novel approach.

-- η-Idᴿ : {Γ : Ctx S} → _∙ᴿᴱ_ {t = t} {ρ = idᴿ} {Γ₁ = Γ} zero (_;ᴿᴿᴱ_ {ρ₁ = idᴿ} {ρ₂ = idᴿ} Wk Idᴿ) ≡ Idᴿ 
-- η-Idᴿ = fun-ext λ _ → fun-ext λ { zero → refl ; (suc x) → refl }

η-Idˢ : {Γ : Ctx S} → _◦_ {t = t} {σ = idˢ} {Γ₁ = Γ} (` zero) (_;ᴿˢᴱ_ {ρ = idᴿ} {σ = idˢ} Wk Idˢ) ≡ Idˢ 
η-Idˢ = fun-ext λ _ → fun-ext λ { zero → refl ; (suc x) → refl }

-- η-idᴿᴱ★ : {Γ : Ctx S} → _∙ᴿᴱ★_ {Γ₁ = Γ} {ρ = (wk _)} zero (_;ᴿᴿᴱ_ {ρ₁ = (wk _)} {ρ₂ = idᴿ} wk* Idᴿ) ≡ Idᴿ 
-- η-idᴿᴱ★ = fun-ext λ _ → fun-ext λ { (suc★ x) → refl }

η-idˢᴱ★ : {Γ : Ctx S} → _◦★_ {Γ₁ = Γ} {σ = wkˢ _ ; idˢ}  (` zero) (_;ᴿˢᴱ_ {ρ = (wk _)} {σ = idˢ} wk* Idˢ) ≡ Idˢ
η-idˢᴱ★ = fun-ext λ _ → fun-ext λ { (suc★ x) → refl }

beta-lift-idᴱ : (Idᴿ ⇑ᴿ t) ≡ Idᴿ
beta-lift-idᴱ = {!   !}

right-id : (e : Expr Γ t) → e ⋯ᴿ[ idᴿ ] Idᴿ ≡ e
right-id (` x)       = refl
right-id (λx e)      = cong λx_ (trans (cong (e ⋯ᴿ[ idᴿ ]_) {!   !}) (right-id e)) 
right-id (Λα e)      = {!   !} --cong Λα_ (trans (cong ((e ⋯ᴿ[ idᴿ ↑ᴿ _ ]_)) η-idᴿᴱ★) (right-id e))
right-id (e₁ · e₂)   = cong₂ _·_ (right-id e₁) (right-id e₂)
right-id (e • t′)    = cong (_• t′) (right-id e)

right-Idˢ : (e : Expr Γ t) → e ⋯ˢ[ idˢ ] Idˢ ≡ e
right-Idˢ (` x)       = refl
right-Idˢ (λx e)      = cong λx_ (trans (cong (e ⋯ˢ[ idˢ ]_) η-Idˢ) (right-Idˢ e)) 
right-Idˢ (Λα e)      = cong Λα_ (trans (cong (e ⋯ˢ[ idˢ ]_) η-idˢᴱ★) (right-Idˢ e)) 
right-Idˢ (e₁ · e₂)   = cong₂ _·_ (right-Idˢ e₁) (right-Idˢ e₂)
right-Idˢ (e • t′)    = cong (_• t′)  (right-Idˢ e) 