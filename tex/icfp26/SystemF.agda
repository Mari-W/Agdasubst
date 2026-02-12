-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module systemf where
open import Agda.Builtin.Equality.Rewrite public

-- standard eq reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
-- we rely on fun-ext for renamings/ substittutions.. 
-- with a little more effort this is not neccessary
-- <insert reference>
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; zero; suc) 
open import Data.List using (List; []; _∷_)

data Type (n : Nat) : Set where
  `_   : Fin n → Type n
  ∀α_  : Type (suc n) → Type n
  _⇒_  : Type n → Type n → Type n

variable
  n n′ n₁ n₂ n₃ : Nat
  x x′ x₁ x₂ x₃ : Fin n
  T T′ T₁ T₂ T₃ : Type n

-- renamings are functions that with 
-- primitive operations that reduce
-- they already have (nearly) all 
-- definitional equalities we need!
_→ᴿ_ : Nat → Nat → Set
n₁ →ᴿ n₂ = Fin n₁ → Fin n₂

variable
  ρ ρ′ ρ₁ ρ₂ ρ₃ : n₁ →ᴿ n₂

id : n →ᴿ n
id x = x
--open import Function using (id)

↑ᴿ : n₁ →ᴿ n₂ → suc n₁ →ᴿ suc n₂
↑ᴿ ρ zero    = zero
↑ᴿ ρ (suc x) = suc (ρ x) 

_∘_ : n₁ →ᴿ n₂ → n₂ →ᴿ n₃ → n₁ →ᴿ n₃
(ρ₁ ∘ ρ₂) x = ρ₂ (ρ₁ x)

_⋯ᴿ_ : Type n₁ → n₁ →ᴿ n₂ → Type n₂ 
(` x)      ⋯ᴿ ρ = ` ρ x
(∀α t)     ⋯ᴿ ρ = ∀α (t ⋯ᴿ ↑ᴿ ρ)
(t₁ ⇒ t₂)  ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)

_→ˢ_ : Nat → Nat → Set
n₁ →ˢ n₂ = Fin n₁ → Type n₂

variable
  σ σ₁ σ₂ σ₃ : n₁ →ˢ n₂  

-- just helpers! 
-- {-# inline -#} so that agda does not say we rewrite 
-- on reducing symbols..
⟨_⟩ : n₁ →ᴿ n₂ → n₁ →ˢ n₂ 
⟨ ρ ⟩ x = ` ρ x
{-# INLINE ⟨_⟩ #-} 

-- the primitives for substitution must be opaque!
-- otherwise we cannot rewrite on them (even if inlined..)
-- since the violate the rewrite rule rules 
-- ask me for an example for where it breaks if neccessary!
opaque
  -- σₛ­ₚ calculus with first class renamings
  
  -- syntax
  _∙_ : Type n₂ → n₁ →ˢ n₂ → suc n₁ →ˢ n₂    
  (t ∙ σ) zero = t
  (t ∙ σ) (suc x) = σ x 

  -- instantiation is defined on both terms and 
  -- variables at the same time, this is important 
  -- so we can rewrite on variable lookup
  -- (introducing an extra lookup operator would 
  -- i guess be possible, but also introduces noise 
  -- in the laws)

  -- blocking alias for lookup
  _&ˢ_ : Fin n₁ → n₁ →ˢ n₂ → Type n₂
  x &ˢ σ = σ x 
  
  _⋯ˢ_ : Type n₁ → n₁ →ˢ n₂ → Type n₂

  ↑ˢ : n₁ →ˢ n₂ → suc n₁ →ˢ suc n₂
  ↑ˢ σ = (` zero) ∙ λ x → (σ x) ⋯ᴿ suc

  (` x)         ⋯ˢ σ = σ x
  (∀α t)        ⋯ˢ σ = ∀α (t ⋯ˢ ↑ˢ σ)
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)

  _⨟_ : n₁ →ˢ n₂ → n₂ →ˢ n₃ → n₁ →ˢ n₃
  (σ₁ ⨟ σ₂) x = (σ₁ x) ⋯ˢ σ₂

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
  beta-lift-id            : ↑ᴿ {n₁ = n₁} id ≡ id

  -- beta laws
  beta-id                 : x &ˢ ⟨ id ⟩ ≡ ` x  
  beta-wk                 : x &ˢ ⟨ suc ⟩ ≡ ` suc x 
  beta-ext-zero           : zero  &ˢ (T ∙ σ)   ≡ T                             
  beta-ext-suc            : suc x &ˢ (T ∙ σ)  ≡ x &ˢ σ 
  beta-lift               : ↑ˢ σ            ≡ (` zero) ∙ (σ ⨟ ⟨ suc ⟩)

  -- interaction laws
  associativity           : (σ₁ ⨟ σ₂) ⨟ σ₃                        ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  distributivity          : (T ∙ σ₁) ⨟ σ₂                         ≡ ((T ⋯ˢ σ₂) ∙ (σ₁ ⨟ σ₂)) 
  distributivityᴿ         : (T ∙ σ₁) ⨟ ⟨ ρ₂ ⟩                     ≡ ((T ⋯ᴿ ρ₂) ∙ (σ₁ ⨟ ⟨ ρ₂ ⟩)) 
  interact                : ⟨ suc ⟩ ⨟ (T ∙ σ)                     ≡ σ                                        
  comp-idᵣ                : σ ⨟ ⟨ id ⟩                             ≡ σ                                               
  comp-idₗ                : ⟨ id ⟩ ⨟ σ                             ≡ σ                                               
  η-id                    : _∙_ {n₁ = n₁} (` zero)  ⟨ suc ⟩  ≡ ⟨ id ⟩
  η-lawˢ                  : (zero &ˢ σ) ∙ (⟨ suc ⟩ ⨟ σ)       ≡ σ
  η-lawᴿ                  : (` ρ zero) ∙ (⟨ suc ⟩ ⨟ ⟨ ρ ⟩)    ≡ ⟨ ρ ⟩

  -- monad laws
  right-id                : ∀ (T : Type n) → T ⋯ᴿ id                   ≡ T   
  compositionalityᴿˢ      : ∀ (T : Type n) → (T ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                    
  compositionalityᴿᴿ      : ∀ (T : Type n) → (T ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ T ⋯ᴿ (ρ₁ ∘ ρ₂)                     
  compositionalityˢᴿ      : ∀ (T : Type n) → (T ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ T ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (T : Type n) → (T ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (σ₁ ⨟ σ₂)

  -- traveral laws
  traversal-x             : (` x)         ⋯ˢ σ  ≡ x &ˢ σ
  traversal-∀             : (∀α T)        ⋯ˢ σ  ≡ ∀α (T ⋯ˢ (↑ˢ σ))
  traversal-⇒             : (T₁ ⇒ T₂)     ⋯ˢ σ  ≡ (T₁ ⋯ˢ σ) ⇒ (T₂ ⋯ˢ σ)

  -- coincidence laws
  coincidence              : T ⋯ˢ ⟨ ρ ⟩                                  ≡ T  ⋯ᴿ ρ
  coincidence-fold         : T ⋯ˢ (⟨ ↑ᴿ ρ ⟩ ⨟ ((T′ ⋯ᴿ ρ) ∙ ⟨ id ⟩))  ≡ T ⋯ˢ ((T′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩)
  
  
  -- proofs 
  
{-# REWRITE 
  beta-lift-id

  beta-id
  beta-wk
  beta-ext-zero 
  beta-ext-suc  
  beta-lift     

  associativity  
  distributivity 
  distributivityᴿ
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

weaken : Type n → Type (suc n)
weaken t = t ⋯ᴿ suc

_[_] : Type (suc n) → Type n → Type n
t [ t′ ] = t ⋯ˢ (t′ ∙ ⟨ id ⟩) 

data Ctx : Nat → Set where
  ∅    : Ctx zero
  _,_  : Ctx n → Type n → Ctx n          
  _,*  : Ctx n → Ctx (suc n) 

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx n

data _∈_ : Type n → Ctx n → Set where
  zero  : T ∈ (Γ , T)
  suc   : T ∈ Γ → T ∈ (Γ , T′)
  suc*  : T ∈ Γ → (weaken T) ∈ (Γ ,*)

data Expr : Ctx n → Type n → Set where
  `_    : T ∈ Γ → 
          Expr Γ T
  λx_   : Expr (Γ , T₁) T₂ → 
          Expr Γ (T₁ ⇒ T₂) 
  Λα_   : Expr (Γ ,*) T → 
          Expr Γ (∀α T)
  _·_   : Expr Γ (T₁ ⇒ T₂) → 
          Expr Γ T₁ → 
          Expr Γ T₂
  _•_   : Expr Γ (∀α T) →
          (T' : Type n) → 
          Expr Γ (T [ T' ]) 

_→ᴿ[_]_ : Ctx n₁ → (n₁ →ᴿ n₂) → Ctx n₂ → Set
Γ₁ →ᴿ[ ρ ] Γ₂ = ∀ T → T ∈ Γ₁ → (T ⋯ᴿ ρ) ∈ Γ₂

_⊚_ : (Γ₁ →ᴿ[ ρ₁ ] Γ₂) → (Γ₂ →ᴿ[ ρ₂ ] Γ₃) → (Γ₁ →ᴿ[ ρ₁ ∘ ρ₂ ] Γ₃)
(ρ₁ ⊚ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

Wk : Γ →ᴿ[ id ] (Γ , T) 
Wk _ = suc

wk* : Γ →ᴿ[ suc ] (Γ ,*) 
wk* _ x = suc* x 

_⇑ᴿ_ : (Γ₁ →ᴿ[ ρ ] Γ₂) → ∀ T → (Γ₁ , T) →ᴿ[ ρ ] (Γ₂ , (T ⋯ᴿ ρ))
(ρ ⇑ᴿ _) _ zero    = zero
(ρ ⇑ᴿ _) _ (suc x) = suc (ρ _ x)

↑ᴿ* : (Γ₁ →ᴿ[ ρ ] Γ₂) → (Γ₁ ,*) →ᴿ[ ↑ᴿ ρ ] (Γ₂ ,*)
↑ᴿ* ρ _ (suc* x) = suc* (ρ _ x)

_⋯ᴿ[_]_ : {T : Type n₁} {Γ₂ : Ctx n₂} → 
  Expr Γ₁ T → (ρ* : n₁ →ᴿ n₂) → (Γ₁ →ᴿ[ ρ* ] Γ₂) → Expr Γ₂ (T ⋯ᴿ ρ*)
(` x)      ⋯ᴿ[ ρ* ] ρ = ` (ρ _ x)
(λx e)     ⋯ᴿ[ ρ* ] ρ = λx (e ⋯ᴿ[ ρ* ] (ρ ⇑ᴿ _))
(Λα e)     ⋯ᴿ[ ρ* ] ρ = Λα (e ⋯ᴿ[ ↑ᴿ ρ* ] (↑ᴿ* ρ))
(e₁ · e₂)  ⋯ᴿ[ ρ* ] ρ = (e₁ ⋯ᴿ[ ρ* ] ρ) · (e₂ ⋯ᴿ[ ρ* ] ρ)
(e • t′)   ⋯ᴿ[ ρ* ] ρ = (e ⋯ᴿ[ ρ* ] ρ) • (t′ ⋯ᴿ ρ*)

Weaken : Expr Γ T → Expr (Γ , T′) T
Weaken e = e ⋯ᴿ[ id ] Wk
  
weaken* : Expr Γ T → Expr (Γ ,*) (weaken T)
weaken* e = e ⋯ᴿ[ suc ] wk*

