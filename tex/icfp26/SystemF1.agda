-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module SystemF1 where
open import Agda.Builtin.Equality.Rewrite public

-- standard eq reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst; module ≡-Reasoning)
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
  α α′ α₁ α₂ α₃ : Fin n
  T T′ T₁ T₂ T₃ : Type n

-- renamings are functions that with 
-- primitive operations that reduce
-- they already have (nearly) all 
-- definitional equalities we need!
--open import Function using (id)

_→ᴿ_ : Nat → Nat → Set
n₁ →ᴿ n₂ = Fin n₁ → Fin n₂ 

variable
  ρ ρ′ ρ₁ ρ₂ ρ₃ : n₁ →ᴿ n₂

opaque
  wk : n →ᴿ (suc n)
  wk = suc

  idᴿ : n →ᴿ n
  idᴿ α = α

  _∙ᴿ_ :  Fin n₂ → n₁ →ᴿ n₂ → suc n₁ →ᴿ n₂    
  (α ∙ᴿ ρ) zero = α
  (_ ∙ᴿ ρ) (suc α) = ρ α 

  _&ᴿ_ : Fin n₁ → n₁ →ᴿ n₂ → Fin n₂
  α &ᴿ σ = σ α 

  _∘_ : n₁ →ᴿ n₂ → n₂ →ᴿ n₃ → n₁ →ᴿ n₃
  (ρ₁ ∘ ρ₂) α = ρ₂ (ρ₁ α)

_↑ᴿ : n₁ →ᴿ n₂ → suc n₁ →ᴿ suc n₂
_↑ᴿ ρ = zero ∙ᴿ (ρ ∘ wk)

opaque
  _⋯ᴿ_ : Type n₁ → n₁ →ᴿ n₂ → Type n₂ 
  (` α)      ⋯ᴿ ρ = ` ρ α
  (∀α t)     ⋯ᴿ ρ = ∀α (t ⋯ᴿ (ρ ↑ᴿ))
  (t₁ ⇒ t₂)  ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)

_→ˢ_ : Nat → Nat → Set
n₁ →ˢ n₂ = Fin n₁ → Type n₂

variable
  σ σ′ σ₁ σ₂ σ₃ : n₁ →ˢ n₂  

opaque
-- just helpers! 
-- {-# inline -#} so that agda does not say we rewrite 
-- on reducing symbols..
-- the primitives for substitution must be opaque!
-- otherwise we cannot rewrite on them (even if inlined..)
-- since the violate the rewrite rule rules 
-- ask me for an example for where it breaks if neccessary!
-- opaque
  -- σₛ­ₚ calculus with first class renamings
  ⟨_⟩ : n₁ →ᴿ n₂ → n₁ →ˢ n₂ 
  ⟨ ρ ⟩ α = ` (α &ᴿ ρ)
  
  -- syntax
  _∙_ : Type n₂ → n₁ →ˢ n₂ → suc n₁ →ˢ n₂    
  (t ∙ σ) zero = t
  (t ∙ σ) (suc α) = σ α 

  -- blocking alias for lookup
  _&ˢ_ : Fin n₁ → n₁ →ˢ n₂ → Type n₂
  α &ˢ σ = σ α 
  
  _⋯ˢ_ : Type n₁ → n₁ →ˢ n₂ → Type n₂

  _↑ˢ : n₁ →ˢ n₂ → suc n₁ →ˢ suc n₂
  _↑ˢ σ = (` zero) ∙ λ α → (σ α) ⋯ᴿ wk

  (` α)         ⋯ˢ σ = σ α
  (∀α t)        ⋯ˢ σ = ∀α (t ⋯ˢ (σ ↑ˢ))
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)

  _⨟_ : n₁ →ˢ n₂ → n₂ →ˢ n₃ → n₁ →ˢ n₃
  (σ₁ ⨟ σ₂) α = (σ₁ α) ⋯ˢ σ₂

postulate
  -- rewrite system
  -- you probably shouldnt care too much about 
  -- the spcific system here, it just "the same as in autosubst" 
  -- namely the σₛₚ calculus
  
  -- importantly: it is locally confluent and terminating
  -- (not complete in presence of first class renamings)
  -- <insert reference>
  -- thus valid rewrite rules 

  -- more importantly, we do not 
  -- (by convention, currently not enforced) use (σ _ α) 
  -- to lookup a variable in a substittution, 
  -- but rather use the blocking symbol α ⋯ˢ σ
  -- on which we can rewrite the sigma laws!

  -- first-class renamings 
  `beta-id                 : α &ᴿ idᴿ ≡ α  
  `beta-wk                 : α &ᴿ wk ≡ suc α 
  `beta-ext-zero           : zero  &ᴿ (α ∙ᴿ ρ)   ≡ α                            
  `beta-ext-suc            : suc α &ᴿ (α′ ∙ᴿ ρ)  ≡ α &ᴿ ρ
  `beta-comp               : (α &ᴿ (ρ₁ ∘ ρ₂)) ≡ ((α &ᴿ ρ₁) &ᴿ ρ₂)


  -- beta laws
  -- beta-id                 : α &ˢ ⟨ idᴿ ⟩ ≡ ` α  
  -- beta-wk                 : α &ˢ ⟨ suc ⟩ ≡ ` suc α
  beta-ext-zero           : zero  &ˢ (T ∙ σ)   ≡ T                             
  beta-ext-suc            : suc α &ˢ (T ∙ σ)  ≡ α &ˢ σ 
  beta-lift               : σ ↑ˢ             ≡ (` zero) ∙ (σ ⨟ ⟨ wk ⟩)
  beta-comp               : (α &ˢ (σ₁ ⨟ σ₂)) ≡ ((α &ˢ σ₁) ⋯ˢ σ₂)

  -- interaction laws
  associativity           : (σ₁ ⨟ σ₂) ⨟ σ₃                        ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  distributivity          : (T ∙ σ₁) ⨟ σ₂                         ≡ ((T ⋯ˢ σ₂) ∙ (σ₁ ⨟ σ₂)) 
  distributivityᴿ         : (T ∙ σ₁) ⨟ ⟨ ρ₂ ⟩                     ≡ ((T ⋯ᴿ ρ₂) ∙ (σ₁ ⨟ ⟨ ρ₂ ⟩)) 
  interact                : ⟨ wk ⟩ ⨟ (T ∙ σ)                     ≡ σ                                        
  comp-idᵣ                : σ ⨟ ⟨ idᴿ ⟩                             ≡ σ                                               
  comp-idₗ                : ⟨ idᴿ ⟩ ⨟ σ                             ≡ σ                                               
  η-id                    : _∙_ {n₁ = n₁} (` zero)  ⟨ wk ⟩        ≡ ⟨ idᴿ ⟩
  η-lawˢ                  : (zero &ˢ σ) ∙ (⟨ wk ⟩ ⨟ σ)            ≡ σ
  -- η-lawᴿ                  : (` (zero &ᴿ ρ)) ∙ (⟨ wk ⟩ ⨟ ⟨ ρ ⟩)    ≡ ⟨ ρ ⟩

  `associativity           : (ρ₁ ∘ ρ₂) ∘ ρ₃                        ≡ ρ₁ ∘ (ρ₂ ∘ ρ₃)                     
  `distributivity          : (α ∙ᴿ ρ₁) ∘ ρ₂                         ≡ ((α &ᴿ ρ₂) ∙ᴿ (ρ₁ ∘ ρ₂))
  `interact                : wk ∘ (α ∙ᴿ ρ)                     ≡ ρ                                        
  `comp-idᵣ                : ρ ∘ idᴿ                             ≡ ρ                                               
  `comp-idₗ                : idᴿ ∘ ρ                             ≡ ρ                                               
  `η-id                    : _∙ᴿ_ {n₁ = n₁} zero wk  ≡ idᴿ
  `η-lawˢ                  : (zero &ᴿ ρ) ∙ᴿ (wk ∘ ρ)       ≡ ρ

  -- monad laws
  right-id                : ∀ (T : Type n) → T ⋯ᴿ idᴿ                   ≡ T   
  compositionalityᴿˢ      : ∀ (T : Type n) → (T ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                    
  compositionalityᴿᴿ      : ∀ (T : Type n) → (T ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ T ⋯ᴿ (ρ₁ ∘ ρ₂)                     
  compositionalityˢᴿ      : ∀ (T : Type n) → (T ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ T ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (T : Type n) → (T ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (σ₁ ⨟ σ₂)


  traversal-x             : (` α)         ⋯ˢ σ  ≡ α &ˢ σ
  traversal-∀             : (∀α T)        ⋯ˢ σ  ≡ ∀α (T ⋯ˢ (σ ↑ˢ))
  traversal-⇒             : (T₁ ⇒ T₂)     ⋯ˢ σ  ≡ (T₁ ⋯ˢ σ) ⇒ (T₂ ⋯ˢ σ)
  
  `traversal-x             : (` α)         ⋯ᴿ ρ  ≡ ` (α &ᴿ ρ)
  `traversal-∀             : (∀α T)        ⋯ᴿ ρ  ≡ ∀α (T ⋯ᴿ (ρ ↑ᴿ))
  `traversal-⇒             : (T₁ ⇒ T₂)     ⋯ᴿ ρ  ≡ (T₁ ⋯ᴿ ρ) ⇒ (T₂ ⋯ᴿ ρ)

  -- coincidence laws
  coincidence              : T ⋯ˢ ⟨ ρ ⟩                           ≡ T  ⋯ᴿ ρ
  coincidencex             : α &ˢ ⟨ ρ ⟩                           ≡ ` (α  &ᴿ ρ)
  coincidence-fold         : T ⋯ˢ (⟨ ρ ↑ᴿ ⟩ ⨟ ((T′ ⋯ᴿ ρ) ∙ ⟨ idᴿ ⟩))  ≡ T ⋯ˢ ((T′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩)
  coincidence-foldx        : α &ˢ (⟨ ρ ↑ᴿ ⟩ ⨟ ((T′ ⋯ᴿ ρ) ∙ ⟨ idᴿ ⟩))  ≡ α &ˢ ((T′ ⋯ᴿ ρ) ∙ ⟨ ρ ⟩) 
  coincidence-comp         : ⟨ ρ₁ ⟩ ⨟ ⟨ ρ₂ ⟩ ≡ ⟨ ρ₂ ∘ ρ₂ ⟩
  coincidence-comp-fold    : (⟨  zero ∙ᴿ (ρ₁ ∘ (ρ₂ ∘ wk)) ⟩ ⨟ ((T′ ⋯ᴿ (ρ₁ ∘ ρ₂)) ∙ ⟨ idᴿ ⟩)) ≡ ((T′ ⋯ᴿ (ρ₁ ∘ ρ₂)) ∙ (⟨ ρ₁ ⟩ ⨟ ⟨ ρ₂ ⟩))
  -- proofs 

{-# REWRITE 
  `beta-id       
  `beta-wk       
  `beta-ext-zero 
  `beta-ext-suc     
  `beta-comp 

  beta-ext-zero 
  beta-ext-suc  
  beta-lift     
  beta-comp 

  associativity  
  distributivity 
  distributivityᴿ
  interact       
  comp-idᵣ       
  comp-idₗ       
  η-id           
  η-lawˢ         

  `associativity  
  `distributivity 
  `interact       
  `comp-idᵣ       
  `comp-idₗ       
  `η-id           
  `η-lawˢ          

  right-id           
  compositionalityᴿˢ 
  compositionalityᴿᴿ 
  compositionalityˢᴿ 
  compositionalityˢˢ 

  traversal-x 
  traversal-∀ 
  traversal-⇒ 

  `traversal-x
  `traversal-∀
  `traversal-⇒

  coincidence       
  coincidence-fold  
  coincidence-comp  
  coincidence-comp-fold
#-}


weaken : Type n → Type (suc n)
weaken t = t ⋯ᴿ wk

_[_] : Type (suc n) → Type n → Type n
t [ t′ ] = t ⋯ˢ (t′ ∙ ⟨ idᴿ ⟩) 

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

variable
  x x′ x₁ x₂ x₃ : T ∈ Γ

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
  _·*_   : Expr Γ (∀α T) →
          (T′ : Type n) → 
          Expr Γ (T [ T′ ]) 

variable
  e e′ e₁ e₂ e₃ : Expr Γ T

_∣_⇒ᴿ_ : n₁ →ᴿ n₂ → Ctx n₁ → Ctx n₂ → Set
ρ ∣ Γ₁ ⇒ᴿ Γ₂ = ∀ T → T ∈ Γ₁ → (T ⋯ᴿ ρ) ∈ Γ₂

variable
  Ρ Ρ′ Ρ₁ Ρ₂ Ρ₃ : ρ ∣ Γ₁ ⇒ᴿ Γ₂

Id : idᴿ ∣ Γ ⇒ᴿ Γ
Id _ x = x -- no subst right-id

Wk : idᴿ ∣ Γ ⇒ᴿ (Γ , T) 
Wk _ = suc

wk* : wk ∣ Γ ⇒ᴿ (Γ ,*) 
wk* _ x = suc* x 

_,_∣_⊚_ : ∀ ρ₁ ρ₂ → ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ρ₁ ∘ ρ₂) ∣ Γ₁ ⇒ᴿ Γ₃
(_ , _ ∣ Ρ₁ ⊚ Ρ₂) _ x = Ρ₂ _ (Ρ₁ _ x)

_⊚_ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ρ₁ ∘ ρ₂) ∣ Γ₁ ⇒ᴿ Γ₃
_⊚_ = _,_∣_⊚_ _ _

_∣_⇑ᴿ_ : ∀ ρ → ρ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ρ ∣ (Γ₁ , T) ⇒ᴿ (Γ₂ , (T ⋯ᴿ ρ))
(_ ∣ Ρ ⇑ᴿ _) _ zero    = zero
(_ ∣ Ρ ⇑ᴿ _) _ (suc x) = suc (Ρ _ x)

_⇑ᴿ_ : ρ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ρ ∣ (Γ₁ , T) ⇒ᴿ (Γ₂ , (T ⋯ᴿ ρ))
_⇑ᴿ_ = _ ∣_⇑ᴿ_

_∣_↑ᴿ* : ∀ ρ → ρ ∣ Γ₁ ⇒ᴿ Γ₂ → (ρ ↑ᴿ) ∣ (Γ₁ ,*) ⇒ᴿ (Γ₂ ,*)
(_ ∣ Ρ ↑ᴿ*) _ (suc* x) = suc* (Ρ _ x) --suc* (Ρ _ x) -- no subst swap ren wk

↑ᴿ*_ : ρ ∣ Γ₁ ⇒ᴿ Γ₂ → (ρ ↑ᴿ) ∣ (Γ₁ ,*) ⇒ᴿ (Γ₂ ,*)
↑ᴿ*_ = _ ∣_↑ᴿ*

-- new symbol?
_∣_⋯ᴿ_ : {T : Type n₁} {Γ₂ : Ctx n₂} → (ρ : n₁ →ᴿ n₂) →
  Expr Γ₁ T → ρ ∣ Γ₁ ⇒ᴿ Γ₂ → Expr Γ₂ (T ⋯ᴿ ρ)
_ ∣ (` x)      ⋯ᴿ Ρ = ` (Ρ _ x)
_ ∣ (λx e)     ⋯ᴿ Ρ = λx (_ ∣ e ⋯ᴿ (Ρ ⇑ᴿ _))
_ ∣ (Λα e)     ⋯ᴿ Ρ = Λα (_ ∣ e ⋯ᴿ (↑ᴿ* Ρ))
_ ∣ (e₁ · e₂)  ⋯ᴿ Ρ = (_ ∣ e₁ ⋯ᴿ Ρ) · (_ ∣ e₂ ⋯ᴿ Ρ)
ρ ∣ (e ·* T′)  ⋯ᴿ Ρ = (ρ ∣ e ⋯ᴿ Ρ) ·* (T′ ⋯ᴿ ρ) -- no subst swap ren single subst

Weaken : Expr Γ T → Expr (Γ , T′) T
Weaken e = idᴿ ∣ e ⋯ᴿ Wk -- no subst right-id
  
weaken* : Expr Γ T → Expr (Γ ,*) (weaken T)
weaken* e = wk ∣ e ⋯ᴿ wk*

_∣_⇒ˢ_ : n₁ →ˢ n₂ → Ctx n₁ → Ctx n₂ → Set
σ ∣ Γ₁ ⇒ˢ Γ₂ = ∀ T → T ∈ Γ₁ → Expr Γ₂ (T ⋯ˢ σ) 

variable
  Σ Σ′ Σ₁ Σ₂ Σ₃ : σ ∣ Γ₁ ⇒ˢ Γ₂ 

_∣⟪_⟫ : ∀ ρ → ρ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ρ ⟩ ∣ Γ₁ ⇒ˢ Γ₂ 
(ρ ∣⟪ Ρ ⟫) _ x = ` Ρ _ x

⟪_⟫ : ρ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ρ ⟩ ∣ Γ₁ ⇒ˢ Γ₂ 
⟪_⟫ = _ ∣⟪_⟫

Idˢ : ⟨ idᴿ ⟩ ∣ Γ ⇒ˢ Γ 
Idˢ _ = `_ -- no subst right-⟨ idᴿ ⟩

Wkˢ : ∀ T → ⟨ idᴿ ⟩ ∣ Γ ⇒ˢ (Γ , T) 
Wkˢ _ = idᴿ ∣⟪ Wk ⟫

wk*ˢ : ⟨ wk ⟩ ∣ Γ ⇒ˢ (Γ ,*) 
wk*ˢ = wk ∣⟪ wk* ⟫

-- new symbol?
_∣_∙_ : ∀ σ → Expr Γ₂ (T ⋯ˢ σ) → σ ∣ Γ₁ ⇒ˢ Γ₂ → σ ∣ (Γ₁ , T) ⇒ˢ Γ₂
(_ ∣ e ∙ Σ) _ zero     = e
(_ ∣ e ∙ Σ) _ (suc x)  = Σ _ x

_∣_∙*_ : ∀ σ T → σ ∣ Γ₁ ⇒ˢ Γ₂ → (T ∙ σ) ∣ (Γ₁ ,*) ⇒ˢ Γ₂
(_ ∣ T ∙* Σ) _ (suc* x) = Σ _ x -- no subst swap wk single subst

_∣_⇑ˢ_ : ∀ σ → σ ∣ Γ₁ ⇒ˢ Γ₂ → ∀ T → σ ∣ (Γ₁ , T) ⇒ˢ (Γ₂ , (T ⋯ˢ σ))
σ ∣ Σ ⇑ˢ T = σ ∣ (` zero) ∙ λ _ x → idᴿ ∣ (Σ _ x) ⋯ᴿ Wk -- no subst swap sub wk

_∣_↑ˢ* : ∀ σ → σ ∣ Γ₁ ⇒ˢ Γ₂ → (σ ↑ˢ) ∣ (Γ₁ ,*) ⇒ˢ (Γ₂ ,*)
(σ ∣ Σ ↑ˢ*) _ (suc* x) = _ ∣ (Σ _ x) ⋯ᴿ wk* -- ? ∣ (Σ _ x) ⋯ᴿ wk*

-- new symbol?
_∣_⋯ˢ_ : {T : Type n₁} {Γ₂ : Ctx n₂} → (σ : n₁ →ˢ n₂) →
  Expr Γ₁ T → σ ∣ Γ₁ ⇒ˢ Γ₂ → Expr Γ₂ (T ⋯ˢ σ)
σ ∣ (` x)      ⋯ˢ Σ = Σ _ x
σ ∣ (λx e)     ⋯ˢ Σ = λx (σ ∣ e ⋯ˢ (σ ∣ Σ ⇑ˢ _))
σ ∣ (Λα e)     ⋯ˢ Σ = Λα ((σ ↑ˢ) ∣ e ⋯ˢ (σ ∣ Σ ↑ˢ*))
σ ∣ (e₁ · e₂)  ⋯ˢ Σ = (σ ∣ e₁ ⋯ˢ Σ) · (σ ∣ e₂ ⋯ˢ Σ)
σ ∣ (e ·* T′)  ⋯ˢ Σ = (σ ∣ e ⋯ˢ Σ) ·* (T′ ⋯ˢ σ) -- no subst swap sub single subst

_,_∣_⨾_ : ∀ σ₁ σ₂ → σ₁ ∣ Γ₁ ⇒ˢ Γ₂ → σ₂ ∣ Γ₂ ⇒ˢ Γ₃ → (σ₁ ⨟ σ₂) ∣ Γ₁ ⇒ˢ Γ₃
(_ , _ ∣ Σ₁ ⨾ Σ₂) _ x = _ ∣ (Σ₁ _ x) ⋯ˢ Σ₂

η-Id : ⟨ idᴿ ⟩ ∣ (` (zero {T = T} {Γ = Γ})) ∙ (Wkˢ T) ≡ (Idˢ {Γ = Γ , T})
η-Id = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

η*-Id : ⟨ idᴿ ⟩ ∣ (Idˢ {Γ = Γ}) ↑ˢ* ≡ Idˢ
η*-Id = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Right-Id : ∀ (e : Expr Γ T) → ⟨ idᴿ ⟩ ∣ e ⋯ˢ Idˢ ≡ e
Right-Id (` x)      = refl
Right-Id (λx e)     = cong λx_ (trans (cong (⟨ idᴿ ⟩ ∣ e ⋯ˢ_) η-Id) (Right-Id e))
Right-Id (Λα e)     = cong Λα_ (trans (cong (⟨ idᴿ ⟩ ∣ e ⋯ˢ_) η*-Id) (Right-Id e))
Right-Id (e₁ · e₂)  = cong₂ _·_ (Right-Id e₁) (Right-Id e₂)
Right-Id (e ·* T′)  = cong (_·* T′) (Right-Id e)

Lift-Dist-Compᴿᴿ : (Ρ₁ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (Ρ₂ : ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  ρ₁ , ρ₂ ∣ ( ρ₁ ∣ Ρ₁ ⇑ᴿ T) ⊚ (ρ₂ ∣ Ρ₂ ⇑ᴿ (T ⋯ᴿ ρ₁)) ≡ ((ρ₁ ∘ ρ₂) ∣ (ρ₁ , ρ₂ ∣ Ρ₁ ⊚ Ρ₂) ⇑ᴿ T)
Lift-Dist-Compᴿᴿ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

lift*-dist-Compᴿᴿ : (ρ₁ : n₁ →ᴿ n₂) (ρ₂ : n₂ →ᴿ n₃) (Ρ₁ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (Ρ₂ : ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  (ρ₁ ↑ᴿ) , (ρ₂ ↑ᴿ) ∣ ( ρ₁ ∣ Ρ₁ ↑ᴿ*) ⊚ (ρ₂ ∣ Ρ₂ ↑ᴿ*) ≡ ((ρ₁ ∘ ρ₂) ∣ (ρ₁ , ρ₂ ∣ Ρ₁ ⊚ Ρ₂) ↑ᴿ*)
lift*-dist-Compᴿᴿ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Compositionalityᴿᴿ : ∀ (e : Expr Γ₁ T) (ρ₁ : n₁ →ᴿ n₂) (ρ₂ : n₂ →ᴿ n₃) (Ρ₁ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (Ρ₂ : ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃) → 
  ρ₂ ∣ (ρ₁ ∣ e ⋯ᴿ Ρ₁) ⋯ᴿ Ρ₂ ≡ (ρ₁ ∘ ρ₂) ∣ e ⋯ᴿ (ρ₁ , ρ₂ ∣ Ρ₁ ⊚ Ρ₂) 
Compositionalityᴿᴿ (` x)      _ _ _ _    = refl
Compositionalityᴿᴿ (λx e)     _ _ _ _    = cong λx_ (trans (Compositionalityᴿᴿ e _ _ _ _) (cong (_ ∣ e ⋯ᴿ_) (Lift-Dist-Compᴿᴿ _ _)))
Compositionalityᴿᴿ (Λα e)     _ _ _ _    = cong Λα_ (trans (Compositionalityᴿᴿ e _ _ _ _) (cong (_ ∣ e ⋯ᴿ_) (lift*-dist-Compᴿᴿ _ _ _ _)))
Compositionalityᴿᴿ (e₁ · e₂)  _ _ _ _    = cong₂ _·_ (Compositionalityᴿᴿ e₁ _ _ _ _) (Compositionalityᴿᴿ e₂ _ _ _ _)
Compositionalityᴿᴿ (e ·* T′) ρ₁ ρ₂ Ρ₁ Ρ₂ = cong (_·* (T′ ⋯ᴿ (ρ₁ ∘ ρ₂))) (Compositionalityᴿᴿ e _ _ _ _)