-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module SystemF where
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
  α α′ α₁ α₂ α₃ : Fin n
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
id α = α
--open import Function using (id)

↑ᴿ : n₁ →ᴿ n₂ → suc n₁ →ᴿ suc n₂
↑ᴿ ρ zero    = zero
↑ᴿ ρ (suc α) = suc (ρ α) 

_∘_ : n₁ →ᴿ n₂ → n₂ →ᴿ n₃ → n₁ →ᴿ n₃
(ρ₁ ∘ ρ₂) α = ρ₂ (ρ₁ α)

_⋯ᴿ_ : Type n₁ → n₁ →ᴿ n₂ → Type n₂ 
(` α)      ⋯ᴿ ρ = ` ρ α
(∀α t)     ⋯ᴿ ρ = ∀α (t ⋯ᴿ ↑ᴿ ρ)
(t₁ ⇒ t₂)  ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)

_→ˢ_ : Nat → Nat → Set
n₁ →ˢ n₂ = Fin n₁ → Type n₂

variable
  σ σ′ σ₁ σ₂ σ₃ : n₁ →ˢ n₂  

-- just helpers! 
-- {-# inline -#} so that agda does not say we rewrite 
-- on reducing symbols..
⟨_⟩ : n₁ →ᴿ n₂ → n₁ →ˢ n₂ 
⟨ ρ ⟩ α = ` ρ α
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
  (t ∙ σ) (suc α) = σ α 

  -- blocking alias for lookup
  _&ˢ_ : Fin n₁ → n₁ →ˢ n₂ → Type n₂
  α &ˢ σ = σ α 
  
  _⋯ˢ_ : Type n₁ → n₁ →ˢ n₂ → Type n₂

  ↑ˢ : n₁ →ˢ n₂ → suc n₁ →ˢ suc n₂
  ↑ˢ σ = (` zero) ∙ λ α → (σ α) ⋯ᴿ suc

  (` α)         ⋯ˢ σ = σ α
  (∀α t)        ⋯ˢ σ = ∀α (t ⋯ˢ ↑ˢ σ)
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)

  _⨟_ : n₁ →ˢ n₂ → n₂ →ˢ n₃ → n₁ →ˢ n₃
  (σ₁ ⨟ σ₂) α = (σ₁ α) ⋯ˢ σ₂

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
  beta-lift-id            : ↑ᴿ {n₁ = n₁} id ≡ id

  -- beta laws
  beta-id                 : α &ˢ ⟨ id ⟩ ≡ ` α  
  beta-wk                 : α &ˢ ⟨ suc ⟩ ≡ ` suc α 
  beta-ext-zero           : zero  &ˢ (T ∙ σ)   ≡ T                             
  beta-ext-suc            : suc α &ˢ (T ∙ σ)  ≡ α &ˢ σ 
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
  traversal-x             : (` α)         ⋯ˢ σ  ≡ α &ˢ σ
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
  _•_   : Expr Γ (∀α T) →
          (T′ : Type n) → 
          Expr Γ (T [ T′ ]) 

variable
  e e′ e₁ e₂ e₃ : Expr Γ T

_→ᴿ[_]_ : Ctx n₁ → (n₁ →ᴿ n₂) → Ctx n₂ → Set
Γ₁ →ᴿ[ ρ ] Γ₂ = ∀ T → T ∈ Γ₁ → (T ⋯ᴿ ρ) ∈ Γ₂

variable
  Ρ Ρ′ Ρ₁ Ρ₂ Ρ₃ : Γ₁ →ᴿ[ ρ ] Γ₂

Id : Γ →ᴿ[ id ] Γ
Id _ x = x -- no subst right-id

Wk : Γ →ᴿ[ id ] (Γ , T) 
Wk _ = suc

wk* : Γ →ᴿ[ suc ] (Γ ,*) 
wk* _ x = suc* x 

[_,_]_⊚_ : ∀ ρ₁ ρ₂ → (Γ₁ →ᴿ[ ρ₁ ] Γ₂) → (Γ₂ →ᴿ[ ρ₂ ] Γ₃) → (Γ₁ →ᴿ[ ρ₁ ∘ ρ₂ ] Γ₃)
([ _ , _ ] Ρ₁ ⊚ Ρ₂) _ x = Ρ₂ _ (Ρ₁ _ x)

[_]_⇑ᴿ_ : ∀ ρ → (Γ₁ →ᴿ[ ρ ] Γ₂) → ∀ T → (Γ₁ , T) →ᴿ[ ρ ] (Γ₂ , (T ⋯ᴿ ρ))
([ _ ] Ρ ⇑ᴿ _) _ zero    = zero
([ _ ] Ρ ⇑ᴿ _) _ (suc x) = suc (Ρ _ x)

[_]↑ᴿ* : ∀ ρ → (Γ₁ →ᴿ[ ρ ] Γ₂) → (Γ₁ ,*) →ᴿ[ ↑ᴿ ρ ] (Γ₂ ,*)
[ _ ]↑ᴿ* Ρ _ (suc* x) = suc* (Ρ _ x) -- no subst swap ren wk

_⋯ᴿ[_]_ : {T : Type n₁} {Γ₂ : Ctx n₂} → 
  Expr Γ₁ T → (ρ : n₁ →ᴿ n₂) → (Γ₁ →ᴿ[ ρ ] Γ₂) → Expr Γ₂ (T ⋯ᴿ ρ)
(` x)      ⋯ᴿ[ ρ ] Ρ = ` (Ρ _ x)
(λx e)     ⋯ᴿ[ ρ ] Ρ = λx (e ⋯ᴿ[ ρ ] ([ ρ ] Ρ ⇑ᴿ _))
(Λα e)     ⋯ᴿ[ ρ ] Ρ = Λα (e ⋯ᴿ[ ↑ᴿ ρ ] ([ ρ ]↑ᴿ* Ρ))
(e₁ · e₂)  ⋯ᴿ[ ρ ] Ρ = (e₁ ⋯ᴿ[ ρ ] Ρ) · (e₂ ⋯ᴿ[ ρ ] Ρ)
(e • T′)   ⋯ᴿ[ ρ ] Ρ = (e ⋯ᴿ[ ρ ] Ρ) • (T′ ⋯ᴿ ρ) -- no subst swap ren single subst

Weaken : Expr Γ T → Expr (Γ , T′) T
Weaken e = e ⋯ᴿ[ id ] Wk -- no subst right-id
  
weaken* : Expr Γ T → Expr (Γ ,*) (weaken T)
weaken* e = e ⋯ᴿ[ suc ] wk*

_→ˢ[_]_ : Ctx n₁ → (n₁ →ˢ n₂) → Ctx n₂ → Set
Γ₁ →ˢ[ σ ] Γ₂ = ∀ T → T ∈ Γ₁ → Expr Γ₂ (T ⋯ˢ σ) 

variable
  Σ Σ′ Σ₁ Σ₂ Σ₃ : Γ₁ →ᴿ[ ρ ] Γ₂ 

[_]⟪_⟫ : ∀ ρ → Γ₁ →ᴿ[ ρ ] Γ₂ → Γ₁ →ˢ[ ⟨ ρ ⟩ ] Γ₂ 
[ ρ* ]⟪ ρ ⟫ _ x = ` ρ _ x

Idˢ : Γ →ˢ[ ⟨ id ⟩ ] Γ 
Idˢ _ = `_ -- no subst right-idˢ

Wkˢ : ∀ T → Γ →ˢ[ ⟨ id ⟩ ] (Γ , T) 
Wkˢ _ = [ id ]⟪ Wk ⟫

wk*ˢ : Γ →ˢ[ ⟨ suc ⟩ ] (Γ ,*) 
wk*ˢ = [ suc ]⟪ wk* ⟫

[_]_∙_ : ∀ σ → Expr Γ₂ (T ⋯ˢ σ) → Γ₁ →ˢ[ σ ] Γ₂ → (Γ₁ , T) →ˢ[ σ ] Γ₂ 
([ _ ] e ∙ Σ) _ zero     = e
([ _ ] e ∙ Σ) _ (suc x)  = Σ _ x

[_]_∙*_ : ∀ σ T → Γ₁ →ˢ[ σ ] Γ₂ → (Γ₁ ,*) →ˢ[ T ∙ σ ] Γ₂ 
([ _ ] T ∙* Σ) _ (suc* x) = Σ _ x -- no subst swap wk single subst

[_]_⇑ˢ_ : ∀ σ → Γ₁ →ˢ[ σ ] Γ₂ → ∀ T → (Γ₁ , T) →ˢ[ σ ] (Γ₂ , (T ⋯ˢ σ))
[ σ ] Σ ⇑ˢ T = [ σ ] (` zero) ∙ λ _ x → Σ _ x ⋯ᴿ[ id ] Wk -- no subst swap sub wk

[_]↑ˢ* : ∀ σ → (Γ₁ →ˢ[ σ ] Γ₂) → (Γ₁ ,*) →ˢ[ ↑ˢ σ ] (Γ₂ ,*) 
[ _ ]↑ˢ* Σ _ (suc* x) = (Σ _ x) ⋯ᴿ[ suc ] wk*

_⋯ˢ[_]_ : {T : Type n₁} {Γ₂ : Ctx n₂} → 
  Expr Γ₁ T → (σ : n₁ →ˢ n₂) → (Γ₁ →ˢ[ σ ] Γ₂) → Expr Γ₂ (T ⋯ˢ σ)
(` x)      ⋯ˢ[ σ ] Σ = Σ _ x
(λx e)     ⋯ˢ[ σ ] Σ = λx (e ⋯ˢ[ σ ] ([ σ ] Σ ⇑ˢ _))
(Λα e)     ⋯ˢ[ σ ] Σ = Λα (e ⋯ˢ[ ↑ˢ σ ] ([ σ ]↑ˢ* Σ))
(e₁ · e₂)  ⋯ˢ[ σ ] Σ = (e₁ ⋯ˢ[ σ ] Σ) · (e₂ ⋯ˢ[ σ ] Σ)
(e • T′)   ⋯ˢ[ σ ] Σ = (e ⋯ˢ[ σ ] Σ) • (T′ ⋯ˢ σ) -- no subst swap sub single subst

_⨾_ : Γ₁ →ˢ[ σ₁ ] Γ₂ → Γ₂ →ˢ[ σ₂ ] Γ₃ → Γ₁ →ˢ[ σ₁ ⨟ σ₂ ] Γ₃
(Σ₁ ⨾ Σ₂) _ x = (Σ₁ _ x) ⋯ˢ[ _ ] Σ₂

η-Id : [ ⟨ id ⟩ ] (` (zero {T = T} {Γ = Γ})) ∙ (Wkˢ T) ≡ (Idˢ {Γ = Γ , T})
η-Id = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

η*-Id : [ ⟨ id ⟩ ]↑ˢ* (Idˢ {Γ = Γ}) ≡ Idˢ
η*-Id = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Right-Id : ∀ (e : Expr Γ T) → e ⋯ˢ[ ⟨ id ⟩ ] Idˢ ≡ e
Right-Id (` x)      = refl
Right-Id (λx e)     = cong λx_ (trans (cong (e ⋯ˢ[ ⟨ id ⟩ ]_) η-Id) (Right-Id e))
Right-Id (Λα e)     = cong Λα_ (trans (cong (e ⋯ˢ[ ⟨ id ⟩ ]_) η*-Id) (Right-Id e))
Right-Id (e₁ · e₂)  = cong₂ _·_ (Right-Id e₁) (Right-Id e₂)
Right-Id (e • T′)   = cong (_• T′) (Right-Id e)

list-dist-compᴿᴿ : 
  [ ρ₁ , ρ₂ ] ([ ρ₁ ] Ρ₁ ⇑ᴿ T) ⊚ ([ ρ₂ ] Ρ₁ ⇑ᴿ (T ⋯ᴿ ρ₁)) ≡ ([ ρ₁ ∘ ρ₂ ] ([ ρ₁ , ρ₂ ] Ρ₁ ⊚ Ρ₂) ⇑ᴿ {!   !})
list-dist-compᴿᴿ = {!   !} -- ext λ { zero → refl; (suc x) → refl }

{- compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (` x)        = refl
compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (λx e)       = cong λx_ (trans (compositionalityᴿᴿ e) (cong (e ⋯ᴿ_) list-dist-compᴿᴿ))
compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿᴿ e) (cong (e ⋯ᴿ_) list-dist-compᴿᴿ))
compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿᴿ k) (trans (compositionalityᴿᴿ t) (cong (t ⋯ᴿ_) list-dist-compᴿᴿ))
compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿᴿ e₁) (compositionalityᴿᴿ e₂)
compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (e • t)      = cong₂ _•_ (compositionalityᴿᴿ e) (compositionalityᴿᴿ t)
compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)
compositionalityᴿᴿ {ρ₁ = ρ₁} {ρ₂ = ρ₂} *            = refl -}