-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module SystemFo where
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

data Kind : Set where
  ∗ : Kind
  _⇒_ : Kind → Kind → Kind

variable
  J K : Kind

data Ctx* : Set where
  ∅ : Ctx*
  _,*_ : Ctx* → Kind → Ctx*

variable
  Φ Ψ Θ : Ctx*

data _∋*_ : Ctx* → Kind → Set where
  Z  : (Φ ,* K) ∋* K
  S  : Φ ∋* K → (Φ ,* J) ∋* K

data Type Φ : Kind → Set where
  `_   : Φ ∋* K → Type Φ K
  λα_  : Type (Φ ,* J) K → Type Φ (J ⇒ K)
  _·_  : Type Φ (J ⇒ K) → Type Φ J → Type Φ K
  ∀α_  : Type (Φ ,* J) ∗ → Type Φ ∗
  _⇒_  : Type Φ ∗ → Type Φ ∗ → Type Φ ∗

variable
  n n′ n₁ n₂ n₃ : Nat
  α α′ α₁ α₂ α₃ : Φ ∋* K
  T T′ T₁ T₂ T₃ : Type Φ K

-- renamings are functions that with 
-- primitive operations that reduce
-- they already have (nearly) all 
-- definitional equalities we need!
_→ᴿ_ : Ctx* → Ctx* → Set
Φ →ᴿ Ψ = ∀ {K} → Φ ∋* K → Ψ ∋* K

variable
  ρ ρ′ ρ₁ ρ₂ ρ₃ : Φ →ᴿ Ψ

id : Φ →ᴿ Φ
id x = x
--open import Function using (id)

↑ᴿ : Φ →ᴿ Ψ → (Φ ,* J) →ᴿ (Ψ ,* J)
↑ᴿ ρ Z    = Z
↑ᴿ ρ (S x) = S (ρ x) 

_∘_ : Φ →ᴿ Ψ → Ψ →ᴿ Θ → Φ →ᴿ Θ
(ρ₁ ∘ ρ₂) x = ρ₂ (ρ₁ x)


_⋯ᴿ_ : Type Φ K → Φ →ᴿ Ψ → Type Ψ K
(` x) ⋯ᴿ ρ = ` ρ x
(λα T) ⋯ᴿ ρ = λα (T ⋯ᴿ ↑ᴿ ρ)
(T₁ · T₂) ⋯ᴿ ρ = (T₁ ⋯ᴿ ρ) · (T₂ ⋯ᴿ ρ)
(∀α T) ⋯ᴿ ρ = ∀α (T ⋯ᴿ ↑ᴿ ρ)
(T₁ ⇒ T₂) ⋯ᴿ ρ = (T₁ ⋯ᴿ ρ) ⇒ (T₂ ⋯ᴿ ρ)

_→ˢ_ : Ctx* → Ctx* → Set
Φ →ˢ Ψ = ∀ {K} → Φ ∋* K → Type Ψ K

variable
  σ σ₁ σ₂ σ₃ : Φ →ˢ Ψ

-- just helpers! 
-- {-# inline -#} so that agda does not say we rewrite 
-- on reducing symbols..
⟨_⟩ : Φ →ᴿ Ψ → Φ →ˢ Ψ
⟨ ρ ⟩ x = ` ρ x
{-# INLINE ⟨_⟩ #-} 

-- the primitives for substitution must be opaque!
-- otherwise we cannot rewrite on them (even if inlined..)
-- since the violate the rewrite rule rules 
-- ask me for an example for where it breaks if neccessary!
opaque
  -- σₛ­ₚ calculus with first class renamings
  
  -- syntax
  _∙_ : Type Ψ K → Φ →ˢ Ψ → (Φ ,* K) →ˢ Ψ
  (t ∙ σ) Z = t
  (t ∙ σ) (S x) = σ x 

  -- blocking alias for lookup
  _&ˢ_ : Φ ∋* K → Φ →ˢ Ψ → Type Ψ K
  x &ˢ σ = σ x 
  
  _⋯ˢ_ : Type Φ K → Φ →ˢ Ψ → Type Ψ K

  ↑ˢ : Φ →ˢ Ψ → (Φ ,* J) →ˢ (Ψ ,* J)
  ↑ˢ σ = (` Z) ∙ λ x → (σ x) ⋯ᴿ S

  (` x) ⋯ˢ σ = σ x
  (λα T) ⋯ˢ σ = λα (T ⋯ˢ ↑ˢ σ)
  (T₁ · T₂) ⋯ˢ σ = (T₁ ⋯ˢ σ) · (T₂ ⋯ˢ σ)
  (∀α T) ⋯ˢ σ = ∀α (T ⋯ˢ ↑ˢ σ)
  (T₁ ⇒ T₂) ⋯ˢ σ = (T₁ ⋯ˢ σ) ⇒ (T₂ ⋯ˢ σ)

  _⨟_ : Φ →ˢ Ψ → Ψ →ˢ Θ → Φ →ˢ Θ
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

postulate
  -- first-class renamings 
  beta-lift-id            : ↑ᴿ {Φ = Φ}{J = J} id {K} ≡ id

  -- beta laws
  beta-id                 : α &ˢ ⟨ id ⟩ ≡ ` α  
  beta-wk                 : α &ˢ ⟨ S {J = J} ⟩ ≡ ` S α 
  beta-ext-zero           : Z  &ˢ (T ∙ σ)   ≡ T                             
  beta-ext-suc            : S α &ˢ (T ∙ σ)  ≡ α &ˢ σ 
  beta-lift               : ↑ˢ {Φ}{Ψ}{J} σ {K}           ≡ (` Z) ∙ (σ ⨟ ⟨ S ⟩)

  -- interaction laws
  associativity           : ((σ₁ ⨟ σ₂) ⨟ σ₃) {K}                        ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)                     
  distributivity          : ((T ∙ σ₁) ⨟ σ₂) {K}                         ≡ ((T ⋯ˢ σ₂) ∙ (σ₁ ⨟ σ₂)) 
  distributivityᴿ         : ((T ∙ σ₁) ⨟ ⟨ ρ₂ ⟩) {K}                     ≡ ((T ⋯ᴿ ρ₂) ∙ (σ₁ ⨟ ⟨ ρ₂ ⟩)) 
  interact                : (⟨ S ⟩ ⨟ (T ∙ σ)) {K}                     ≡ σ                                        
  comp-idᵣ                : (σ ⨟ ⟨ id ⟩) {K}                             ≡ σ                                               
  comp-idₗ                : (⟨ id ⟩ ⨟ σ) {K}                             ≡ σ                                               
  η-id                    : ((` Z) ∙ ⟨ S ⟩)  ≡ ⟨ id {Φ ,* J} ⟩ {K}
  η-lawˢ                  : ((Z &ˢ σ) ∙ (⟨ S ⟩ ⨟ σ)) {K}       ≡ σ
  η-lawᴿ                  : ((` ρ Z) ∙ (⟨ S ⟩ ⨟ ⟨ ρ ⟩)) {K}   ≡ ⟨ ρ ⟩

  -- monad laws
  right-id                : ∀ (T : Type Φ K) → T ⋯ᴿ id                   ≡ T   
  compositionalityᴿˢ      : ∀ (T : Type Φ K) → (T ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)                    
  compositionalityᴿᴿ      : ∀ (T : Type Φ K) → (T ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ T ⋯ᴿ (ρ₁ ∘ ρ₂)                     
  compositionalityˢᴿ      : ∀ (T : Type Φ K) → (T ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ T ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)                         
  compositionalityˢˢ      : ∀ (T : Type Φ K) → (T ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (σ₁ ⨟ σ₂)

  -- traversal laws
  traversal-x             : (` α)         ⋯ˢ σ  ≡ α &ˢ σ
  traversal-λ             : (λα T)        ⋯ˢ σ  ≡ λα (T ⋯ˢ (↑ˢ σ))
  traversal-·             : (T₁ · T₂)     ⋯ˢ σ  ≡ (T₁ ⋯ˢ σ) · (T₂ ⋯ˢ σ)
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

weaken : Type Φ K → Type (Φ ,* J) K
weaken t = t ⋯ᴿ S

_[_] : Type (Φ ,* J) K → Type Φ J → Type Φ K
t [ t′ ] = t ⋯ˢ (t′ ∙ ⟨ id ⟩)

-- expressions

-- data Ctx : Nat → Set where
--   ∅    : Ctx zero
--   _,_  : Ctx n → Type n → Ctx n          
--   _,*  : Ctx n → Ctx (suc n) 

-- variable
--   Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx n

-- data _∈_ : Type n → Ctx n → Set where
--   zero  : T ∈ (Γ , T)
--   suc   : T ∈ Γ → T ∈ (Γ , T′)
--   suc*  : T ∈ Γ → (weaken T) ∈ (Γ ,*)

-- data Expr : Ctx n → Type n → Set where
--   `_    : T ∈ Γ → 
--           Expr Γ T
--   λx_   : Expr (Γ , T₁) T₂ → 
--           Expr Γ (T₁ ⇒ T₂) 
--   Λα_   : Expr (Γ ,*) T → 
--           Expr Γ (∀α T)
--   _·_   : Expr Γ (T₁ ⇒ T₂) → 
--           Expr Γ T₁ → 
--           Expr Γ T₂
--   _•_   : Expr Γ (∀α T) →
--           (T' : Type n) → 
--           Expr Γ (T [ T' ]) 

-- _→ᴿ[_]_ : Ctx n₁ → (n₁ →ᴿ n₂) → Ctx n₂ → Set
-- Γ₁ →ᴿ[ ρ ] Γ₂ = ∀ T → T ∈ Γ₁ → (T ⋯ᴿ ρ) ∈ Γ₂

-- _⊚_ : (Γ₁ →ᴿ[ ρ₁ ] Γ₂) → (Γ₂ →ᴿ[ ρ₂ ] Γ₃) → (Γ₁ →ᴿ[ ρ₁ ∘ ρ₂ ] Γ₃)
-- (ρ₁ ⊚ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

-- Wk : Γ →ᴿ[ id ] (Γ , T) 
-- Wk _ = suc

-- wk* : Γ →ᴿ[ suc ] (Γ ,*) 
-- wk* _ x = suc* x 

-- _⇑ᴿ_ : (Γ₁ →ᴿ[ ρ ] Γ₂) → ∀ T → (Γ₁ , T) →ᴿ[ ρ ] (Γ₂ , (T ⋯ᴿ ρ))
-- (ρ ⇑ᴿ _) _ zero    = zero
-- (ρ ⇑ᴿ _) _ (suc x) = suc (ρ _ x)

-- ↑ᴿ* : (Γ₁ →ᴿ[ ρ ] Γ₂) → (Γ₁ ,*) →ᴿ[ ↑ᴿ ρ ] (Γ₂ ,*)
-- ↑ᴿ* ρ _ (suc* x) = suc* (ρ _ x)

-- _⋯ᴿ[_]_ : {T : Type n₁} {Γ₂ : Ctx n₂} → 
--   Expr Γ₁ T → (ρ* : n₁ →ᴿ n₂) → (Γ₁ →ᴿ[ ρ* ] Γ₂) → Expr Γ₂ (T ⋯ᴿ ρ*)
-- (` x)      ⋯ᴿ[ ρ* ] ρ = ` (ρ _ x)
-- (λx e)     ⋯ᴿ[ ρ* ] ρ = λx (e ⋯ᴿ[ ρ* ] (ρ ⇑ᴿ _))
-- (Λα e)     ⋯ᴿ[ ρ* ] ρ = Λα (e ⋯ᴿ[ ↑ᴿ ρ* ] (↑ᴿ* ρ))
-- (e₁ · e₂)  ⋯ᴿ[ ρ* ] ρ = (e₁ ⋯ᴿ[ ρ* ] ρ) · (e₂ ⋯ᴿ[ ρ* ] ρ)
-- (e • t′)   ⋯ᴿ[ ρ* ] ρ = (e ⋯ᴿ[ ρ* ] ρ) • (t′ ⋯ᴿ ρ*)

-- Weaken : Expr Γ T → Expr (Γ , T′) T
-- Weaken e = e ⋯ᴿ[ id ] Wk
  
-- weaken* : Expr Γ T → Expr (Γ ,*) (weaken T)
-- weaken* e = e ⋯ᴿ[ suc ] wk*

