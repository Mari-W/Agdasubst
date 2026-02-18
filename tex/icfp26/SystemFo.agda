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
  λα  : Type (Φ ,* J) K → Type Φ (J ⇒ K)
  -- _$_  : Type Φ (J ⇒ K) → Type Φ J → Type Φ K
  ∀α  : Type (Φ ,* J) ∗ → Type Φ ∗
  _⇒_  : Type Φ ∗ → Type Φ ∗ → Type Φ ∗

postulate
  _$_  : Type Φ (J ⇒ K) → Type Φ J → Type Φ K

variable
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
-- (T₁ $ T₂) ⋯ᴿ ρ = (T₁ ⋯ᴿ ρ) $ (T₂ ⋯ᴿ ρ)
(∀α T) ⋯ᴿ ρ = ∀α (T ⋯ᴿ ↑ᴿ ρ)
(T₁ ⇒ T₂) ⋯ᴿ ρ = (T₁ ⋯ᴿ ρ) ⇒ (T₂ ⋯ᴿ ρ)

postulate
  traverseᴿ-$ : (T₁ $ T₂) ⋯ᴿ ρ ≡ (T₁ ⋯ᴿ ρ) $ (T₂ ⋯ᴿ ρ)

{-# REWRITE traverseᴿ-$ #-}

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
  -- (T₁ $ T₂) ⋯ˢ σ = (T₁ ⋯ˢ σ) $ (T₂ ⋯ˢ σ)
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
  traversal-$             : (T₁ $ T₂)     ⋯ˢ σ  ≡ (T₁ ⋯ˢ σ) $ (T₂ ⋯ˢ σ)
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
  traversal-λ
  traversal-$

  coincidence
  coincidence-fold
#-}

weaken* : Type Φ K → Type (Φ ,* J) K
weaken* t = t ⋯ᴿ S

_[_]* : Type (Φ ,* J) K → Type Φ J → Type Φ K
t [ t′ ]* = t ⋯ˢ (t′ ∙ ⟨ id ⟩)

-- type equality

postulate
  β≡* : (λα T₁) $ T₂ ≡ T₁ [ T₂ ]*
  
-- term contexts

data Ctx : Ctx* → Set where
  ∅    : Ctx ∅
  _,*  : Ctx Φ → Ctx (Φ ,* J) 
  _,_  : Ctx Φ → Type Φ ∗ → Ctx Φ

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx Φ
  Δ Δ′ : Ctx Ψ

-- term variables

data _∋_ : Ctx Φ → Type Φ ∗ → Set where
  Z   : (Γ , T) ∋ T
  S   : Γ ∋ T → (Γ , T′) ∋ T
  S*  : Γ ∋ T → (Γ ,*) ∋ weaken* {J = J} T

data Expr {Φ} Γ : Type Φ ∗ → Set where
  `_    : Γ ∋ T → 
          Expr Γ T
  λx   : Expr (Γ , T₁) T₂ → 
          Expr Γ (T₁ ⇒ T₂) 
  Λα   : Expr (Γ ,*) T → 
          Expr Γ (∀α T)
  _·_   : Expr Γ (T₁ ⇒ T₂) → 
          Expr Γ T₁ → 
          Expr Γ T₂
  _•_   : Expr Γ (∀α T) →
          (T′ : Type Φ K) → 
          Expr Γ (T [ T′ ]*) 

variable
  e e′ e₁ e₂ e₃ e₁′ e₂′ e₃′ : Expr Γ T

-- term renamings

_→ᴿ[_]_ : Ctx Φ → (Φ →ᴿ Ψ) → Ctx Ψ → Set
Γ →ᴿ[ ρ ] Δ = ∀ T → Γ ∋ T  → Δ ∋ (T ⋯ᴿ ρ)

_⊚ᴿ_ : (Γ₁ →ᴿ[ ρ₁ ] Γ₂) → (Γ₂ →ᴿ[ ρ₂ ] Γ₃) → (Γ₁ →ᴿ[ ρ₁ ∘ ρ₂ ] Γ₃)
(ρ₁ ⊚ᴿ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

Wk : Γ →ᴿ[ id ] (Γ , T) 
Wk _ = S

wk* : Γ →ᴿ[ S {J = J} ] (Γ ,*) 
wk* _ x = S* x 

_⇑ᴿ_ : (Γ₁ →ᴿ[ ρ ] Γ₂) → ∀ T → (Γ₁ , T) →ᴿ[ ρ ] (Γ₂ , (T ⋯ᴿ ρ))
(ρ ⇑ᴿ _) _ Z    = Z
(ρ ⇑ᴿ _) _ (S x) = S (ρ _ x)

↑ᴿ* : (Γ₁ →ᴿ[ ρ ] Γ₂) → (Γ₁ ,*) →ᴿ[ ↑ᴿ {J = J} ρ ] (Γ₂ ,*)
↑ᴿ* ρ _ (S* x) = S* (ρ _ x)

_⋯ᴿ[_]_ : {T : Type Φ ∗} {Γ₂ : Ctx Ψ} → 
  Expr Γ₁ T → (ρ* : Φ →ᴿ Ψ) → (Γ₁ →ᴿ[ ρ* ] Γ₂) → Expr Γ₂ (T ⋯ᴿ ρ*)
(` x)      ⋯ᴿ[ ρ* ] ρ = ` (ρ _ x)
(λx e)     ⋯ᴿ[ ρ* ] ρ = λx (e ⋯ᴿ[ ρ* ] (ρ ⇑ᴿ _))
(Λα e)     ⋯ᴿ[ ρ* ] ρ = Λα (e ⋯ᴿ[ ↑ᴿ ρ* ] (↑ᴿ* ρ))
(e₁ · e₂)  ⋯ᴿ[ ρ* ] ρ = (e₁ ⋯ᴿ[ ρ* ] ρ) · (e₂ ⋯ᴿ[ ρ* ] ρ)
(e • t′)   ⋯ᴿ[ ρ* ] ρ = (e ⋯ᴿ[ ρ* ] ρ) • (t′ ⋯ᴿ ρ*)

Weaken : Expr Γ T → Expr (Γ , T′) T
Weaken e = e ⋯ᴿ[ id ] Wk
  
weaken** : Expr Γ T → Expr (Γ ,*) (weaken* {J = J} T)
weaken** e = e ⋯ᴿ[ S ] wk*

-- term substitution

_→ˢ[_]_ : Ctx Φ → (Φ →ˢ Ψ) → Ctx Ψ → Set
Γ →ˢ[ σ* ] Δ = ∀ T → Γ ∋ T  → Expr Δ (T ⋯ˢ σ*)

idˢ : Γ →ˢ[ ⟨ id ⟩ ] Γ
idˢ _ x = ` x

⇑ˢ    : {σ* : Φ →ˢ Ψ} → Γ₁ →ˢ[ σ* ] Γ₂ → (Γ₁ , T) →ˢ[ σ* ] (Γ₂ , (T ⋯ˢ σ*))
⇑ˢ σ T Z = ` Z
⇑ˢ σ T (S x) = Weaken (σ _ x)

⇑ˢ*   : {σ* : Φ →ˢ Ψ} → (σ : Γ₁ →ˢ[ σ* ] Γ₂) → (Γ₁ ,*) →ˢ[ ↑ˢ {J = J} σ* ] (Γ₂ ,*)
⇑ˢ* σ T (S* x) = weaken** (σ _ x)

_⋯s[_]_ : Expr Γ T → (σ* : Φ →ˢ Ψ) → Γ →ˢ[ σ* ] Δ → Expr Δ (T ⋯ˢ σ*)
(` x)      ⋯s[ σ* ] σ  = σ _ x
(λx e)     ⋯s[ σ* ] σ  = λx (e ⋯s[ σ* ] ⇑ˢ {σ* = σ*} σ)
(Λα e)     ⋯s[ σ* ] σ  = Λα (e ⋯s[ ↑ˢ σ* ] ⇑ˢ* {σ* = σ*} σ)
(e₁ · e₂)  ⋯s[ σ* ] σ  = (e₁ ⋯s[ σ* ] σ) · (e₂ ⋯s[ σ* ] σ)
(e • T′)   ⋯s[ σ* ] σ  = (e ⋯s[ σ* ] σ) • (T′ ⋯ˢ σ*)

_[_] : Expr (Γ , T′) T → Expr Γ T′ → Expr Γ T
e₁ [ e₂ ] = e₁ ⋯s[ ⟨ id ⟩ ] σ₀ e₂
  where σ₀ : Expr Γ T′ → (Γ , T′) →ˢ[ ⟨ id ⟩ ] Γ
        σ₀ e T Z = e
        σ₀ e T (S x) = ` x

extˢ : {σ* : Φ →ˢ Ψ}{T′ : Type Ψ J} → (Γ₁ →ˢ[ σ* ] Γ₂) → ((Γ₁ ,*) →ˢ[ T′ ∙ σ* ] Γ₂)
extˢ σ T (S* x) = σ _ x

_[_]** : {Γ : Ctx Φ} → Expr (Γ ,*) T → (T′ : Type Φ J) → Expr Γ (T [ T′ ]*)
e [ T′ ]** = e ⋯s[ T′ ∙ ⟨ id ⟩ ] (extˢ {T′ = T′}) idˢ

-- term reduction

data _⟶_ {Γ : Ctx Φ} : ∀ {T} → Expr Γ T → Expr Γ T → Set where
  β-λ : ((λx e₁) · e₂) ⟶ (e₁ [ e₂ ])
  β-Λ : ∀ {T′ : Type Φ J} → -- ∀ {T : Type (Φ ,* J) ∗} → -- {e : Expr (Γ ,*) {!!}} →
       ((Λα e) • T′) ⟶ (e [ T′ ]**)

  ξ-· : e₁ ⟶ e₁′ → (e₁ · e₂) ⟶ (e₁′ · e₂)
  ξ-Λ : e ⟶ e′ → (Λα e) ⟶ (Λα e′)
  ξ-• : e ⟶ e′ → (e • T) ⟶ (e′ • T)

-- progress

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; contradiction)

data Value {Γ : Ctx Φ} : ∀ {T : Type Φ ∗} → Expr Γ T → Set where
  λx : (e : Expr (Γ , T₁) T₂) → Value (λx e)
  Λα : Value e → Value (Λα e)

data Progress {Γ : Ctx Φ} {T : Type Φ ∗} : Expr Γ T → Set where
  done : {e : Expr Γ T} → (v : Value e) → Progress e
  step : (e⟶e′ : e ⟶ e′) → Progress e

data NoVar : Ctx Φ → Set where
  ∅ : NoVar ∅
  _,* : NoVar Γ → NoVar {Φ ,* J} (Γ ,*)

noVar : NoVar Γ → ¬ (Γ ∋ T)
noVar (nv ,*) (S* x) = noVar nv x

progress : NoVar Γ → (e : Expr Γ T) → Progress e
progress nv (` x) = ⊥-elim (noVar nv x)
progress nv (λx e) = done (λx e)
progress nv (Λα e)
  with progress (nv ,*) e
... | done v = done (Λα v)
... | step e⟶e′ = step (ξ-Λ e⟶e′)
progress nv (e · e′)
  with progress nv e
... | step e⟶e′ = step (ξ-· e⟶e′)
... | done (λx e₁) = step β-λ
progress nv (e • T′)
  with progress nv e
... | step e⟶e′ = step (ξ-• e⟶e′)
... | done (Λα v) = step β-Λ

-- composition of term substitutions

_⊚ˢ_ : (Γ₁ →ˢ[ σ₁ ] Γ₂) → (Γ₂ →ˢ[ σ₂ ] Γ₃) → (Γ₁ →ˢ[ σ₁ ⨟ σ₂ ] Γ₃)
(σ₁ ⊚ˢ σ₂) _ x = σ₁ _ x ⋯s[ _ ] σ₂

-- execution

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; ∃-syntax; _,_; _×_)

data _⟶*_ {Γ : Ctx Φ} : ∀ {T} → Expr Γ T → Expr Γ T → Set where
  ⟶refl   : e ⟶* e
  ⟶trans  : e₁ ⟶ e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃

run : {T : Type ∅ ∗} → ℕ → (e : Expr ∅ T) → ∃[ e′ ] e ⟶* e′ × Maybe (Value e′)
run zero e = e , ⟶refl , nothing
run (suc n) e
  with progress ∅ e
... | done v = e , ⟶refl , just v
... | step {e′ = e′} e⟶e′
  with run n e′
... | e″ , e′⟶e″ , mve″ = e″ , ⟶trans e⟶e′ e′⟶e″ , mve″

-- examples

-- Church numerals

-- ∀ α (α→α) → α→α

ℕᶜ : Type ∅ ∗
ℕᶜ = ∀α (((` Z) ⇒ (` Z)) ⇒ ((` Z) ⇒ (` Z)))

zeroᶜ : Expr ∅ ℕᶜ
zeroᶜ = Λα (λx (λx (` Z)))

oneᶜ : Expr ∅ ℕᶜ
oneᶜ = Λα (λx (λx ((` S Z) · (` Z))))

succᶜ : Expr ∅ (ℕᶜ ⇒ ℕᶜ)
succᶜ = λx (Λα (λx (λx ((` S Z) · ((((` (S (S (S* Z)))) • (` Z)) · (` S Z)) · (` Z))))))

twoᶜ : Expr ∅ ℕᶜ
twoᶜ = succᶜ · (succᶜ · zeroᶜ)

fourᶜ : Expr ∅ ℕᶜ
fourᶜ = succᶜ · (succᶜ · (succᶜ · (succᶜ · zeroᶜ)))

two+twoᶜ : Expr ∅ ℕᶜ
two+twoᶜ = ((twoᶜ • ℕᶜ) · succᶜ)  · twoᶜ

