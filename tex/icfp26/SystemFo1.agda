-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
module SystemFo1 where
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

--! FOKind
data Kind : Set where
  ∗ : Kind
  _⇒_ : Kind → Kind → Kind

variable
  I J K : Kind

--! FOTypeCtx
data Ctx* : Set where
  ∅ : Ctx*
  _▷*_ : Ctx* → Kind → Ctx*

variable
  Φ Ψ Θ : Ctx*

--! FOTypeVar
data _∋*_ : Ctx* → Kind → Set where
  Z  : (Φ ▷* K) ∋* K
  S  : Φ ∋* K → (Φ ▷* J) ∋* K

--! FOType
data Type Φ : Kind → Set where
  `_   : Φ ∋* K → Type Φ K
  λα  : Type (Φ ▷* J) K → Type Φ (J ⇒ K)
  -- _$_  : Type Φ (J ⇒ K) → Type Φ J → Type Φ K
  ∀α  : Type (Φ ▷* J) ∗ → Type Φ ∗
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
Φ →ᴿ Ψ = ∀ K → Φ ∋* K → Ψ ∋* K

variable
  ρ ρ′ ρ₁ ρ₂ ρ₃ : Φ →ᴿ Ψ

opaque
  wkᴿ : Φ →ᴿ (Φ ▷* J)
  wkᴿ _ = S

  idᴿ : Φ →ᴿ Φ
  idᴿ _ x = x

  _∙ᴿ_ :  Ψ ∋* J → Φ →ᴿ Ψ → (Φ ▷* J) →ᴿ Ψ
  (α ∙ᴿ ρ) _ Z = α
  (_ ∙ᴿ ρ) _ (S α) = ρ _ α

  _&ᴿ_ : Φ ∋* J → Φ →ᴿ Ψ → Ψ ∋* J
  α &ᴿ ρ = ρ _ α
  
  _∘_ : Φ →ᴿ Ψ → Ψ →ᴿ Θ → Φ →ᴿ Θ
  (ρ₁ ∘ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_↑ᴿ : Φ →ᴿ Ψ → (Φ ▷* J) →ᴿ (Ψ ▷* J)
_↑ᴿ ρ = Z ∙ᴿ (ρ ∘ wkᴿ)

--! FORenTraversal
_⋯ᴿ_ : Type Φ K → Φ →ᴿ Ψ → Type Ψ K
(` x) ⋯ᴿ ρ = ` ρ _ x
(λα T) ⋯ᴿ ρ = λα (T ⋯ᴿ (ρ ↑ᴿ))
-- (T₁ $ T₂) ⋯ᴿ ρ = (T₁ ⋯ᴿ ρ) $ (T₂ ⋯ᴿ ρ)
(∀α T) ⋯ᴿ ρ = ∀α (T ⋯ᴿ (ρ ↑ᴿ))
(T₁ ⇒ T₂) ⋯ᴿ ρ = (T₁ ⋯ᴿ ρ) ⇒ (T₂ ⋯ᴿ ρ)
postulate
  traverseᴿ-$ : (T₁ $ T₂) ⋯ᴿ ρ ≡ (T₁ ⋯ᴿ ρ) $ (T₂ ⋯ᴿ ρ)
{-# REWRITE traverseᴿ-$ #-}

_→ˢ_ : Ctx* → Ctx* → Set
Φ →ˢ Ψ = ∀ K → Φ ∋* K → Type Ψ K

variable
  σ σ₁ σ₂ σ₃ : Φ →ˢ Ψ


opaque
  ⟨_⟩ : Φ →ᴿ Ψ → Φ →ˢ Ψ
  ⟨ ρ ⟩ _ x = ` (ρ _ x)
  
  -- syntax
  _∙ˢ_ : Type Ψ K → Φ →ˢ Ψ → (Φ ▷* K) →ˢ Ψ
  (t ∙ˢ σ) _ Z = t
  (t ∙ˢ σ) _ (S x) = σ _ x 

  -- blocking alias for lookup
  _&ˢ_ : Φ ∋* K → Φ →ˢ Ψ → Type Ψ K
  x &ˢ σ = σ _ x 

  _↑ˢ : Φ →ˢ Ψ → (Φ ▷* J) →ˢ (Ψ ▷* J)
  _↑ˢ σ = (` Z) ∙ˢ λ _ x → (σ _ x) ⋯ᴿ wkᴿ
  
_⋯ˢ_ : Type Φ K → Φ →ˢ Ψ → Type Ψ K
(` x) ⋯ˢ σ = x &ˢ σ
(λα T) ⋯ˢ σ = λα (T ⋯ˢ (σ ↑ˢ))
-- (T₁ $ T₂) ⋯ˢ σ = (T₁ ⋯ˢ σ) $ (T₂ ⋯ˢ σ)
(∀α T) ⋯ˢ σ = ∀α (T ⋯ˢ (σ ↑ˢ))
(T₁ ⇒ T₂) ⋯ˢ σ = (T₁ ⋯ˢ σ) ⇒ (T₂ ⋯ˢ σ)

opaque  
  _⨟_ : Φ →ˢ Ψ → Ψ →ˢ Θ → Φ →ˢ Θ
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂


opaque
  unfolding wkᴿ ⟨_⟩ _⨟_
  `beta-ext-zero           : Z  &ᴿ (α ∙ᴿ ρ)        ≡ α
  `beta-ext-suc            : S α &ᴿ (α′ ∙ᴿ ρ)       ≡ α &ᴿ ρ
  `beta-id                 : α &ᴿ idᴿ                 ≡ α
  `beta-wk                 : α &ᴿ (wkᴿ {J = J})                 ≡ S α
  `beta-comp               : α &ᴿ (ρ₁ ∘ ρ₂)           ≡ (α &ᴿ ρ₁) &ᴿ ρ₂

  `associativity           : (ρ₁ ∘ ρ₂) ∘ ρ₃           ≡ ρ₁ ∘ (ρ₂ ∘ ρ₃)
  `distributivity          : (α ∙ᴿ ρ₁) ∘ ρ₂           ≡ (α &ᴿ ρ₂) ∙ᴿ (ρ₁ ∘ ρ₂)
  `interact                : (wkᴿ {J = J}) ∘ (α ∙ᴿ ρ)            ≡ ρ
  `comp-idᵣ                : ρ ∘ idᴿ                  ≡ ρ
  `comp-idₗ                : idᴿ ∘ ρ                  ≡ ρ
  `η-id                    : Z {Φ} ∙ᴿ (wkᴿ {J = J})           ≡ idᴿ
  `η-law                   : (Z &ᴿ ρ) ∙ᴿ ((wkᴿ {J = J}) ∘ ρ)  ≡ ρ

  beta-ext-zero           : Z  &ˢ (T ∙ˢ σ)                ≡ T
  beta-ext-suc            : S α &ˢ (T ∙ˢ σ)                ≡ α &ˢ σ
  beta-rename             : α &ˢ ⟨ ρ ⟩                       ≡ ` (α  &ᴿ ρ)
  beta-comp               : α &ˢ (σ₁ ⨟ σ₂)                   ≡ (α &ˢ σ₁) ⋯ˢ σ₂
  beta-lift               : σ ↑ˢ                             ≡ (` Z) ∙ˢ (σ ⨟ ⟨ (wkᴿ {J = J}) ⟩)

  associativity           : (σ₁ ⨟ σ₂) ⨟ σ₃                   ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)
  distributivity          : (T ∙ˢ σ₁) ⨟ σ₂                   ≡ (T ⋯ˢ σ₂) ∙ˢ (σ₁ ⨟ σ₂)
  interact                : ⟨ (wkᴿ {J = J}) ⟩ ⨟ (T ∙ˢ σ)                ≡ σ
  comp-idᵣ                : σ ⨟ ⟨ idᴿ ⟩                      ≡ σ
  comp-idₗ                : ⟨ idᴿ ⟩ ⨟ σ                      ≡ σ
  η-id                    : (` Z {Φ}) ∙ˢ ⟨ (wkᴿ {J = J}) ⟩           ≡ ⟨ idᴿ ⟩
  η-law                   : (Z &ˢ σ) ∙ˢ (⟨ (wkᴿ {J = J}) ⟩ ⨟ σ)      ≡ σ

  identityᵣ      : T ⋯ᴿ idᴿ          ≡ T
  composeᴿˢ      : (T ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)
  composeᴿᴿ      : (T ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ T ⋯ᴿ (ρ₁ ∘ ρ₂)
  composeˢᴿ      : (T ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ T ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)
  composeˢˢ      : (T ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (σ₁ ⨟ σ₂)

  coincidence              : T ⋯ˢ ⟨ ρ ⟩                                 ≡ T  ⋯ᴿ ρ
  coincidence-comp         : ⟨ ρ₁ ⟩ ⨟ ⟨ ρ₂ ⟩                            ≡ ⟨ ρ₁ ∘ ρ₂ ⟩

  coincidence-lemma₁  : (⟨ ρ ↑ᴿ ⟩ ⨟ ((T′ ⋯ᴿ ρ) ∙ˢ ⟨ idᴿ ⟩)) ≡ ((T′ ⋯ᴿ ρ) ∙ˢ ⟨ ρ ⟩)
  coincidence-lemma₁ = fun-ext λ _ → fun-ext λ { Z → refl; (S x) → refl }
  coincidence-lemma₂ : ((_↑ᴿ {Φ = Φ} wkᴿ ) ∗ Z &ˢ ((` Z) ∙ˢ ⟨ idᴿ ⟩)) ≡ (` Z)
  coincidence-lemma₂ = refl
  
  
  
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
  beta-rename

  associativity
  distributivity
  interact
  comp-idᵣ
  comp-idₗ
  η-id
  η-law

  `associativity
  `distributivity
  `interact
  `comp-idᵣ
  `comp-idₗ
  `η-id
  `η-law

  identityᵣ
  composeᴿˢ
  composeᴿᴿ
  composeˢᴿ
  composeˢˢ

  coincidence
  coincidence-comp
  coincidence-lemma₁
  coincidence-lemma₂
#-}

weaken* : Type Φ K → Type (Φ ▷* J) K
weaken* t = t ⋯ᴿ wkᴿ

_[_]* : Type (Φ ▷* J) K → Type Φ J → Type Φ K
t [ t′ ]* = t ⋯ˢ (t′ ∙ˢ ⟨ idᴿ ⟩)

-- type equality

--! FOTypeBeta
postulate
  β≡* : (λα T₁) $ T₂ ≡ T₁ [ T₂ ]*
  
-- term contexts

data Ctx : Ctx* → Set where
  ∅    : Ctx ∅
  _▷*  : Ctx Φ → Ctx (Φ ▷* J) 
  _▷_  : Ctx Φ → Type Φ ∗ → Ctx Φ

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx Φ
  Δ Δ′ : Ctx Ψ

-- term variables

data _∋_ : Ctx Φ → Type Φ ∗ → Set where
  Z   : (Γ ▷ T) ∋ T
  S   : Γ ∋ T → (Γ ▷ T′) ∋ T
  S*  : Γ ∋ T → (Γ ▷*) ∋ weaken* {J = J} T

data Expr {Φ} Γ : Type Φ ∗ → Set where
  `_    : Γ ∋ T → 
          Expr Γ T
  λx   : Expr (Γ ▷ T₁) T₂ → 
          Expr Γ (T₁ ⇒ T₂) 
  Λα   : Expr (Γ ▷*) T → 
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

Wk : Γ →ᴿ[ idᴿ ] (Γ ▷ T) 
Wk _ = S

wk* : Γ →ᴿ[ wkᴿ {J = J} ] (Γ ▷*) 
wk* _ x = S* x 

_⇑ᴿ_ : (Γ₁ →ᴿ[ ρ ] Γ₂) → ∀ T → (Γ₁ ▷ T) →ᴿ[ ρ ] (Γ₂ ▷ (T ⋯ᴿ ρ))
(ρ ⇑ᴿ _) _ Z    = Z
(ρ ⇑ᴿ _) _ (S x) = S (ρ _ x)

↑ᴿ* : (Γ₁ →ᴿ[ ρ ] Γ₂) → (Γ₁ ▷*) →ᴿ[ _↑ᴿ {J = J} ρ  ] (Γ₂ ▷*)
↑ᴿ* ρ _ (S* x) = S* (ρ _ x)

_⋯ᴿ[_]_ : {T : Type Φ ∗} {Γ₂ : Ctx Ψ} → 
  Expr Γ₁ T → (ρ* : Φ →ᴿ Ψ) → (Γ₁ →ᴿ[ ρ* ] Γ₂) → Expr Γ₂ (T ⋯ᴿ ρ*)
(` x)      ⋯ᴿ[ ρ* ] ρ = ` (ρ _ x)
(λx e)     ⋯ᴿ[ ρ* ] ρ = λx (e ⋯ᴿ[ ρ* ] (ρ ⇑ᴿ _))
(Λα e)     ⋯ᴿ[ ρ* ] ρ = Λα (e ⋯ᴿ[ ρ* ↑ᴿ ] (↑ᴿ* ρ))
(e₁ · e₂)  ⋯ᴿ[ ρ* ] ρ = (e₁ ⋯ᴿ[ ρ* ] ρ) · (e₂ ⋯ᴿ[ ρ* ] ρ)
(e • t′)   ⋯ᴿ[ ρ* ] ρ = (e ⋯ᴿ[ ρ* ] ρ) • (t′ ⋯ᴿ ρ*)

Weaken : Expr Γ T → Expr (Γ ▷ T′) T
Weaken e = e ⋯ᴿ[ idᴿ ] Wk
  
weaken** : Expr Γ T → Expr (Γ ▷*) (weaken* {J = J} T)
weaken** e = e ⋯ᴿ[ wkᴿ ] wk*

-- term substitution

_→ˢ[_]_ : Ctx Φ → (Φ →ˢ Ψ) → Ctx Ψ → Set
Γ →ˢ[ σ* ] Δ = ∀ T → Γ ∋ T  → Expr Δ (T ⋯ˢ σ*)

idˢ : Γ →ˢ[ ⟨ idᴿ ⟩ ] Γ
idˢ _ x = ` x

⇑ˢ    : {σ* : Φ →ˢ Ψ} → Γ₁ →ˢ[ σ* ] Γ₂ → (Γ₁ ▷ T) →ˢ[ σ* ] (Γ₂ ▷ (T ⋯ˢ σ*))
⇑ˢ σ T Z = ` Z
⇑ˢ σ T (S x) = Weaken (σ _ x)

⇑ˢ*   : {σ* : Φ →ˢ Ψ} → (σ : Γ₁ →ˢ[ σ* ] Γ₂) → (Γ₁ ▷*) →ˢ[ _↑ˢ {J = J} σ* ] (Γ₂ ▷*)
⇑ˢ* σ T (S* x) = weaken** (σ _ x)

_⋯s[_]_ : Expr Γ T → (σ* : Φ →ˢ Ψ) → Γ →ˢ[ σ* ] Δ → Expr Δ (T ⋯ˢ σ*)
(` x)      ⋯s[ σ* ] σ  = σ _ x
(λx e)     ⋯s[ σ* ] σ  = λx (e ⋯s[ σ* ] ⇑ˢ {σ* = σ*} σ)
(Λα e)     ⋯s[ σ* ] σ  = Λα (e ⋯s[ _↑ˢ σ* ] ⇑ˢ* {σ* = σ*} σ)
(e₁ · e₂)  ⋯s[ σ* ] σ  = (e₁ ⋯s[ σ* ] σ) · (e₂ ⋯s[ σ* ] σ)
(e • T′)   ⋯s[ σ* ] σ  = (e ⋯s[ σ* ] σ) • (T′ ⋯ˢ σ*)

_[_] : Expr (Γ ▷ T′) T → Expr Γ T′ → Expr Γ T
e₁ [ e₂ ] = e₁ ⋯s[ ⟨ idᴿ ⟩ ] σ₀ e₂
  where σ₀ : Expr Γ T′ → (Γ ▷ T′) →ˢ[ ⟨ idᴿ ⟩ ] Γ
        σ₀ e T Z = e
        σ₀ e T (S x) = ` x

extˢ : {σ* : Φ →ˢ Ψ}{T′ : Type Ψ J} → (Γ₁ →ˢ[ σ* ] Γ₂) → ((Γ₁ ▷*) →ˢ[ T′ ∙ˢ σ* ] Γ₂)
extˢ σ T (S* x) = σ _ x

_[_]** : {Γ : Ctx Φ} → Expr (Γ ▷*) T → (T′ : Type Φ J) → Expr Γ (T [ T′ ]*)
e [ T′ ]** = e ⋯s[ T′ ∙ˢ ⟨ idᴿ ⟩ ] (extˢ {T′ = T′}) idˢ

-- term reduction

data _⟶_ {Γ : Ctx Φ} : ∀ {T} → Expr Γ T → Expr Γ T → Set where
  β-λ : ((λx e₁) · e₂) ⟶ (e₁ [ e₂ ])
  β-Λ : ∀ {T′ : Type Φ J} → -- ∀ {T : Type (Φ ▷* J) ∗} → -- {e : Expr (Γ ▷*) {!!}} →
       ((Λα e) • T′) ⟶ (e [ T′ ]**)

  ξ-· : e₁ ⟶ e₁′ → (e₁ · e₂) ⟶ (e₁′ · e₂)
  ξ-Λ : e ⟶ e′ → (Λα e) ⟶ (Λα e′)
  ξ-• : e ⟶ e′ → (e • T) ⟶ (e′ • T)

-- progress

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; contradiction)

data Value {Γ : Ctx Φ} : ∀ {T : Type Φ ∗} → Expr Γ T → Set where
  λx : (e : Expr (Γ ▷ T₁) T₂) → Value (λx e)
  Λα : Value e → Value (Λα e)

data Progress {Γ : Ctx Φ} {T : Type Φ ∗} : Expr Γ T → Set where
  done : {e : Expr Γ T} → (v : Value e) → Progress e
  step : (e⟶e′ : e ⟶ e′) → Progress e

data NoVar : Ctx Φ → Set where
  ∅ : NoVar ∅
  _▷* : NoVar Γ → NoVar {Φ ▷* J} (Γ ▷*)

noVar : NoVar Γ → ¬ (Γ ∋ T)
noVar (nv ▷*) (S* x) = noVar nv x

progress : NoVar Γ → (e : Expr Γ T) → Progress e
progress nv (` x) = ⊥-elim (noVar nv x)
progress nv (λx e) = done (λx e)
progress nv (Λα e)
  with progress (nv ▷*) e
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
-- readability
∀β ∀κ : Type (Φ ▷* J) ∗ → Type Φ ∗
∀β = ∀α
∀κ = ∀α

λβ λγ : Type (Φ ▷* J) K → Type Φ (J ⇒ K)
λβ = λα
λγ = λα

λf λg λz λy : Expr (Γ ▷ T₁) T₂ → Expr Γ (T₁ ⇒ T₂)
λf = λx
λg = λx
λz = λx
λy = λx

`α : Type (Φ ▷* K) K
`α = ` Z
`β : Type ((Φ ▷* K) ▷* J) K
`β = ` (S Z)
`κ `γ : Type (((Φ ▷* K) ▷* I) ▷* J) K
`κ = ` (S (S Z))
`γ = `κ

Λκ Λβ : Expr (Γ ▷*) T → Expr Γ (∀α T)
Λκ = Λα
Λβ = Λα

`x : Expr (Γ ▷ T) T
`x = ` Z
`y `g : Expr ((Γ ▷ T) ▷ T₁) T
`y = ` (S Z)
`g = ` (S Z)
`z `f : Expr (((Γ ▷ T) ▷ T₂) ▷ T₁) T
`z = ` (S (S Z))
`f = `z

-- Church numerals

-- ∀ α (α→α) → α→α

--! FCNType
ℕᶜ : Type ∅ ∗
ℕᶜ = ∀α ((`α ⇒ `α) ⇒ (`α ⇒ `α))

--! FCNZero
zeroᶜ : Expr ∅ ℕᶜ
zeroᶜ = Λα (λg (λx `x))

--! FCNOne
oneᶜ : Expr ∅ ℕᶜ
oneᶜ = Λα (λg (λx (`g · `x)))

--! FCNSucc
succᶜ : Expr ∅ (ℕᶜ ⇒ ℕᶜ)
succᶜ = λx (Λα (λg (λx (`g · ((((` (S (S (S* Z)))) • `α) · `g) · `x)))))

--! FCNTwo
twoᶜ : Expr ∅ ℕᶜ
twoᶜ = succᶜ · (succᶜ · zeroᶜ)

fourᶜ : Expr ∅ ℕᶜ
fourᶜ = succᶜ · (succᶜ · (succᶜ · (succᶜ · zeroᶜ)))

--! FCNFour
two+twoᶜ : Expr ∅ ℕᶜ
two+twoᶜ = ((twoᶜ • ℕᶜ) · succᶜ)  · twoᶜ