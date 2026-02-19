-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --confluence-check --double-check #-}
module SystemF1 where
open import Agda.Builtin.Equality.Rewrite public

-- standard eq reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)

--! SF >
--! Type >
--! Definition
data Type (n : Nat) : Set where
  `_   : Fin n → Type n
  ∀α_  : Type (suc n) → Type n
  _⇒_  : Type n → Type n → Type n

variable
  n n′ n₁ n₂ n₃ : Nat
  α α′ α₁ α₂ α₃ : Fin n
  T T′ T₁ T₂ T₃ : Type n

--! Renaming
-- renamings
_→ᴿ_ : Nat → Nat → Set
n₁ →ᴿ n₂ = Fin n₁ → Fin n₂

--! RenamingOpaque {
opaque
  -- weakening
  wk : n →ᴿ suc n
  wk = suc

  -- identity renaming
  idᴿ : n →ᴿ n
  idᴿ α = α

  -- extend with new variable
  _∙ᴿ_ :  Fin n₂ → n₁ →ᴿ n₂ → suc n₁ →ᴿ n₂
  (α ∙ᴿ ρ) zero = α
  (_ ∙ᴿ ρ) (suc α) = ρ α

  -- apply renaming to variable
  _&ᴿ_ : Fin n₁ → n₁ →ᴿ n₂ → Fin n₂
  α &ᴿ ρ = ρ α

  -- composition
  _∘_ : n₁ →ᴿ n₂ → n₂ →ᴿ n₃ → n₁ →ᴿ n₃
  (ρ₁ ∘ ρ₂) α = ρ₂ (ρ₁ α)

-- lifting
_↑ᴿ : n₁ →ᴿ n₂ → suc n₁ →ᴿ suc n₂
_↑ᴿ ρ = zero ∙ᴿ (ρ ∘ wk)

-- apply renaming to type
_⋯ᴿ_ : Type n₁ → n₁ →ᴿ n₂ → Type n₂
(` α)      ⋯ᴿ ρ = ` (α &ᴿ ρ)
(∀α T)     ⋯ᴿ ρ = ∀α (T ⋯ᴿ (ρ ↑ᴿ))
(T₁ ⇒ T₂)  ⋯ᴿ ρ = (T₁ ⋯ᴿ ρ) ⇒ (T₂ ⋯ᴿ ρ)
--! }

variable
  ρ ρ′ ρ₁ ρ₂ ρ₃ : n₁ →ᴿ n₂

--! Substitution
-- substitutions
_→ˢ_ : Nat → Nat → Set
n₁ →ˢ n₂ = Fin n₁ → Type n₂

--! SubstitutionOpaque {
opaque
  -- lift renaming to substitution
  ⟨_⟩ : n₁ →ᴿ n₂ → n₁ →ˢ n₂
  ⟨ ρ ⟩ α = ` (α &ᴿ ρ)

  -- extend with new type
  _∙ˢ_ : Type n₂ → n₁ →ˢ n₂ → suc n₁ →ˢ n₂
  (T ∙ˢ σ) zero = T
  (T ∙ˢ σ) (suc α) = σ α

  -- apply substitution to variable
  _&ˢ_ : Fin n₁ → n₁ →ˢ n₂ → Type n₂
  α &ˢ σ = σ α

  -- lifting
  _↑ˢ : n₁ →ˢ n₂ → suc n₁ →ˢ suc n₂
  _↑ˢ σ = (` zero) ∙ˢ λ α → (σ α) ⋯ᴿ wk

-- apply substitution to type
_⋯ˢ_ : Type n₁ → n₁ →ˢ n₂ → Type n₂
(` α)         ⋯ˢ σ = α &ˢ σ
(∀α T)        ⋯ˢ σ = ∀α (T ⋯ˢ (σ ↑ˢ))
(T₁ ⇒ T₂)     ⋯ˢ σ = (T₁ ⋯ˢ σ) ⇒ (T₂ ⋯ˢ σ)

opaque
  -- composition
  _⨟_ : n₁ →ˢ n₂ → n₂ →ˢ n₃ → n₁ →ˢ n₃
  (σ₁ ⨟ σ₂) α = (σ₁ α) ⋯ˢ σ₂
--! }

variable
  σ σ′ σ₁ σ₂ σ₃ : n₁ →ˢ n₂

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
  --! RenamingBeta {
  -- computing renamings
  `beta-ext-zero           : zero  &ᴿ (α ∙ᴿ ρ)        ≡ α
  `beta-ext-suc            : suc α &ᴿ (α′ ∙ᴿ ρ)       ≡ α &ᴿ ρ
  `beta-id                 : α &ᴿ idᴿ                 ≡ α
  `beta-wk                 : α &ᴿ wk                  ≡ suc α
  `beta-comp               : α &ᴿ (ρ₁ ∘ ρ₂)           ≡ (α &ᴿ ρ₁) &ᴿ ρ₂
  -- interaction between renamings
  `associativity           : (ρ₁ ∘ ρ₂) ∘ ρ₃           ≡ ρ₁ ∘ (ρ₂ ∘ ρ₃)
  `distributivity          : (α ∙ᴿ ρ₁) ∘ ρ₂           ≡ (α &ᴿ ρ₂) ∙ᴿ (ρ₁ ∘ ρ₂)
  `interact                : wk ∘ (α ∙ᴿ ρ)            ≡ ρ
  `comp-idᵣ                : ρ ∘ idᴿ                  ≡ ρ
  `comp-idₗ                : idᴿ ∘ ρ                  ≡ ρ
  `η-id                    : zero {n} ∙ᴿ wk           ≡ idᴿ
  `η-law                   : (zero &ᴿ ρ) ∙ᴿ (wk ∘ ρ)  ≡ ρ
  --! }

  -- beta laws
  -- beta-id                 : α &ˢ ⟨ idᴿ ⟩ ≡ ` α
  -- beta-wk                 : α &ˢ ⟨ suc ⟩ ≡ ` suc α

  --! SubstitutionBeta {
  -- computing substitutions
  beta-ext-zero           : zero  &ˢ (T ∙ˢ σ)                ≡ T
  beta-ext-suc            : suc α &ˢ (T ∙ˢ σ)                ≡ α &ˢ σ
  beta-rename             : α &ˢ ⟨ ρ ⟩                       ≡ ` (α  &ᴿ ρ)
  beta-comp               : α &ˢ (σ₁ ⨟ σ₂)                   ≡ (α &ˢ σ₁) ⋯ˢ σ₂
  beta-lift               : σ ↑ˢ                             ≡ (` zero) ∙ˢ (σ ⨟ ⟨ wk ⟩)
  -- interaction between substitutions
  associativity           : (σ₁ ⨟ σ₂) ⨟ σ₃                   ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)
  distributivity          : (T ∙ˢ σ₁) ⨟ σ₂                   ≡ (T ⋯ˢ σ₂) ∙ˢ (σ₁ ⨟ σ₂)
  interact                : ⟨ wk ⟩ ⨟ (T ∙ˢ σ)                ≡ σ
  comp-idᵣ                : σ ⨟ ⟨ idᴿ ⟩                      ≡ σ
  comp-idₗ                : ⟨ idᴿ ⟩ ⨟ σ                      ≡ σ
  η-id                    : (` zero {n}) ∙ˢ ⟨ wk ⟩           ≡ ⟨ idᴿ ⟩
  η-law                   : (zero &ˢ σ) ∙ˢ (⟨ wk ⟩ ⨟ σ)      ≡ σ
  --! }
  -- η-lawᴿ                  : (` (zero &ᴿ ρ)) ∙ˢ (⟨ wk ⟩ ⨟ ⟨ ρ ⟩)   ≡ ⟨ ρ ⟩
  -- distributivityᴿ         : (T ∙ˢ σ₁) ⨟ ⟨ ρ₂ ⟩               ≡ (T ⋯ᴿ ρ₂) ∙ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)
  -- monad laws
  --! Monad
  -- composing renamings and substitutions
  identityʳ      : T ⋯ᴿ idᴿ          ≡ T
  composeᴿˢ      : (T ⋯ᴿ ρ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂)
  composeᴿᴿ      : (T ⋯ᴿ ρ₁) ⋯ᴿ ρ₂   ≡ T ⋯ᴿ (ρ₁ ∘ ρ₂)
  composeˢᴿ      : (T ⋯ˢ σ₁) ⋯ᴿ ρ₂   ≡ T ⋯ˢ (σ₁ ⨟ ⟨ ρ₂ ⟩)
  composeˢˢ      : (T ⋯ˢ σ₁) ⋯ˢ σ₂   ≡ T ⋯ˢ (σ₁ ⨟ σ₂)


  -- traversal-x             : (` α)         ⋯ˢ σ  ≡ α &ˢ σ
  -- traversal-∀             : (∀α T)        ⋯ˢ σ  ≡ ∀α (T ⋯ˢ (σ ↑ˢ))
  -- traversal-⇒             : (T₁ ⇒ T₂)     ⋯ˢ σ  ≡ (T₁ ⋯ˢ σ) ⇒ (T₂ ⋯ˢ σ)

  -- `traversal-x             : (` α)         ⋯ᴿ ρ  ≡ ` (α &ᴿ ρ)
  -- `traversal-∀             : (∀α T)        ⋯ᴿ ρ  ≡ ∀α (T ⋯ᴿ (ρ ↑ᴿ))
  -- `traversal-⇒             : (T₁ ⇒ T₂)     ⋯ᴿ ρ  ≡ (T₁ ⋯ᴿ ρ) ⇒ (T₂ ⋯ᴿ ρ)

  -- coincidence laws
  --! Coincidence
  coincidence              : T ⋯ˢ ⟨ ρ ⟩                                 ≡ T  ⋯ᴿ ρ
  coincidence-comp         : ⟨ ρ₁ ⟩ ⨟ ⟨ ρ₂ ⟩                            ≡ ⟨ ρ₂ ∘ ρ₂ ⟩

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

  identityʳ
  composeᴿˢ
  composeᴿᴿ
  composeˢᴿ
  composeˢˢ

  coincidence
  coincidence-comp
#-}

-- more coincidence lemmas ...
-- all follow directly from case analysis
-- (they are extracted from type failures,
--  i did not analyise them)

-- definitely supports the claim that we need 
-- a dedicated coincidence solving strategy
opaque
  unfolding wk ⟨_⟩ _⨟_
  coincidence-lemma₁  : (⟨ ρ ↑ᴿ ⟩ ⨟ ((T′ ⋯ᴿ ρ) ∙ˢ ⟨ idᴿ ⟩)) ≡ ((T′ ⋯ᴿ ρ) ∙ˢ ⟨ ρ ⟩)
  coincidence-lemma₁ = fun-ext λ { zero → refl; (suc x) → refl }
  coincidence-lemma₂ : ⟨  zero ∙ᴿ (ρ₁ ∘ (ρ₂ ∘ wk)) ⟩ ⨟ ((T ⋯ᴿ (ρ₁ ∘ ρ₂)) ∙ˢ ⟨ idᴿ ⟩) ≡ (T ⋯ᴿ (ρ₁ ∘ ρ₂)) ∙ˢ (⟨ ρ₁ ⟩ ⨟ ⟨ ρ₂ ⟩)
  coincidence-lemma₂ = fun-ext λ { zero → refl; (suc x) → refl }
  coincidence-lemma₃ : ⟨ zero ∙ᴿ (ρ₁ ∘ wk) ⟩ ⨟ ((` zero) ∙ˢ (σ₂ ⨟ ⟨ wk ⟩)) ≡ (` zero) ∙ˢ (⟨ ρ₁ ⟩ ⨟ (σ₂ ⨟ ⟨ wk ⟩))
  coincidence-lemma₃ = fun-ext λ { zero → refl; (suc x) → refl }
  coincidence-lemma₄ : ((` zero) ∙ˢ (σ₁ ⨟ (⟨ wk ⟩ ⨟ ⟨ zero ∙ᴿ (ρ₂ ∘ wk) ⟩))) ≡ ((` zero) ∙ˢ (σ₁ ⨟ (⟨ ρ₂ ⟩ ⨟ ⟨ wk ⟩)))
  coincidence-lemma₄ = fun-ext λ { zero → refl; (suc x) → refl }


{-# REWRITE
  coincidence-lemma₁
  coincidence-lemma₂
  coincidence-lemma₃
  coincidence-lemma₄
#-}

idˢ : n →ˢ n
idˢ = ⟨ idᴿ ⟩

-- functorial action
lift*-id1 : α &ᴿ (idᴿ ↑ᴿ) ≡ α
lift*-id1 = refl

lift*-comp1 : α &ᴿ ((ρ′ ∘ ρ) ↑ᴿ) ≡ (α &ᴿ (ρ′ ↑ᴿ)) &ᴿ (ρ ↑ᴿ)
lift*-comp1 {α = zero} = refl
lift*-comp1 {α = suc α} = refl

lifts*-id1 : α &ˢ (idˢ ↑ˢ) ≡ ` α
lifts*-id1 = refl

lifts*-comp1 : α &ˢ ((σ′ ⨟ σ) ↑ˢ) ≡ (α &ˢ (σ′ ↑ˢ)) ⋯ˢ (σ ↑ˢ)
lifts*-comp1 {α = zero} = refl
lifts*-comp1 {α = suc α} = refl


--! RenFunctorial {
lift*-id : (idᴿ {n} ↑ᴿ) ≡ idᴿ
lift*-id = refl

lift*-comp : (ρ′ ∘ ρ) ↑ᴿ ≡ (ρ′ ↑ᴿ) ∘ (ρ ↑ᴿ)
lift*-comp  = refl

ren*-id : T ⋯ᴿ idᴿ ≡ T
ren*-id = refl

ren*-comp : T ⋯ᴿ (ρ′ ∘ ρ) ≡ (T ⋯ᴿ ρ′) ⋯ᴿ ρ
ren*-comp = refl
--! }

--! SubFunctorial {
lifts*-id : (idˢ {n} ↑ˢ) ≡ idˢ
lifts*-id = refl

lifts*-comp : (σ′ ⨟ σ) ↑ˢ ≡ (σ′ ↑ˢ) ⨟ (σ ↑ˢ)
lifts*-comp = refl

sub*-id : T ⋯ˢ idˢ ≡ T
sub*-id = refl

sub*-var : (` α) ⋯ˢ σ ≡ α &ˢ σ
sub*-var = refl

sub*-comp : T ⋯ˢ (σ ⨟ σ′) ≡ (T ⋯ˢ σ) ⋯ˢ σ′
sub*-comp = refl
--! }

--! Weaken
weaken : Type n → Type (suc n)
weaken T = T ⋯ᴿ wk

--! Subzero
_[_] : Type (suc n) → Type n → Type n
T [ T′ ] = T ⋯ˢ (T′ ∙ˢ ⟨ idᴿ ⟩) 

--! Ctx
data Ctx : Nat → Set where
  ∅    : Ctx zero
  _▷_  : Ctx n → Type n → Ctx n
  _▷*  : Ctx n → Ctx (suc n)

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx n

--! Var
data _∋_ : Ctx n → Type n → Set where
  zero  : (Γ ▷ T) ∋ T
  suc   : Γ ∋ T → (Γ ▷ T′) ∋ T
  suc*  : Γ ∋ T → (Γ ▷*) ∋ (weaken T)

variable
  x x′ x₁ x₂ x₃ : Γ ∋ T

--! <
--! Expr >
--! Definition
data Expr : Ctx n → Type n → Set where
  `_    : Γ ∋ T →
          Expr Γ T
  λx_   : Expr (Γ ▷ T₁) T₂ →
          Expr Γ (T₁ ⇒ T₂)
  _·_   : Expr Γ (T₁ ⇒ T₂) →
          Expr Γ T₁ →
          Expr Γ T₂
  Λα_   : Expr (Γ ▷*) T →
          Expr Γ (∀α T)
  _·*_  : Expr Γ (∀α T) →
          (T′ : Type n) →
          Expr Γ (T [ T′ ])

variable
  e e′ e₁ e₂ e₃ : Expr Γ T

_∣_⇒ᴿ_ : n₁ →ᴿ n₂ → Ctx n₁ → Ctx n₂ → Set
ρ ∣ Γ₁ ⇒ᴿ Γ₂ = ∀ T → Γ₁ ∋ T → Γ₂ ∋ (T ⋯ᴿ ρ)

variable
  Ρ Ρ′ Ρ₁ Ρ₂ Ρ₃ : ρ ∣ Γ₁ ⇒ᴿ Γ₂

Id : idᴿ ∣ Γ ⇒ᴿ Γ
Id _ x = x -- no subst identityʳ

Wk : idᴿ ∣ Γ ⇒ᴿ (Γ ▷ T)
Wk _ = suc

wk* : wk ∣ Γ ⇒ᴿ (Γ ▷*)
wk* _ x = suc* x

_,_∣_⊚_ : ∀ ρ₁ ρ₂ → ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ρ₁ ∘ ρ₂) ∣ Γ₁ ⇒ᴿ Γ₃
(_ , _ ∣ Ρ₁ ⊚ Ρ₂) _ x = Ρ₂ _ (Ρ₁ _ x)

_⊚_ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ρ₁ ∘ ρ₂) ∣ Γ₁ ⇒ᴿ Γ₃
_⊚_ = _,_∣_⊚_ _ _

_∣_⇑ᴿ_ : ∀ ρ → ρ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ρ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T ⋯ᴿ ρ))
(_ ∣ Ρ ⇑ᴿ _) _ zero    = zero
(_ ∣ Ρ ⇑ᴿ _) _ (suc x) = suc (Ρ _ x)

_⇑ᴿ_ : ρ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ρ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T ⋯ᴿ ρ))
_⇑ᴿ_ = _ ∣_⇑ᴿ_

_∣_↑ᴿ* : ∀ ρ → ρ ∣ Γ₁ ⇒ᴿ Γ₂ → (ρ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
(_ ∣ Ρ ↑ᴿ*) _ (suc* x) = suc* (Ρ _ x) --suc* (Ρ _ x) -- no subst swap ren wk

↑ᴿ*_ : ρ ∣ Γ₁ ⇒ᴿ Γ₂ → (ρ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
↑ᴿ*_ = _ ∣_↑ᴿ*

-- new symbol?
_∣_⋯ᴿ_ : {T : Type n₁} {Γ₂ : Ctx n₂} → (ρ : n₁ →ᴿ n₂) →
  Expr Γ₁ T → ρ ∣ Γ₁ ⇒ᴿ Γ₂ → Expr Γ₂ (T ⋯ᴿ ρ)
_ ∣ (` x)      ⋯ᴿ Ρ = ` (Ρ _ x)
_ ∣ (λx e)     ⋯ᴿ Ρ = λx (_ ∣ e ⋯ᴿ (Ρ ⇑ᴿ _))
_ ∣ (Λα e)     ⋯ᴿ Ρ = Λα (_ ∣ e ⋯ᴿ (↑ᴿ* Ρ))
_ ∣ (e₁ · e₂)  ⋯ᴿ Ρ = (_ ∣ e₁ ⋯ᴿ Ρ) · (_ ∣ e₂ ⋯ᴿ Ρ)
ρ ∣ (e ·* T′)  ⋯ᴿ Ρ = (ρ ∣ e ⋯ᴿ Ρ) ·* (T′ ⋯ᴿ ρ) -- no subst swap ren single subst

Weaken : Expr Γ T → Expr (Γ ▷ T′) T
Weaken e = idᴿ ∣ e ⋯ᴿ Wk -- no subst identityʳ

weaken* : Expr Γ T → Expr (Γ ▷*) (weaken T)
weaken* e = wk ∣ e ⋯ᴿ wk*

_∣_⇒ˢ_ : n₁ →ˢ n₂ → Ctx n₁ → Ctx n₂ → Set
σ ∣ Γ₁ ⇒ˢ Γ₂ = ∀ T → Γ₁ ∋ T → Expr Γ₂ (T ⋯ˢ σ)

variable
  Σ Σ′ Σ₁ Σ₂ Σ₃ : σ ∣ Γ₁ ⇒ˢ Γ₂

_∣⟪_⟫ : ∀ ρ → ρ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ρ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
(ρ ∣⟪ Ρ ⟫) _ x = ` Ρ _ x

⟪_⟫ : ρ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ρ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
⟪_⟫ = _ ∣⟪_⟫

Idˢ : ⟨ idᴿ ⟩ ∣ Γ ⇒ˢ Γ
Idˢ _ = `_ -- no subst right-⟨ idᴿ ⟩

Wkˢ : ∀ T → ⟨ idᴿ ⟩ ∣ Γ ⇒ˢ (Γ ▷ T)
Wkˢ _ = idᴿ ∣⟪ Wk ⟫

wk*ˢ : ⟨ wk ⟩ ∣ Γ ⇒ˢ (Γ ▷*)
wk*ˢ = wk ∣⟪ wk* ⟫

-- new symbol?
_∣_∙ˢ_ : ∀ σ → Expr Γ₂ (T ⋯ˢ σ) → σ ∣ Γ₁ ⇒ˢ Γ₂ → σ ∣ (Γ₁ ▷ T) ⇒ˢ Γ₂
(_ ∣ e ∙ˢ Σ) _ zero     = e
(_ ∣ e ∙ˢ Σ) _ (suc x)  = Σ _ x

_∣_∙*_ : ∀ σ T → σ ∣ Γ₁ ⇒ˢ Γ₂ → (T ∙ˢ σ) ∣ (Γ₁ ▷*) ⇒ˢ Γ₂
(_ ∣ T ∙* Σ) _ (suc* x) = Σ _ x -- no subst swap wk single subst

_∣_⇑ˢ_ : ∀ σ → σ ∣ Γ₁ ⇒ˢ Γ₂ → ∀ T → σ ∣ (Γ₁ ▷ T) ⇒ˢ (Γ₂ ▷ (T ⋯ˢ σ))
σ ∣ Σ ⇑ˢ T = σ ∣ (` zero) ∙ˢ λ _ x → idᴿ ∣ (Σ _ x) ⋯ᴿ Wk -- no subst swap sub wk

_∣_↑ˢ* : ∀ σ → σ ∣ Γ₁ ⇒ˢ Γ₂ → (σ ↑ˢ) ∣ (Γ₁ ▷*) ⇒ˢ (Γ₂ ▷*)
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

η-Id : ⟨ idᴿ ⟩ ∣ (` (zero {Γ = Γ} {T = T})) ∙ˢ (Wkˢ T) ≡ (Idˢ {Γ = Γ ▷ T})
η-Id = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

η*-Id : ⟨ idᴿ ⟩ ∣ (Idˢ {Γ = Γ}) ↑ˢ* ≡ Idˢ
η*-Id = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Identityʳ : ∀ (e : Expr Γ T) → ⟨ idᴿ ⟩ ∣ e ⋯ˢ Idˢ ≡ e
Identityʳ (` x)      = refl
Identityʳ (λx e)     = cong λx_ (trans (cong (⟨ idᴿ ⟩ ∣ e ⋯ˢ_) η-Id) (Identityʳ e))
Identityʳ (Λα e)     = cong Λα_ (trans (cong (⟨ idᴿ ⟩ ∣ e ⋯ˢ_) η*-Id) (Identityʳ e))
Identityʳ (e₁ · e₂)  = cong₂ _·_ (Identityʳ e₁) (Identityʳ e₂)
Identityʳ (e ·* T′)  = cong (_·* T′) (Identityʳ e)

Lift-Dist-Compᴿᴿ : (Ρ₁ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (Ρ₂ : ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  ρ₁ , ρ₂ ∣ ( ρ₁ ∣ Ρ₁ ⇑ᴿ T) ⊚ (ρ₂ ∣ Ρ₂ ⇑ᴿ (T ⋯ᴿ ρ₁)) ≡ ((ρ₁ ∘ ρ₂) ∣ (ρ₁ , ρ₂ ∣ Ρ₁ ⊚ Ρ₂) ⇑ᴿ T)
Lift-Dist-Compᴿᴿ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

lift*-dist-Compᴿᴿ : (ρ₁ : n₁ →ᴿ n₂) (ρ₂ : n₂ →ᴿ n₃) (Ρ₁ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (Ρ₂ : ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  (ρ₁ ↑ᴿ) , (ρ₂ ↑ᴿ) ∣ ( ρ₁ ∣ Ρ₁ ↑ᴿ*) ⊚ (ρ₂ ∣ Ρ₂ ↑ᴿ*) ≡ ((ρ₁ ∘ ρ₂) ∣ (ρ₁ , ρ₂ ∣ Ρ₁ ⊚ Ρ₂) ↑ᴿ*)
lift*-dist-Compᴿᴿ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Composeᴿᴿ : ∀ (e : Expr Γ₁ T) (ρ₁ : n₁ →ᴿ n₂) (ρ₂ : n₂ →ᴿ n₃) (Ρ₁ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (Ρ₂ : ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  ρ₂ ∣ (ρ₁ ∣ e ⋯ᴿ Ρ₁) ⋯ᴿ Ρ₂ ≡ (ρ₁ ∘ ρ₂) ∣ e ⋯ᴿ (ρ₁ , ρ₂ ∣ Ρ₁ ⊚ Ρ₂)
Composeᴿᴿ (` x)     _  _  _  _   = refl
Composeᴿᴿ (λx e)    _  _  _  _   = cong λx_ (trans (Composeᴿᴿ e _ _ _ _) (cong (_ ∣ e ⋯ᴿ_) (Lift-Dist-Compᴿᴿ _ _)))
Composeᴿᴿ (Λα e)    _  _  _  _   = cong Λα_ (trans (Composeᴿᴿ e _ _ _ _) (cong (_ ∣ e ⋯ᴿ_) (lift*-dist-Compᴿᴿ _ _ _ _)))
Composeᴿᴿ (e₁ · e₂) _  _  _  _   = cong₂ _·_ (Composeᴿᴿ e₁ _ _ _ _) (Composeᴿᴿ e₂ _ _ _ _)
Composeᴿᴿ (e ·* T′) ρ₁ ρ₂ Ρ₁ Ρ₂  = cong (_·* (T′ ⋯ᴿ (ρ₁ ∘ ρ₂))) (Composeᴿᴿ e _ _ _ _)

Lift-Dist-Compᴿˢ : (Ρ₁ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (Σ₂ : σ₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  ⟨ ρ₁ ⟩ , σ₂ ∣ (ρ₁ ∣⟪ ρ₁ ∣ Ρ₁ ⇑ᴿ T ⟫) ⨾ (σ₂ ∣ Σ₂ ⇑ˢ (T ⋯ᴿ ρ₁)) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ∣ (⟨ ρ₁ ⟩ , σ₂ ∣ ρ₁ ∣⟪ Ρ₁ ⟫ ⨾ Σ₂) ⇑ˢ T)
Lift-Dist-Compᴿˢ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

lift*-dist-Compᴿˢ : (ρ₁ : n₁ →ᴿ n₂) (σ₂ : n₂ →ˢ n₃) (Ρ₁ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (Σ₂ : σ₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  ⟨ ρ₁ ↑ᴿ ⟩ , (σ₂ ↑ˢ) ∣ ((ρ₁ ↑ᴿ ∣⟪ ρ₁ ∣ Ρ₁ ↑ᴿ* ⟫)) ⨾ (σ₂ ∣ Σ₂ ↑ˢ*) ≡ ((⟨ ρ₁ ⟩ ⨟ σ₂) ∣ (⟨ ρ₁ ⟩ , σ₂ ∣ ρ₁ ∣⟪ Ρ₁ ⟫ ⨾ Σ₂) ↑ˢ*)
lift*-dist-Compᴿˢ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Composeᴿˢ : ∀ (e : Expr Γ₁ T) (ρ₁ : n₁ →ᴿ n₂) (σ₂ : n₂ →ˢ n₃) (Ρ₁ : ρ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (Σ₂ : σ₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  σ₂ ∣ (ρ₁ ∣ e ⋯ᴿ Ρ₁) ⋯ˢ Σ₂ ≡ (⟨ ρ₁ ⟩ ⨟ σ₂) ∣ e ⋯ˢ (⟨ ρ₁ ⟩ , σ₂ ∣ ρ₁ ∣⟪ Ρ₁ ⟫ ⨾ Σ₂)
Composeᴿˢ (` x)     _  _  _  _   = refl
Composeᴿˢ (λx e)    ρ₁ σ₂ Ρ₁ Σ₂  = cong λx_ (trans (Composeᴿˢ e _ _ _ _) (cong ((⟨ ρ₁ ⟩ ⨟ σ₂) ∣ e ⋯ˢ_) (Lift-Dist-Compᴿˢ Ρ₁ Σ₂)))
Composeᴿˢ (Λα e)    ρ₁ σ₂ Ρ₁ Σ₂  = cong Λα_ (trans (Composeᴿˢ e _ _ _ _) (cong (((⟨ ρ₁ ⟩ ⨟ σ₂) ↑ˢ) ∣ e ⋯ˢ_) (lift*-dist-Compᴿˢ _ σ₂ Ρ₁ Σ₂)))
Composeᴿˢ (e₁ · e₂) _  _  _  _   = cong₂ _·_ (Composeᴿˢ e₁ _ _ _ _) (Composeᴿˢ e₂ _ _ _ _)
Composeᴿˢ (e ·* T′) ρ₁ σ₂ Ρ₁ Ρ₂  = cong (_·* (T′ ⋯ˢ (⟨ ρ₁ ⟩ ⨟ σ₂))) (Composeᴿˢ e _ _ _ _)

postulate
  Coincidence : ∀ (e : Expr Γ₁ T) (Ρ : ρ ∣ Γ₁ ⇒ᴿ Γ₂) →
      ⟨ ρ ⟩ ∣ e ⋯ˢ (ρ ∣⟪ Ρ ⟫) ≡ (ρ ∣ e ⋯ᴿ Ρ)

Lift-Dist-Compˢᴿ : (Σ₁ : σ₁ ∣ Γ₁ ⇒ˢ Γ₂) (Ρ₂ : ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  σ₁ , ⟨ ρ₂ ⟩ ∣ (σ₁ ∣ Σ₁ ⇑ˢ T) ⨾ (ρ₂ ∣⟪ ρ₂ ∣ Ρ₂ ⇑ᴿ (T ⋯ˢ σ₁) ⟫) ≡ ((σ₁ ⨟ ⟨ ρ₂ ⟩) ∣ (σ₁ , ⟨ ρ₂ ⟩ ∣ Σ₁ ⨾ (ρ₂ ∣⟪ Ρ₂ ⟫ )) ⇑ˢ T)
Lift-Dist-Compˢᴿ Σ₁ Ρ₂ = fun-ext λ _ → fun-ext λ 
  { zero → refl; (suc x) → 
    let e = Σ₁ _ x in begin
    _ ≡⟨ Coincidence (idᴿ ∣ e ⋯ᴿ Wk) _ ⟩
    _ ≡⟨ Composeᴿᴿ e _ _ _ _ ⟩
    _ ≡⟨ sym (Composeᴿᴿ e _ idᴿ Ρ₂ Wk) ⟩
    _ ≡⟨ cong (idᴿ ∣_⋯ᴿ Wk) (sym (Coincidence e _)) ⟩
    _ ∎ }

lift*-dist-Compˢᴿ  : (σ₁ : n₁ →ˢ n₂) (ρ₂ : n₂ →ᴿ n₃) (Σ₁ : σ₁ ∣ Γ₁ ⇒ˢ Γ₂) (Ρ₂ : ρ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  (σ₁ ↑ˢ) ,  ⟨ ρ₂ ↑ᴿ ⟩ ∣ (σ₁ ∣ Σ₁ ↑ˢ* ) ⨾ ((ρ₂ ↑ᴿ) ∣⟪ ρ₂ ∣ Ρ₂ ↑ᴿ* ⟫) ≡ (σ₁ ⨟ ⟨ ρ₂ ⟩) ∣ (σ₁ , ⟨ ρ₂ ⟩ ∣ Σ₁ ⨾ (ρ₂ ∣⟪ Ρ₂ ⟫)) ↑ˢ*
lift*-dist-Compˢᴿ  _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → {!   !} }
