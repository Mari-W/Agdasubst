-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --local-confluence-check --double-check #-}
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
  (α ∙ᴿ ζ) zero = α
  (_ ∙ᴿ ζ) (suc α) = ζ α

  -- apply renaming to variable
  _&ᴿ_ : Fin n₁ → n₁ →ᴿ n₂ → Fin n₂
  α &ᴿ ζ = ζ α

  -- composition
  _∘_ : n₁ →ᴿ n₂ → n₂ →ᴿ n₃ → n₁ →ᴿ n₃
  (ζ₁ ∘ ζ₂) α = ζ₂ (ζ₁ α)

-- lifting
_↑ᴿ : n₁ →ᴿ n₂ → suc n₁ →ᴿ suc n₂
_↑ᴿ ζ = zero ∙ᴿ (ζ ∘ wk)

-- apply renaming to type
_⋯ᴿ_ : Type n₁ → n₁ →ᴿ n₂ → Type n₂
(` α)      ⋯ᴿ ζ = ` (α &ᴿ ζ)
(∀α T)     ⋯ᴿ ζ = ∀α (T ⋯ᴿ (ζ ↑ᴿ))
(T₁ ⇒ T₂)  ⋯ᴿ ζ = (T₁ ⋯ᴿ ζ) ⇒ (T₂ ⋯ᴿ ζ)
--! }

variable
  ζ ζ′ ζ₁ ζ₂ ζ₃ : n₁ →ᴿ n₂

--! Substitution
-- substitutions
_→ˢ_ : Nat → Nat → Set
n₁ →ˢ n₂ = Fin n₁ → Type n₂

--! SubstitutionOpaque {
opaque
  -- lift renaming to substitution
  ⟨_⟩ : n₁ →ᴿ n₂ → n₁ →ˢ n₂
  ⟨ ζ ⟩ α = ` (α &ᴿ ζ)

  -- extend with new type
  _∙ˢ_ : Type n₂ → n₁ →ˢ n₂ → suc n₁ →ˢ n₂
  (T ∙ˢ η) zero = T
  (T ∙ˢ η) (suc α) = η α

  -- apply substitution to variable
  _&ˢ_ : Fin n₁ → n₁ →ˢ n₂ → Type n₂
  α &ˢ η = η α

  -- lifting
  _↑ˢ : n₁ →ˢ n₂ → suc n₁ →ˢ suc n₂
  _↑ˢ η = (` zero) ∙ˢ λ α → (η α) ⋯ᴿ wk

-- apply substitution to type
_⋯ˢ_ : Type n₁ → n₁ →ˢ n₂ → Type n₂
(` α)         ⋯ˢ η = α &ˢ η
(∀α T)        ⋯ˢ η = ∀α (T ⋯ˢ (η ↑ˢ))
(T₁ ⇒ T₂)     ⋯ˢ η = (T₁ ⋯ˢ η) ⇒ (T₂ ⋯ˢ η)

opaque
  -- composition
  _⨟_ : n₁ →ˢ n₂ → n₂ →ˢ n₃ → n₁ →ˢ n₃
  (η₁ ⨟ η₂) α = (η₁ α) ⋯ˢ η₂
--! }

variable
  η η′ η₁ η₂ η₃ : n₁ →ˢ n₂

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
  `beta-ext-zero           : zero  &ᴿ (α ∙ᴿ ζ)        ≡ α
  `beta-ext-suc            : suc α &ᴿ (α′ ∙ᴿ ζ)       ≡ α &ᴿ ζ
  `beta-id                 : α &ᴿ idᴿ                 ≡ α
  `beta-wk                 : α &ᴿ wk                  ≡ suc α
  `beta-comp               : α &ᴿ (ζ₁ ∘ ζ₂)           ≡ (α &ᴿ ζ₁) &ᴿ ζ₂
  -- interaction between renamings
  `associativity           : (ζ₁ ∘ ζ₂) ∘ ζ₃           ≡ ζ₁ ∘ (ζ₂ ∘ ζ₃)
  `distributivity          : (α ∙ᴿ ζ₁) ∘ ζ₂           ≡ (α &ᴿ ζ₂) ∙ᴿ (ζ₁ ∘ ζ₂)
  `interact                : wk ∘ (α ∙ᴿ ζ)            ≡ ζ
  `comp-idᵣ                : ζ ∘ idᴿ                  ≡ ζ
  `comp-idₗ                : idᴿ ∘ ζ                  ≡ ζ
  `η-id                    : zero {n} ∙ᴿ wk           ≡ idᴿ
  `η-law                   : (zero &ᴿ ζ) ∙ᴿ (wk ∘ ζ)  ≡ ζ
  --! }

  -- beta laws
  -- beta-id                 : α &ˢ ⟨ idᴿ ⟩ ≡ ` α
  -- beta-wk                 : α &ˢ ⟨ suc ⟩ ≡ ` suc α

  --! SubstitutionBeta {
  -- computing substitutions
  beta-ext-zero           : zero  &ˢ (T ∙ˢ η)                ≡ T
  beta-ext-suc            : suc α &ˢ (T ∙ˢ η)                ≡ α &ˢ η
  beta-rename             : α &ˢ ⟨ ζ ⟩                       ≡ ` (α  &ᴿ ζ)
  beta-comp               : α &ˢ (η₁ ⨟ η₂)                   ≡ (α &ˢ η₁) ⋯ˢ η₂
  beta-lift               : η ↑ˢ                             ≡ (` zero) ∙ˢ (η ⨟ ⟨ wk ⟩)
  -- interaction between substitutions
  associativity           : (η₁ ⨟ η₂) ⨟ η₃                   ≡ η₁ ⨟ (η₂ ⨟ η₃)
  distributivity          : (T ∙ˢ η₁) ⨟ η₂                   ≡ (T ⋯ˢ η₂) ∙ˢ (η₁ ⨟ η₂)
  interact                : ⟨ wk ⟩ ⨟ (T ∙ˢ η)                ≡ η
  comp-idᵣ                : η ⨟ ⟨ idᴿ ⟩                      ≡ η
  comp-idₗ                : ⟨ idᴿ ⟩ ⨟ η                      ≡ η
  η-id                    : (` zero {n}) ∙ˢ ⟨ wk ⟩           ≡ ⟨ idᴿ ⟩
  η-law                   : (zero &ˢ η) ∙ˢ (⟨ wk ⟩ ⨟ η)      ≡ η
  --! }
  -- η-lawᴿ                  : (` (zero &ᴿ ζ)) ∙ˢ (⟨ wk ⟩ ⨟ ⟨ ζ ⟩)   ≡ ⟨ ζ ⟩
  -- distributivityᴿ         : (T ∙ˢ η₁) ⨟ ⟨ ζ₂ ⟩               ≡ (T ⋯ᴿ ζ₂) ∙ˢ (η₁ ⨟ ⟨ ζ₂ ⟩)
  -- monad laws
  --! Monad
  -- composing renamings and substitutions
  identityᵣ      : T ⋯ᴿ idᴿ          ≡ T
  composeᴿˢ      : (T ⋯ᴿ ζ₁) ⋯ˢ η₂   ≡ T ⋯ˢ (⟨ ζ₁ ⟩ ⨟ η₂)
  composeᴿᴿ      : (T ⋯ᴿ ζ₁) ⋯ᴿ ζ₂   ≡ T ⋯ᴿ (ζ₁ ∘ ζ₂)
  composeˢᴿ      : (T ⋯ˢ η₁) ⋯ᴿ ζ₂   ≡ T ⋯ˢ (η₁ ⨟ ⟨ ζ₂ ⟩)
  composeˢˢ      : (T ⋯ˢ η₁) ⋯ˢ η₂   ≡ T ⋯ˢ (η₁ ⨟ η₂)


  -- traversal-x             : (` α)         ⋯ˢ η  ≡ α &ˢ η
  -- traversal-∀             : (∀α T)        ⋯ˢ η  ≡ ∀α (T ⋯ˢ (η ↑ˢ))
  -- traversal-⇒             : (T₁ ⇒ T₂)     ⋯ˢ η  ≡ (T₁ ⋯ˢ η) ⇒ (T₂ ⋯ˢ η)

  -- `traversal-x             : (` α)         ⋯ᴿ ζ  ≡ ` (α &ᴿ ζ)
  -- `traversal-∀             : (∀α T)        ⋯ᴿ ζ  ≡ ∀α (T ⋯ᴿ (ζ ↑ᴿ))
  -- `traversal-⇒             : (T₁ ⇒ T₂)     ⋯ᴿ ζ  ≡ (T₁ ⋯ᴿ ζ) ⇒ (T₂ ⋯ᴿ ζ)

  -- coincidence laws
  --! Coincidence
  coincidence              : T ⋯ˢ ⟨ ζ ⟩                                 ≡ T  ⋯ᴿ ζ
  coincidence-comp         : ⟨ ζ₁ ⟩ ⨟ ⟨ ζ₂ ⟩                            ≡ ⟨ ζ₁ ∘ ζ₂ ⟩

  -- proofs

-- more coincidence lemmas ...
-- all follow directly from case analysis
-- (they are extracted from type failures,
--  i did not analyise them)

-- definitely supports the claim that we need 
-- a dedicated coincidence solving strategy
opaque
  unfolding wk ⟨_⟩ _⨟_
  coincidence-lemma₁  : (⟨ ζ ↑ᴿ ⟩ ⨟ ((T′ ⋯ᴿ ζ) ∙ˢ ⟨ idᴿ ⟩)) ≡ ((T′ ⋯ᴿ ζ) ∙ˢ ⟨ ζ ⟩)
  coincidence-lemma₁ = fun-ext λ { zero → refl; (suc x) → refl }
  coincidence-lemma₂ : ⟨  zero ∙ᴿ (ζ₁ ∘ (ζ₂ ∘ wk)) ⟩ ⨟ ((T ⋯ᴿ (ζ₁ ∘ ζ₂)) ∙ˢ ⟨ idᴿ ⟩) ≡ (T ⋯ᴿ (ζ₁ ∘ ζ₂)) ∙ˢ (⟨ ζ₁ ⟩ ⨟ ⟨ ζ₂ ⟩)
  coincidence-lemma₂ = fun-ext λ { zero → refl; (suc x) → refl }
  coincidence-lemma₃ : ⟨ zero ∙ᴿ (ζ₁ ∘ wk) ⟩ ⨟ ((` zero) ∙ˢ (η₂ ⨟ ⟨ wk ⟩)) ≡ (` zero) ∙ˢ (⟨ ζ₁ ⟩ ⨟ (η₂ ⨟ ⟨ wk ⟩))
  coincidence-lemma₃ = fun-ext λ { zero → refl; (suc x) → refl }
  coincidence-lemma₄ : ((` zero) ∙ˢ (η₁ ⨟ (⟨ wk ⟩ ⨟ ⟨ zero ∙ᴿ (ζ₂ ∘ wk) ⟩))) ≡ ((` zero) ∙ˢ (η₁ ⨟ (⟨ ζ₂ ⟩ ⨟ ⟨ wk ⟩)))
  coincidence-lemma₄ = fun-ext λ { zero → refl; (suc x) → refl }
  coincidence-lemma₅ : (η₁ ⨟ (⟨ wk ⟩ ⨟ ⟨ zero ∙ᴿ (ζ₂ ∘ wk) ⟩)) ≡ (η₁ ⨟ (⟨ ζ₂ ⟩ ⨟ ⟨ wk ⟩))
  coincidence-lemma₅ = fun-ext λ { zero → refl; (suc x) → refl }
  coincidence-lemma₆ : (⟨ wk ∘ (zero ∙ᴿ (ζ₂ ∘ wk)) ⟩ ⨟ ((T′ ⋯ˢ (η₁ ⨟ ⟨ ζ₂ ⟩)) ∙ˢ ⟨ idᴿ ⟩)) ≡ ⟨ ζ₂ ⟩ 
  coincidence-lemma₆ = fun-ext λ { zero → refl; (suc x) → refl }
  coincidence-lemma₇ : ((T′ ⋯ˢ (η₁ ⨟ ⟨ ζ₂ ⟩)) ∙ˢ (η₁ ⨟ (⟨ ζ₂ ∘ wk ⟩ ⨟ ((T′ ⋯ˢ (η₁ ⨟ ⟨ ζ₂ ⟩)) ∙ˢ ⟨ idᴿ ⟩))))≡ ((T′ ⋯ˢ (η₁ ⨟ ⟨ ζ₂ ⟩)) ∙ˢ (η₁ ⨟ ⟨ ζ₂ ⟩))
  coincidence-lemma₇ = fun-ext λ { zero → refl; (suc x) → refl }
  
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
  coincidence-lemma₃
  coincidence-lemma₄
  coincidence-lemma₅
  coincidence-lemma₆
  coincidence-lemma₇
#-}

idˢ : n →ˢ n
idˢ = ⟨ idᴿ ⟩

-- functorial action
lift*-id1 : α &ᴿ (idᴿ ↑ᴿ) ≡ α
lift*-id1 = refl

lift*-comp1 : α &ᴿ ((ζ′ ∘ ζ) ↑ᴿ) ≡ (α &ᴿ (ζ′ ↑ᴿ)) &ᴿ (ζ ↑ᴿ)
lift*-comp1 {α = zero} = refl
lift*-comp1 {α = suc α} = refl

lifts*-id1 : α &ˢ (idˢ ↑ˢ) ≡ ` α
lifts*-id1 = refl

lifts*-comp1 : α &ˢ ((η′ ⨟ η) ↑ˢ) ≡ (α &ˢ (η′ ↑ˢ)) ⋯ˢ (η ↑ˢ)
lifts*-comp1 {α = zero} = refl
lifts*-comp1 {α = suc α} = refl


--! RenFunctorial {
lift*-id : (idᴿ {n} ↑ᴿ) ≡ idᴿ
lift*-id = refl

lift*-comp : (ζ′ ∘ ζ) ↑ᴿ ≡ (ζ′ ↑ᴿ) ∘ (ζ ↑ᴿ)
lift*-comp  = refl

ren*-id : T ⋯ᴿ idᴿ ≡ T
ren*-id = refl                  -- *

ren*-comp : T ⋯ᴿ (ζ′ ∘ ζ) ≡ (T ⋯ᴿ ζ′) ⋯ᴿ ζ
ren*-comp = refl                -- *
--! }

--! SubFunctorial {
lifts*-id : (idˢ {n} ↑ˢ) ≡ idˢ
lifts*-id = refl

lifts*-comp : (η′ ⨟ η) ↑ˢ ≡ (η′ ↑ˢ) ⨟ (η ↑ˢ)
lifts*-comp = refl

sub*-id : T ⋯ˢ idˢ ≡ T
sub*-id = refl

sub*-var : (` α) ⋯ˢ η ≡ α &ˢ η
sub*-var = refl                 -- *

sub*-comp : T ⋯ˢ (η ⨟ η′) ≡ (T ⋯ˢ η) ⋯ˢ η′
sub*-comp = refl                -- *
--! }

--! Weaken
weaken : Type n → Type (suc n)
weaken T = T ⋯ᴿ wk

--! Subzero
_[_]* : Type (suc n) → Type n → Type n
T [ T′ ]* = T ⋯ˢ (T′ ∙ˢ idˢ) 

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
  λx    : Expr (Γ ▷ T₁) T₂ →
          Expr Γ (T₁ ⇒ T₂)
  _·_   : Expr Γ (T₁ ⇒ T₂) →
          Expr Γ T₁ →
          Expr Γ T₂
  Λα    : Expr (Γ ▷*) T →
          Expr Γ (∀α T)
  _·*_  : Expr Γ (∀α T) →
          (T′ : Type n) →
          Expr Γ (T [ T′ ]*)

variable
  e e′ e₁ e₁′ e₂ e₃ : Expr Γ T

--! Renaming
_∣_⇒ᴿ_ : n₁ →ᴿ n₂ → Ctx n₁ → Ctx n₂ → Set
ζ ∣ Γ₁ ⇒ᴿ Γ₂ = ∀ T → Γ₁ ∋ T → Γ₂ ∋ (T ⋯ᴿ ζ)

variable
  ρ ρ′ ρ₁ ρ₂ ρ₃ : ζ ∣ Γ₁ ⇒ᴿ Γ₂

--! Ren >
--! Idr
Idᴿ : idᴿ ∣ Γ ⇒ᴿ Γ
Idᴿ _ x = x -- no subst identityᵣ

Wk : ∀ T → idᴿ ∣ Γ ⇒ᴿ (Γ ▷ T)
Wk _ _ = suc

wk* : wk ∣ Γ ⇒ᴿ (Γ ▷*)
wk* _ x = suc* x

--! Composition
_,_∣_⊚_ : ∀ ζ₁ ζ₂ → ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ζ₁ ∘ ζ₂) ∣ Γ₁ ⇒ᴿ Γ₃
(_ , _ ∣ ρ₁ ⊚ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_⊚_ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ζ₁ ∘ ζ₂) ∣ Γ₁ ⇒ᴿ Γ₃
_⊚_ = _,_∣_⊚_ _ _

--! Extension
_∣_∙ᴿ_ : ∀ ζ → Γ₂ ∋ (T ⋯ᴿ ζ) → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ Γ₂
(_ ∣ x ∙ᴿ ρ) _ zero     = x
(_ ∣ _ ∙ᴿ ρ) _ (suc x)  = ρ _ x

-- _∣_∙ᴿ*_ : ∀ ζ x → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (x ∙ᴿ ζ) ∣ (Γ₁ ▷*) ⇒ᴿ Γ₂
-- (_ ∣ _ ∙ᴿ* ρ) _ (suc* x) = ρ _ x -- no subst swap wk single subst

--! Lifting
_∣_⇑ᴿ_ : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T ⋯ᴿ ζ))
(ζ ∣ ρ ⇑ᴿ _) = ζ ∣ zero ∙ᴿ (ζ , idᴿ ∣ ρ ⊚ (Wk _))

_⇑ᴿ_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T ⋯ᴿ ζ))
_⇑ᴿ_ = _ ∣_⇑ᴿ_

--! TLifting
_∣_↑ᴿ* : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (ζ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
(_ ∣ ρ ↑ᴿ*) _ (suc* x) = suc* (ρ _ x) 

↑ᴿ*_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (ζ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
↑ᴿ*_ = _ ∣_↑ᴿ*

-- new symbol?
--! Traversal
_∣_⋯ᴿ_ : (ζ : n₁ →ᴿ n₂) → Expr Γ₁ T → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → Expr Γ₂ (T ⋯ᴿ ζ)
_  ∣ (` x)      ⋯ᴿ ρ  = ` (ρ _ x)
_  ∣ (λx e)     ⋯ᴿ ρ  = λx (_ ∣ e ⋯ᴿ (ρ ⇑ᴿ _))
_  ∣ (Λα e)     ⋯ᴿ ρ  = Λα (_ ∣ e ⋯ᴿ (↑ᴿ* ρ))
_  ∣ (e₁ · e₂)  ⋯ᴿ ρ  = (_ ∣ e₁ ⋯ᴿ ρ) · (_ ∣ e₂ ⋯ᴿ ρ)
ζ  ∣ (e ·* T′)  ⋯ᴿ ρ  = (ζ ∣ e ⋯ᴿ ρ) ·* (T′ ⋯ᴿ ζ) -- no subst swap ren single subst

Weaken : Expr Γ T → Expr (Γ ▷ T′) T
Weaken e = idᴿ ∣ e ⋯ᴿ (Wk _) -- no subst identityᵣ

weaken* : Expr Γ T → Expr (Γ ▷*) (weaken T)
weaken* e = wk ∣ e ⋯ᴿ wk*

--! <
--! Substitution
_∣_⇒ˢ_ : n₁ →ˢ n₂ → Ctx n₁ → Ctx n₂ → Set
η ∣ Γ₁ ⇒ˢ Γ₂ = ∀ T → Γ₁ ∋ T → Expr Γ₂ (T ⋯ˢ η)

--! Sub >
variable
  σ σ′ σ₁ σ₂ σ₃ : η ∣ Γ₁ ⇒ˢ Γ₂

-- raising a renaming to a substitution
_∣⟪_⟫ : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
(ζ ∣⟪ ρ ⟫) _ x = ` ρ _ x

⟪_⟫ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
⟪_⟫ = _ ∣⟪_⟫

--! Ids
Idˢ : idˢ ∣ Γ ⇒ˢ Γ
Idˢ _ = `_ -- no subst right-⟨ idᴿ ⟩

Wkˢ : ∀ T → ⟨ idᴿ ⟩ ∣ Γ ⇒ˢ (Γ ▷ T)
Wkˢ _ = idᴿ ∣⟪ Wk _ ⟫

wk*ˢ : ⟨ wk ⟩ ∣ Γ ⇒ˢ (Γ ▷*)
wk*ˢ = wk ∣⟪ wk* ⟫

-- extending a substitution
-- new symbol?
--! Extension
_∣_∙ˢ_ : ∀ η → Expr Γ₂ (T ⋯ˢ η) → η ∣ Γ₁ ⇒ˢ Γ₂ → η ∣ (Γ₁ ▷ T) ⇒ˢ Γ₂
(_ ∣ e ∙ˢ σ) _ zero     = e
(_ ∣ e ∙ˢ σ) _ (suc x)  = σ _ x

_∣_∙ˢ*_ : ∀ η T → η ∣ Γ₁ ⇒ˢ Γ₂ → (T ∙ˢ η) ∣ (Γ₁ ▷*) ⇒ˢ Γ₂
(_ ∣ T ∙ˢ* σ) _ (suc* x) = σ _ x -- no subst swap wk single subst

-- lifting a substitution
--! Lifting
_∣_⇑ˢ_ : ∀ η → η ∣ Γ₁ ⇒ˢ Γ₂ → ∀ T → η ∣ (Γ₁ ▷ T) ⇒ˢ (Γ₂ ▷ (T ⋯ˢ η))
η ∣ σ ⇑ˢ T = η ∣ (` zero) ∙ˢ λ _ x → idᴿ ∣ (σ _ x) ⋯ᴿ (Wk _) -- no subst swap sub wk

-- type lifting
--! TLifting
_∣_↑ˢ* : ∀ η → η ∣ Γ₁ ⇒ˢ Γ₂ → (η ↑ˢ) ∣ (Γ₁ ▷*) ⇒ˢ (Γ₂ ▷*)
(η ∣ σ ↑ˢ*) _ (suc* x) = _ ∣ (σ _ x) ⋯ᴿ wk*

-- expression substitution - traversal
-- new symbol?
--! Traversal
_∣_⋯ˢ_ : (η : n₁ →ˢ n₂) → Expr Γ₁ T → η ∣ Γ₁ ⇒ˢ Γ₂ → Expr Γ₂ (T ⋯ˢ η)
η  ∣ (` x)      ⋯ˢ σ  = σ _ x
η  ∣ (λx e)     ⋯ˢ σ  = λx (η ∣ e ⋯ˢ (η ∣ σ ⇑ˢ _))
η  ∣ (Λα e)     ⋯ˢ σ  = Λα ((η ↑ˢ) ∣ e ⋯ˢ (η ∣ σ ↑ˢ*))
η  ∣ (e · e₁)   ⋯ˢ σ  = (η ∣ e ⋯ˢ σ) · (η ∣ e₁ ⋯ˢ σ)
η  ∣ (e ·* T′)  ⋯ˢ σ  = (η ∣ e ⋯ˢ σ) ·* (T′ ⋯ˢ η) -- no subst swap sub single subst

--! CompDefinition
_,_∣_⨾_ : ∀ η₁ η₂ → η₁ ∣ Γ₁ ⇒ˢ Γ₂ → η₂ ∣ Γ₂ ⇒ˢ Γ₃ → (η₁ ⨟ η₂) ∣ Γ₁ ⇒ˢ Γ₃
(_ , _ ∣ σ₁ ⨾ σ₂) _ x = _ ∣ (σ₁ _ x) ⋯ˢ σ₂

opaque
  η-Id : ⟨ idᴿ ⟩ ∣ (` (zero {Γ = Γ} {T = T})) ∙ˢ (Wkˢ T) ≡ (Idˢ {Γ = Γ ▷ T})
  η-Id = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  η*-Id : ⟨ idᴿ ⟩ ∣ (Idˢ {Γ = Γ}) ↑ˢ* ≡ Idˢ
  η*-Id = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Identityᵣ : ∀ (e : Expr Γ T) → ⟨ idᴿ ⟩ ∣ e ⋯ˢ Idˢ ≡ e
  Identityᵣ (` x)      = refl
  Identityᵣ (λx e)     = cong λx (trans (cong (⟨ idᴿ ⟩ ∣ e ⋯ˢ_) η-Id) (Identityᵣ e))
  Identityᵣ (Λα e)     = cong Λα (trans (cong (⟨ idᴿ ⟩ ∣ e ⋯ˢ_) η*-Id) (Identityᵣ e))
  Identityᵣ (e₁ · e₂)  = cong₂ _·_ (Identityᵣ e₁) (Identityᵣ e₂)
  Identityᵣ (e ·* T′)  = cong (_·* T′) (Identityᵣ e)

  Lift-Dist-Compᴿᴿ : (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    ζ₁ , ζ₂ ∣ ( ζ₁ ∣ ρ₁ ⇑ᴿ T) ⊚ (ζ₂ ∣ ρ₂ ⇑ᴿ (T ⋯ᴿ ζ₁)) ≡ ((ζ₁ ∘ ζ₂) ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⊚ ρ₂) ⇑ᴿ T)
  Lift-Dist-Compᴿᴿ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  lift*-dist-Compᴿᴿ : (ζ₁ : n₁ →ᴿ n₂) (ζ₂ : n₂ →ᴿ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    (ζ₁ ↑ᴿ) , (ζ₂ ↑ᴿ) ∣ ( ζ₁ ∣ ρ₁ ↑ᴿ*) ⊚ (ζ₂ ∣ ρ₂ ↑ᴿ*) ≡ ((ζ₁ ∘ ζ₂) ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⊚ ρ₂) ↑ᴿ*)
  lift*-dist-Compᴿᴿ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Composeᴿᴿ : ∀ (e : Expr Γ₁ T) (ζ₁ : n₁ →ᴿ n₂) (ζ₂ : n₂ →ᴿ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    ζ₂ ∣ (ζ₁ ∣ e ⋯ᴿ ρ₁) ⋯ᴿ ρ₂ ≡ (ζ₁ ∘ ζ₂) ∣ e ⋯ᴿ (ζ₁ , ζ₂ ∣ ρ₁ ⊚ ρ₂)
  Composeᴿᴿ (` x)     _  _  _  _   = refl
  Composeᴿᴿ (λx e)    _  _  _  _   = cong λx (trans (Composeᴿᴿ e _ _ _ _) (cong (_ ∣ e ⋯ᴿ_) (Lift-Dist-Compᴿᴿ _ _)))
  Composeᴿᴿ (Λα e)    _  _  _  _   = cong Λα (trans (Composeᴿᴿ e _ _ _ _) (cong (_ ∣ e ⋯ᴿ_) (lift*-dist-Compᴿᴿ _ _ _ _)))
  Composeᴿᴿ (e₁ · e₂) _  _  _  _   = cong₂ _·_ (Composeᴿᴿ e₁ _ _ _ _) (Composeᴿᴿ e₂ _ _ _ _)
  Composeᴿᴿ (e ·* T′) ζ₁ ζ₂ ρ₁ ρ₂  = cong (_·* (T′ ⋯ᴿ (ζ₁ ∘ ζ₂))) (Composeᴿᴿ e _ _ _ _)

  Lift-Dist-Compᴿˢ : (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    ⟨ ζ₁ ⟩ , η₂ ∣ (ζ₁ ∣⟪ ζ₁ ∣ ρ₁ ⇑ᴿ T ⟫) ⨾ (η₂ ∣ σ₂ ⇑ˢ (T ⋯ᴿ ζ₁)) ≡ ((⟨ ζ₁ ⟩ ⨟ η₂) ∣ (⟨ ζ₁ ⟩ , η₂ ∣ ζ₁ ∣⟪ ρ₁ ⟫ ⨾ σ₂) ⇑ˢ T)
  Lift-Dist-Compᴿˢ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  lift*-dist-Compᴿˢ : (ζ₁ : n₁ →ᴿ n₂) (η₂ : n₂ →ˢ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    ⟨ ζ₁ ↑ᴿ ⟩ , (η₂ ↑ˢ) ∣ ((ζ₁ ↑ᴿ ∣⟪ ζ₁ ∣ ρ₁ ↑ᴿ* ⟫)) ⨾ (η₂ ∣ σ₂ ↑ˢ*) ≡ ((⟨ ζ₁ ⟩ ⨟ η₂) ∣ (⟨ ζ₁ ⟩ , η₂ ∣ ζ₁ ∣⟪ ρ₁ ⟫ ⨾ σ₂) ↑ˢ*)
  lift*-dist-Compᴿˢ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Composeᴿˢ : ∀ (e : Expr Γ₁ T) (ζ₁ : n₁ →ᴿ n₂) (η₂ : n₂ →ˢ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    η₂ ∣ (ζ₁ ∣ e ⋯ᴿ ρ₁) ⋯ˢ σ₂ ≡ (⟨ ζ₁ ⟩ ⨟ η₂) ∣ e ⋯ˢ (⟨ ζ₁ ⟩ , η₂ ∣ ζ₁ ∣⟪ ρ₁ ⟫ ⨾ σ₂)
  Composeᴿˢ (` x)     _  _  _  _   = refl
  Composeᴿˢ (λx e)    ζ₁ η₂ ρ₁ σ₂  = cong λx (trans (Composeᴿˢ e _ _ _ _) (cong ((⟨ ζ₁ ⟩ ⨟ η₂) ∣ e ⋯ˢ_) (Lift-Dist-Compᴿˢ ρ₁ σ₂)))
  Composeᴿˢ (Λα e)    ζ₁ η₂ ρ₁ σ₂  = cong Λα (trans (Composeᴿˢ e _ _ _ _) (cong (((⟨ ζ₁ ⟩ ⨟ η₂) ↑ˢ) ∣ e ⋯ˢ_) (lift*-dist-Compᴿˢ _ η₂ ρ₁ σ₂)))
  Composeᴿˢ (e₁ · e₂) _  _  _  _   = cong₂ _·_ (Composeᴿˢ e₁ _ _ _ _) (Composeᴿˢ e₂ _ _ _ _)
  Composeᴿˢ (e ·* T′) ζ₁ η₂ ρ₁ ρ₂  = cong (_·* (T′ ⋯ˢ (⟨ ζ₁ ⟩ ⨟ η₂))) (Composeᴿˢ e _ _ _ _)

  η-Idᴿᵣ : idᴿ ∣ (zero {Γ = Γ} {T = T}) ∙ᴿ (Wk T) ≡ (Idᴿ{Γ = Γ ▷ T})
  η-Idᴿᵣ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  η*-Idᴿᵣ : idᴿ ∣ (Idᴿ{Γ = Γ}) ↑ᴿ* ≡ Idᴿ
  η*-Idᴿᵣ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }


  Coincidence : ∀ (e : Expr Γ₁ T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
      ⟨ ζ ⟩ ∣ e ⋯ˢ (ζ ∣⟪ ρ ⟫) ≡ (ζ ∣ e ⋯ᴿ ρ)
  Coincidence e ρ = begin
    _ ≡⟨ sym (Composeᴿˢ e _ _ ρ Idˢ) ⟩ 
    _ ≡⟨ Identityᵣ (_ ∣ e ⋯ᴿ ρ) ⟩ 
    _ ∎

Lift-Dist-Compˢᴿ : (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  η₁ , ⟨ ζ₂ ⟩ ∣ (η₁ ∣ σ₁ ⇑ˢ T) ⨾ (ζ₂ ∣⟪ ζ₂ ∣ ρ₂ ⇑ᴿ (T ⋯ˢ η₁) ⟫) ≡ ((η₁ ⨟ ⟨ ζ₂ ⟩) ∣ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ (ζ₂ ∣⟪ ρ₂ ⟫ )) ⇑ˢ T)
Lift-Dist-Compˢᴿ σ₁ ρ₂ = fun-ext λ _ → fun-ext λ 
  { zero → refl; (suc x) → 
    let e = σ₁ _ x in begin
    _ ≡⟨ Coincidence (idᴿ ∣ e ⋯ᴿ (Wk _)) _ ⟩
    _ ≡⟨ Composeᴿᴿ e idᴿ _ _ _ ⟩
    _ ≡⟨ sym (Composeᴿᴿ e _ idᴿ ρ₂ (Wk _)) ⟩
    _ ≡⟨ cong (idᴿ ∣_⋯ᴿ (Wk _)) (sym (Coincidence e _)) ⟩
    _ ∎ }

lift*-dist-Compˢᴿ  : (η₁ : n₁ →ˢ n₂) (ζ₂ : n₂ →ᴿ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  (η₁ ↑ˢ) ,  ⟨ ζ₂ ↑ᴿ ⟩ ∣ (η₁ ∣ σ₁ ↑ˢ* ) ⨾ ((ζ₂ ↑ᴿ) ∣⟪ ζ₂ ∣ ρ₂ ↑ᴿ* ⟫) ≡ (η₁ ⨟ ⟨ ζ₂ ⟩) ∣ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ (ζ₂ ∣⟪ ρ₂ ⟫)) ↑ˢ*
lift*-dist-Compˢᴿ  η₁ ζ₂ σ₁ ρ₂ = fun-ext λ _ → fun-ext λ 
  { (suc* x) → 
    let e = σ₁ _ x in begin 
    _ ≡⟨ Coincidence (wk ∣ e ⋯ᴿ wk*) (ζ₂ ∣ ρ₂ ↑ᴿ*) ⟩ 
    _ ≡⟨ Composeᴿᴿ e _ _ wk* (ζ₂ ∣ ρ₂ ↑ᴿ*)  ⟩ 
    _ ≡⟨ sym (Composeᴿᴿ e _ _ ρ₂ wk*) ⟩ 
    _ ≡⟨ cong (wk ∣_⋯ᴿ wk*) (sym (Coincidence e _)) ⟩ 
    _ ∎ } 
    
Composeˢᴿ : ∀ (e : Expr Γ₁ T) (η₁ : n₁ →ˢ n₂) (ζ₂ : n₂ →ᴿ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  ζ₂ ∣ (η₁ ∣ e ⋯ˢ σ₁) ⋯ᴿ ρ₂ ≡ (η₁ ⨟ ⟨ ζ₂ ⟩) ∣ e ⋯ˢ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ (ζ₂ ∣⟪ ρ₂ ⟫))
Composeˢᴿ (` x)     _  _  σ₁  _  = sym (Coincidence (σ₁ _ x) _)
Composeˢᴿ (λx e)    η₁ ζ₂ σ₁ ρ₂  = cong λx (trans (Composeˢᴿ e _ _ _ _) (cong ((η₁ ⨟ ⟨ ζ₂ ⟩) ∣ e ⋯ˢ_) (Lift-Dist-Compˢᴿ σ₁ ρ₂)))
Composeˢᴿ (Λα e)    η₁ ζ₂ σ₁ ρ₂  = cong Λα (trans (Composeˢᴿ e _ _ _ _) (cong (((η₁ ⨟ ⟨ ζ₂ ⟩) ↑ˢ) ∣ e ⋯ˢ_) (lift*-dist-Compˢᴿ η₁ ζ₂ σ₁ ρ₂)))
Composeˢᴿ (e₁ · e₂) _  _  _  _   = cong₂ _·_ (Composeˢᴿ e₁ _ _ _ _) (Composeˢᴿ e₂ _ _ _ _)
Composeˢᴿ (e ·* T′) η₁ ζ₂ σ₁ ρ₂  = cong (_·* (T′ ⋯ˢ (η₁ ⨟ ⟨ ζ₂ ⟩))) (Composeˢᴿ e η₁ ζ₂ σ₁ ρ₂) 


Lift-Dist-Compˢˢ : (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  η₁ , η₂ ∣ (η₁ ∣ σ₁ ⇑ˢ T) ⨾ (η₂ ∣ σ₂ ⇑ˢ (T ⋯ˢ η₁)) ≡ ((η₁ ⨟ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ σ₂) ⇑ˢ T)
Lift-Dist-Compˢˢ σ₁ σ₂ = fun-ext λ _ → fun-ext λ 
  { zero → refl; (suc x) → 
    let e = σ₁ _ x in begin
    _ ≡⟨ Composeᴿˢ e _ _ _ _ ⟩
    _ ≡⟨ cong (_ ∣ e ⋯ˢ_) (fun-ext (λ _ → fun-ext λ x → sym (Coincidence (σ₂ _ x) _))) ⟩
    _ ≡⟨ sym (Composeˢᴿ e _ idᴿ σ₂ (Wk _)) ⟩
    _ ∎ }
  
lift*-dist-Compˢˢ : (η₁ : n₁ →ˢ n₂) (η₂ : n₂ →ˢ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  (η₁ ↑ˢ) , (η₂ ↑ˢ) ∣ (η₁ ∣ σ₁ ↑ˢ*) ⨾ (η₂ ∣ σ₂ ↑ˢ*) ≡ ((η₁ ⨟ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ σ₂) ↑ˢ*)
lift*-dist-Compˢˢ _ η₂ σ₁ σ₂ = fun-ext λ _ → fun-ext λ 
  { (suc* x) → 
    let e = σ₁ _ x in begin
    _ ≡⟨ Composeᴿˢ e _ _ _ _ ⟩
    _ ≡⟨ cong ((η₂ ⨟ ⟨ wk ⟩) ∣ e ⋯ˢ_) (fun-ext (λ _ → fun-ext λ { x → sym (Coincidence (σ₂ _ x) wk*) })) ⟩
    _ ≡⟨ sym (Composeˢᴿ e _ wk σ₂ wk*) ⟩
    _ ∎ }

--! ComposeType
Composeˢˢ : ∀ (e : Expr Γ₁ T) (η₁ : n₁ →ˢ n₂) (η₂ : n₂ →ˢ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  η₂ ∣ (η₁ ∣ e ⋯ˢ σ₁) ⋯ˢ σ₂ ≡ (η₁ ⨟ η₂) ∣ e ⋯ˢ (η₁ , η₂ ∣ σ₁ ⨾ σ₂)

--! ComposeBody
Composeˢˢ (` x)      _  _  _  _   = refl
Composeˢˢ (λx e)     η₁ η₂ σ₁ σ₂  = cong λx (trans (Composeˢˢ e _ _ _ _)
                                           (cong ((η₁ ⨟ η₂) ∣ e ⋯ˢ_) (Lift-Dist-Compˢˢ σ₁ σ₂)))
Composeˢˢ (Λα e)     η₁ η₂ σ₁ σ₂  = cong Λα (trans (Composeˢˢ e _ _ _ _)
                                           (cong (((η₁ ⨟ η₂) ↑ˢ) ∣ e ⋯ˢ_) (lift*-dist-Compˢˢ η₁ η₂ σ₁ σ₂)))
Composeˢˢ (e₁ · e₂)  _  _  _  _   = cong₂ _·_ (Composeˢˢ e₁ _ _ _ _)
                                             (Composeˢˢ e₂ _ _ _ _)
Composeˢˢ (e ·* T′)  η₁ η₂ σ₁ σ₂  = cong (_·* (T′ ⋯ˢ (η₁ ⨟ η₂))) (Composeˢˢ e _ _ _ _)

-- single substitution, semantics, and progress

--! Sem >
--! SingleSub {
_[_] : Expr (Γ ▷ T′) T → Expr Γ T′ → Expr Γ T
e [ e′ ] = idˢ ∣ e ⋯ˢ (idˢ ∣ e′ ∙ˢ Idˢ)

_[*_*] : Expr (Γ ▷*) T → (T′ : Type n) → Expr Γ (T [ T′ ]*)
e [* T′ *] = (T′ ∙ˢ idˢ) ∣ e ⋯ˢ (idˢ ∣ T′ ∙ˢ* Idˢ)
--! }

--! Definition
data _⟶_ : Expr Γ T → Expr Γ T → Set where
  β-λ   : (λx e₁ · e₂) ⟶ (e₁ [ e₂ ])
  β-Λ   : (Λα e ·* T′) ⟶ (e [* T′ *])
  ξ-·   : e₁ ⟶ e₁′ → (e₁ · e₂) ⟶ (e₁′ · e₂)
  ξ-·*  : e ⟶ e′ → (e ·* T) ⟶ (e′ ·* T)
  ξ-Λ   : e ⟶ e′ → (Λα e) ⟶ (Λα e′)

data _⟶*_ : Expr Γ T → Expr Γ T → Set where
  ⟶refl : e ⟶* e
  ⟶trans : e₁ ⟶ e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; contradiction)

--! ProgressDefs {
data Value : Expr Γ T → Set where
  λx : (e : Expr (Γ ▷ T₁) T₂) → Value (λx e)
  Λα : Value e → Value (Λα e)

data Progress : Expr Γ T → Set where
  done : (v : Value e) → Progress e
  step : (e⟶e′ : e ⟶ e′) → Progress e

NoVar : Ctx n → Set
NoVar ∅ = ⊤
NoVar (Γ ▷ x) = ⊥
NoVar (Γ ▷*) = NoVar Γ

noVar : NoVar Γ → ¬ (Γ ∋ T)
noVar nv (suc* x) = noVar nv x
--! }

--! Progress
progress : NoVar Γ → (e : Expr Γ T) → Progress e
progress nv (` x) = ⊥-elim (noVar nv x)
progress nv (λx e) = done (λx e)
progress nv (e · e₁)
  with progress nv e
... | done (λx e₂) = step β-λ
... | step e⟶e′ = step (ξ-· e⟶e′)
progress nv (Λα e)
  with progress nv e
... | done v = done (Λα v)
... | step e⟶e′ = step (ξ-Λ e⟶e′)
progress nv (e ·* T′)
  with progress nv e
... | done (Λα v) = step β-Λ
... | step e⟶e′ = step (ξ-·* e⟶e′)
