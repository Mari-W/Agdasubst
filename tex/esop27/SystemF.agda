-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --confluence-check --double-check #-}
module SystemF where
open import Agda.Builtin.Equality.Rewrite public

-- standard equational reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning

-- function extensionality (postulated)
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (Fin; zero; suc)

--! SF >
--! Type >
--! Definition
data Type (n : Nat) : Set where
  `_   : Fin n → Type n
  ∀α   : Type (suc n) → Type n
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
  wkᴿ : n →ᴿ suc n
  wkᴿ = suc

  -- identity renaming
  idᴿ : n →ᴿ n
  idᴿ α = α

  -- extend with new variable
  _∙ᴿ_ : Fin n₂ → n₁ →ᴿ n₂ → suc n₁ →ᴿ n₂
  (α ∙ᴿ ζ) zero    = α
  (_ ∙ᴿ ζ) (suc α) = ζ α

  -- apply renaming to variable
  _&ᴿ_ : Fin n₁ → n₁ →ᴿ n₂ → Fin n₂
  α &ᴿ ζ = ζ α

  -- composition
  _⨟ᴿ_ : n₁ →ᴿ n₂ → n₂ →ᴿ n₃ → n₁ →ᴿ n₃
  (ζ₁ ⨟ᴿ ζ₂) α = ζ₂ (ζ₁ α)

-- lifting
_↑ᴿ : n₁ →ᴿ n₂ → suc n₁ →ᴿ suc n₂
_↑ᴿ ζ = zero ∙ᴿ (ζ ⨟ᴿ wkᴿ)

-- apply renaming to type
_[_]ᴿ : Type n₁ → n₁ →ᴿ n₂ → Type n₂
(` α) [ ζ ]ᴿ = ` (α &ᴿ ζ)
(∀α T) [ ζ ]ᴿ = ∀α (T [ ζ ↑ᴿ ]ᴿ)
(T₁ ⇒ T₂) [ ζ ]ᴿ = (T₁ [ ζ ]ᴿ) ⇒ (T₂ [ ζ ]ᴿ)
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
  (T ∙ˢ η) zero    = T
  (T ∙ˢ η) (suc α) = η α

  -- apply substitution to variable
  _&ˢ_ : Fin n₁ → n₁ →ˢ n₂ → Type n₂
  α &ˢ η = η α

  -- lifting
  _↑ˢ : n₁ →ˢ n₂ → suc n₁ →ˢ suc n₂
  _↑ˢ η = (` zero) ∙ˢ λ α → (η α) [ wkᴿ ]ᴿ

-- apply substitution to type
_[_]ˢ : Type n₁ → n₁ →ˢ n₂ → Type n₂
(` α) [ η ]ˢ = α &ˢ η
(∀α T) [ η ]ˢ = ∀α (T [ η ↑ˢ ]ˢ)
(T₁ ⇒ T₂) [ η ]ˢ = (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)

opaque
  -- composition
  _⨟ˢ_ : n₁ →ˢ n₂ → n₂ →ˢ n₃ → n₁ →ˢ n₃
  (η₁ ⨟ˢ η₂) α = (η₁ α) [ η₂ ]ˢ
--! }

variable
  η η′ η₁ η₂ η₃ : n₁ →ˢ n₂

opaque
  unfolding wkᴿ ⟨_⟩ _⨟ˢ_
  -- rewrite system
  -- you probably shouldn't care too much about
  -- the specific system here, it is "the same as in Autosubst"
  -- namely the σₛₚ calculus

  -- importantly: it is locally confluent and terminating
  -- (not complete in the presence of first-class renamings)
  -- thus valid rewrite rules

  -- more importantly, we do not
  -- (by convention, currently not enforced) use (σ _ α)
  -- to look up a variable in a substitution,
  -- but rather use the blocking symbol α [ σ ]ˢ
  -- on which we can rewrite the sigma laws!

  -- first-class renamings
  --! RenamingBeta {
  -- computing renamings
  `beta-ext-zero    : zero  &ᴿ (α ∙ᴿ ζ)         ≡ α
  `beta-ext-suc     : suc α &ᴿ (α′ ∙ᴿ ζ)        ≡ α &ᴿ ζ
  `beta-id          : α &ᴿ idᴿ                  ≡ α
  `beta-wk          : α &ᴿ wkᴿ                  ≡ suc α
  `beta-comp        : α &ᴿ (ζ₁ ⨟ᴿ ζ₂)            ≡ (α &ᴿ ζ₁) &ᴿ ζ₂
  -- interaction between renamings
  `associativity    : (ζ₁ ⨟ᴿ ζ₂) ⨟ᴿ ζ₃            ≡ ζ₁ ⨟ᴿ (ζ₂ ⨟ᴿ ζ₃)
  `distributivity   : (α ∙ᴿ ζ₁) ⨟ᴿ ζ₂            ≡ (α &ᴿ ζ₂) ∙ᴿ (ζ₁ ⨟ᴿ ζ₂)
  `interact         : wkᴿ ⨟ᴿ (α ∙ᴿ ζ)            ≡ ζ
  `comp-idᵣ         : ζ ⨟ᴿ idᴿ                   ≡ ζ
  `comp-idₗ         : idᴿ ⨟ᴿ ζ                   ≡ ζ
  `η-id             : zero {n} ∙ᴿ wkᴿ           ≡ idᴿ
  `η-law            : (zero &ᴿ ζ) ∙ᴿ (wkᴿ ⨟ᴿ ζ)  ≡ ζ
  --! }

  --! SubstitutionBeta {
  -- computing substitutions
  beta-ext-zero     : zero  &ˢ (T ∙ˢ η)              ≡ T
  beta-ext-suc      : suc α &ˢ (T ∙ˢ η)              ≡ α &ˢ η
  beta-rename       : α &ˢ ⟨ ζ ⟩                     ≡ ` (α &ᴿ ζ)
  beta-comp         : α &ˢ (η₁ ⨟ˢ η₂)                 ≡ (α &ˢ η₁) [ η₂ ]ˢ
  beta-lift         : η ↑ˢ                           ≡ (` zero) ∙ˢ (η ⨟ˢ ⟨ wkᴿ ⟩)
  -- interaction between substitutions
  associativity     : (η₁ ⨟ˢ η₂) ⨟ˢ η₃                 ≡ η₁ ⨟ˢ (η₂ ⨟ˢ η₃)
  distributivity    : (T ∙ˢ η₁) ⨟ˢ η₂                 ≡ (T [ η₂ ]ˢ) ∙ˢ (η₁ ⨟ˢ η₂)
  interact          : ⟨ wkᴿ ⟩ ⨟ˢ (T ∙ˢ η)             ≡ η
  comp-idᵣ          : η ⨟ˢ ⟨ idᴿ ⟩                    ≡ η
  comp-idₗ          : ⟨ idᴿ ⟩ ⨟ˢ η                    ≡ η
  η-id              : (` zero {n}) ∙ˢ ⟨ wkᴿ ⟩        ≡ ⟨ idᴿ ⟩
  η-law             : (zero &ˢ η) ∙ˢ (⟨ wkᴿ ⟩ ⨟ˢ η)   ≡ η
  --! }

  -- monad laws
  --! Monad
  -- composing renamings and substitutions
  identityᵣ         : T [ idᴿ ]ᴿ        ≡ T
  compositionalityᴿˢ         : (T [ ζ₁ ]ᴿ) [ η₂ ]ˢ  ≡ T [ ⟨ ζ₁ ⟩ ⨟ˢ η₂ ]ˢ
  compositionalityᴿᴿ         : (T [ ζ₁ ]ᴿ) [ ζ₂ ]ᴿ  ≡ T [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ
  compositionalityˢᴿ         : (T [ η₁ ]ˢ) [ ζ₂ ]ᴿ  ≡ T [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ
  compositionalityˢˢ         : (T [ η₁ ]ˢ) [ η₂ ]ˢ  ≡ T [ η₁ ⨟ˢ η₂ ]ˢ

  -- coincidence laws
  --! Coincidence
  -- transforming substitutions to renamings
  coincidence       : T [ ⟨ ζ ⟩ ]ˢ       ≡ T [ ζ ]ᴿ
  coincidence-comp  : ⟨ ζ₁ ⟩ ⨟ˢ ⟨ ζ₂ ⟩  ≡ ⟨ ζ₁ ⨟ᴿ ζ₂ ⟩

  identityᵣˢ        : T [ ⟨ idᴿ ⟩ ]ˢ     ≡ T

  `beta-ext-zero = refl
  `beta-ext-suc  = refl
  `beta-id       = refl
  `beta-wk       = refl
  `beta-comp     = refl

  `associativity  = refl
  `distributivity = fun-ext λ { zero → refl; (suc α) → refl }
  `interact       = refl
  `comp-idᵣ       = refl
  `comp-idₗ       = refl
  `η-id           = fun-ext λ { zero → refl; (suc α) → refl }
  `η-law          = fun-ext λ { zero → refl; (suc α) → refl }

  beta-ext-zero = refl
  beta-ext-suc  = refl
  beta-rename   = refl
  beta-comp     = refl
  beta-lift     = cong ((` zero) ∙ˢ_) (sym (fun-ext λ x → coincidence))

  associativity {η₁ = η₁} = fun-ext (λ α → compositionalityˢˢ {T = η₁ α})
  distributivity = fun-ext λ { zero → refl; (suc α) → refl }
  interact       = refl
  comp-idᵣ       = fun-ext (λ α → identityᵣˢ)
  comp-idₗ       = refl
  η-id           = fun-ext λ { zero → refl; (suc α) → refl }
  η-law          = fun-ext λ { zero → refl; (suc α) → refl }


  lift-idᴿ : (idᴿ {n}) ↑ᴿ ≡ idᴿ
  lift-idᴿ = fun-ext λ { zero → refl; (suc α) → refl }
  identityᵣ {T = (` α)}      = refl
  identityᵣ {T = (∀α T)}     = cong ∀α (trans (cong (T [_]ᴿ) lift-idᴿ) (identityᵣ {T = T}))
  identityᵣ {T = (T₁ ⇒ T₂)}  = cong₂ _⇒_ (identityᵣ {T = T₁}) (identityᵣ {T = T₂})

  lift-coincidence : ∀ {n₁ n₂} {ζ : n₁ →ᴿ n₂} → (⟨ ζ ⟩ ↑ˢ) ≡ ⟨ ζ ↑ᴿ ⟩
  lift-coincidence = fun-ext λ { zero → refl; (suc α) → refl }

  coincidence {T = ` α}            = refl
  coincidence {T = ∀α T} {ζ = ζ}   = cong ∀α (trans (cong (T [_]ˢ) lift-coincidence) coincidence)
  coincidence {T = T₁ ⇒ T₂}        = cong₂ _⇒_ coincidence coincidence

  coincidence-comp = fun-ext λ α → refl

  lift-compositionalityᴿᴿ : ∀ {n₁ n₂ n₃} {ζ₁ : n₁ →ᴿ n₂} {ζ₂ : n₂ →ᴿ n₃} → (ζ₁ ↑ᴿ) ⨟ᴿ (ζ₂ ↑ᴿ) ≡ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ
  lift-compositionalityᴿᴿ = fun-ext λ { zero → refl; (suc α) → refl }

  compositionalityᴿᴿ {T = ` α}      = refl
  compositionalityᴿᴿ {T = ∀α T}     = cong ∀α (trans compositionalityᴿᴿ (cong (T [_]ᴿ) lift-compositionalityᴿᴿ))
  compositionalityᴿᴿ {T = T₁ ⇒ T₂}  = cong₂ _⇒_ compositionalityᴿᴿ compositionalityᴿᴿ

  lift-compositionalityᴿˢ : ∀ {n₁ n₂ n₃} {ζ₁ : n₁ →ᴿ n₂} {η₂ : n₂ →ˢ n₃} → (⟨ ζ₁ ↑ᴿ ⟩ ⨟ˢ (η₂ ↑ˢ)) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ↑ˢ)
  lift-compositionalityᴿˢ = fun-ext λ { zero → refl; (suc α) → refl }

  compositionalityᴿˢ {T = ` α}      = refl
  compositionalityᴿˢ {T = ∀α T}     = cong ∀α (trans (compositionalityᴿˢ {T = T}) (cong (T [_]ˢ) lift-compositionalityᴿˢ))
  compositionalityᴿˢ {T = T₁ ⇒ T₂}  = cong₂ _⇒_ (compositionalityᴿˢ {T = T₁}) (compositionalityᴿˢ {T = T₂})

  lift-compositionalityˢᴿ : ∀ {n₁ n₂ n₃} {η₁ : n₁ →ˢ n₂} {ζ₂ : n₂ →ᴿ n₃} → ((η₁ ↑ˢ) ⨟ˢ ⟨ ζ₂ ↑ᴿ ⟩) ≡ ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ↑ˢ)
  lift-compositionalityˢᴿ {η₁ = η₁} {ζ₂ = ζ₂} = fun-ext λ { zero → refl; (suc α) →
    let T = η₁ α in
    begin
      (T [ wkᴿ ]ᴿ) [ ⟨ ζ₂ ↑ᴿ ⟩ ]ˢ  ≡⟨ coincidence ⟩
      (T [ wkᴿ ]ᴿ) [ ζ₂ ↑ᴿ ]ᴿ      ≡⟨ compositionalityᴿᴿ ⟩
      T [ wkᴿ ⨟ᴿ (ζ₂ ↑ᴿ) ]ᴿ        ≡⟨ sym compositionalityᴿᴿ ⟩
      (T [ ζ₂ ]ᴿ) [ wkᴿ ]ᴿ         ≡⟨ cong (_[ wkᴿ ]ᴿ) (sym coincidence) ⟩
      (T [ ⟨ ζ₂ ⟩ ]ˢ) [ wkᴿ ]ᴿ     ∎ }

  compositionalityˢᴿ {T = ` α}      = sym coincidence
  compositionalityˢᴿ {T = ∀α T}     = cong ∀α (trans (compositionalityˢᴿ {T = T}) (cong (T [_]ˢ) lift-compositionalityˢᴿ))
  compositionalityˢᴿ {T = T₁ ⇒ T₂}  = cong₂ _⇒_ (compositionalityˢᴿ {T = T₁}) (compositionalityˢᴿ {T = T₂})

  lift-compositionalityˢˢ : ∀ {n₁ n₂ n₃} {η₁ : n₁ →ˢ n₂} {η₂ : n₂ →ˢ n₃} → ((η₁ ↑ˢ) ⨟ˢ (η₂ ↑ˢ)) ≡ ((η₁ ⨟ˢ η₂) ↑ˢ)
  lift-compositionalityˢˢ {η₁ = η₁} {η₂ = η₂} = fun-ext λ { zero → refl; (suc α) →
    let T = η₁ α in
    begin
      (T [ wkᴿ ]ᴿ) [ η₂ ↑ˢ ]ˢ        ≡⟨ compositionalityᴿˢ {T = T} ⟩
      T [ ⟨ wkᴿ ⟩ ⨟ˢ (η₂ ↑ˢ) ]ˢ      ≡⟨ cong (T [_]ˢ) (fun-ext λ α → sym (coincidence {T = η₂ α})) ⟩
      T [ η₂ ⨟ˢ ⟨ wkᴿ ⟩ ]ˢ           ≡⟨ sym (compositionalityˢᴿ {T = T}) ⟩
      (T [ η₂ ]ˢ) [ wkᴿ ]ᴿ           ∎ }

  compositionalityˢˢ {T = ` α}      = refl
  compositionalityˢˢ {T = ∀α T}     = cong ∀α (trans (compositionalityˢˢ {T = T}) (cong (T [_]ˢ) lift-compositionalityˢˢ))
  compositionalityˢˢ {T = T₁ ⇒ T₂}  = cong₂ _⇒_ (compositionalityˢˢ {T = T₁}) (compositionalityˢˢ {T = T₂})

  identityᵣˢ {T = ` α}      = refl
  identityᵣˢ {T = ∀α T}     = cong ∀α (trans (cong (T [_]ˢ) η-id) identityᵣˢ)
  identityᵣˢ {T = T₁ ⇒ T₂}  = cong₂ _⇒_ identityᵣˢ identityᵣˢ

-- more coincidence lemmas ...
-- all follow directly from case analysis
-- (they are extracted from type failures,
--  i did not analyise them)

-- definitely supports the claim that we need
-- a dedicated coincidence solving strategy
opaque
  unfolding wkᴿ ⟨_⟩ _⨟ˢ_
  -- "single substitution under renaming": lifting ζ and post-composing with a
  -- single-substitution `_∙ˢ⟨idᴿ⟩` collapses to direct single substitution
  -- with ζ as the tail. Justifies (T [ T′ ]*) [ ζ ]ᴿ ≡ (T [ ζ ↑ᴿ ]ᴿ) [ T′[ζ]ᴿ ]*.
  coincidence-pop-ᴿ : (⟨ ζ ↑ᴿ ⟩ ⨟ˢ ((T′ [ ζ ]ᴿ) ∙ˢ ⟨ idᴿ ⟩)) ≡ ((T′ [ ζ ]ᴿ) ∙ˢ ⟨ ζ ⟩)
  coincidence-pop-ᴿ = fun-ext λ { zero → refl; (suc α) → refl }
  -- composed-renaming variant of `coincidence-pop-ᴿ`: pulls a `ζ₁ ⨟ᴿ ζ₂` into the
  -- single-sub equation so `(T [ T′ ]*) [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ` reassociates cleanly.
  coincidence-pop-ᴿ-⨟ : ⟨ zero ∙ᴿ (ζ₁ ⨟ᴿ (ζ₂ ⨟ᴿ wkᴿ)) ⟩ ⨟ˢ ((T [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ) ∙ˢ ⟨ idᴿ ⟩) ≡ (T [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ) ∙ˢ (⟨ ζ₁ ⟩ ⨟ˢ ⟨ ζ₂ ⟩)
  coincidence-pop-ᴿ-⨟ = fun-ext λ { zero → refl; (suc α) → refl }
  -- lift fusion in expanded form: composing a renaming-lift `ζ₁ ↑ᴿ` (made manifest
  -- as `zero ∙ᴿ (ζ₁ ⨟ᴿ wkᴿ)`) with a substitution-lift `η₂ ↑ˢ` reassociates.
  -- Aligns the post-beta normal forms of `↑ᴿ ⨟ˢ ↑ˢ` and `↑ˢ`.
  coincidence-↑ᴿ-↑ˢ : ⟨ zero ∙ᴿ (ζ₁ ⨟ᴿ wkᴿ) ⟩ ⨟ˢ ((` zero) ∙ˢ (η₂ ⨟ˢ ⟨ wkᴿ ⟩)) ≡ (` zero) ∙ˢ (⟨ ζ₁ ⟩ ⨟ˢ (η₂ ⨟ˢ ⟨ wkᴿ ⟩))
  coincidence-↑ᴿ-↑ˢ = fun-ext λ { zero → refl; (suc α) → refl }
  coincidence-lemma₄ : (⟨ wkᴿ ⟩ ⨟ˢ ⟨ zero ∙ᴿ (ζ₂ ⨟ᴿ wkᴿ) ⟩) ≡ (⟨ ζ₂ ⟩ ⨟ˢ ⟨ wkᴿ ⟩)
  coincidence-lemma₄ = fun-ext λ { zero → refl; (suc α) → refl }
  -- "single substitution under substitution": substitutional analogue of
  -- `coincidence-pop-ᴿ`. Eliminates the inner `_∙ˢ⟨idᴿ⟩` introduced when pushing
  -- a single-sub `[ T′ ]*` past a composed substitution `η₁ ⨟ˢ ⟨ ζ₂ ⟩`.
  coincidence-pop-ˢ : ((T′ [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ) ∙ˢ (η₁ ⨟ˢ (⟨ ζ₂ ⨟ᴿ wkᴿ ⟩ ⨟ˢ ((T′ [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ) ∙ˢ ⟨ idᴿ ⟩)))) ≡ ((T′ [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ) ∙ˢ (η₁ ⨟ˢ ⟨ ζ₂ ⟩))
  coincidence-pop-ˢ = fun-ext λ { zero → refl; (suc α) → refl }

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
  compositionalityᴿˢ
  compositionalityᴿᴿ
  compositionalityˢᴿ
  compositionalityˢˢ

  coincidence
  coincidence-comp

  coincidence-pop-ᴿ
  coincidence-pop-ᴿ-⨟
  coincidence-↑ᴿ-↑ˢ
  coincidence-pop-ˢ
#-}

idˢ : n →ˢ n
idˢ = ⟨ idᴿ ⟩

-- functorial action
lift*-id1 : α &ᴿ (idᴿ ↑ᴿ) ≡ α
lift*-id1 = refl

lift*-comp1 : α &ᴿ ((ζ′ ⨟ᴿ ζ) ↑ᴿ) ≡ (α &ᴿ (ζ′ ↑ᴿ)) &ᴿ (ζ ↑ᴿ)
lift*-comp1 {α = zero} = refl
lift*-comp1 {α = suc α} = refl

lifts*-id1 : α &ˢ (idˢ ↑ˢ) ≡ ` α
lifts*-id1 = refl

lifts*-comp1 : α &ˢ ((η′ ⨟ˢ η) ↑ˢ) ≡ (α &ˢ (η′ ↑ˢ)) [ η ↑ˢ ]ˢ
lifts*-comp1 {α = zero} = refl
lifts*-comp1 {α = suc α} = refl


--! RenFunctorial {
lift*-id : (idᴿ {n} ↑ᴿ) ≡ idᴿ
lift*-id = refl

lift*-comp : (ζ′ ⨟ᴿ ζ) ↑ᴿ ≡ (ζ′ ↑ᴿ) ⨟ᴿ (ζ ↑ᴿ)
lift*-comp  = refl

ren*-id : T [ idᴿ ]ᴿ ≡ T
ren*-id = refl                  -- *

ren*-comp : T [ ζ′ ⨟ᴿ ζ ]ᴿ ≡ (T [ ζ′ ]ᴿ) [ ζ ]ᴿ
ren*-comp = refl                -- *
--! }

--! SubFunctorial {
lifts*-id : (idˢ {n} ↑ˢ) ≡ idˢ
lifts*-id = refl

lifts*-comp : (η′ ⨟ˢ η) ↑ˢ ≡ (η′ ↑ˢ) ⨟ˢ (η ↑ˢ)
lifts*-comp = refl

sub*-id : T [ idˢ ]ˢ ≡ T
sub*-id = refl

sub*-var : (` α) [ η ]ˢ ≡ α &ˢ η
sub*-var = refl                 -- *

sub*-comp : T [ η ⨟ˢ η′ ]ˢ ≡ (T [ η ]ˢ) [ η′ ]ˢ
sub*-comp = refl                -- *
--! }

--! Weaken
weaken : Type n → Type (suc n)
weaken T = T [ wkᴿ ]ᴿ

--! Subzero
_[_]* : Type (suc n) → Type n → Type n
T [ T′ ]* = T [ T′ ∙ˢ idˢ ]ˢ

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
ζ ∣ Γ₁ ⇒ᴿ Γ₂ = ∀ T → Γ₁ ∋ T → Γ₂ ∋ (T [ ζ ]ᴿ)

variable
  ρ ρ′ ρ₁ ρ₂ ρ₃ : ζ ∣ Γ₁ ⇒ᴿ Γ₂

--! Ren >
--! Idr
Idᴿ : idᴿ ∣ Γ ⇒ᴿ Γ
Idᴿ _ x = x

--! Weakening
Wkᴿ : ∀ T → idᴿ ∣ Γ ⇒ᴿ (Γ ▷ T)
Wkᴿ _ _ = suc

--! TWeakening
wkᴿ* : wkᴿ ∣ Γ ⇒ᴿ (Γ ▷*)
wkᴿ* _ x = suc* x

--! Composition
_,_∣_⨾ᴿ_ : ∀ ζ₁ ζ₂ → ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ζ₁ ⨟ᴿ ζ₂) ∣ Γ₁ ⇒ᴿ Γ₃
(_ , _ ∣ ρ₁ ⨾ᴿ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_⨾ᴿ_ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ζ₁ ⨟ᴿ ζ₂) ∣ Γ₁ ⇒ᴿ Γ₃
_⨾ᴿ_ = _,_∣_⨾ᴿ_ _ _

--! Extension
_∣_∙ᴿ_ : ∀ ζ → Γ₂ ∋ (T [ ζ ]ᴿ) → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ Γ₂
(_ ∣ x ∙ᴿ ρ) _ zero     = x
(_ ∣ _ ∙ᴿ ρ) _ (suc x)  = ρ _ x

-- _∣_∙ᴿ*_ : ∀ ζ x → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (x ∙ᴿ ζ) ∣ (Γ₁ ▷*) ⇒ᴿ Γ₂
-- (_ ∣ _ ∙ᴿ* ρ) _ (suc* x) = ρ _ x

--! Lifting
_∣_⇑ᴿ_ : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ ζ ]ᴿ))
(ζ ∣ ρ ⇑ᴿ _) = ζ ∣ zero ∙ᴿ (ζ , idᴿ ∣ ρ ⨾ᴿ (Wkᴿ _))

_⇑ᴿ_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ ζ ]ᴿ))
_⇑ᴿ_ = _ ∣_⇑ᴿ_

--! TLifting
_∣_↑ᴿ* : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (ζ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
(_ ∣ ρ ↑ᴿ*) _ (suc* x) = suc* (ρ _ x)

↑ᴿ*_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (ζ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
↑ᴿ*_ = _ ∣_↑ᴿ*

-- new symbol?
--! Traversal
_∣_[_]ᴿ : (ζ : n₁ →ᴿ n₂) → Expr Γ₁ T → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → Expr Γ₂ (T [ ζ ]ᴿ)
_  ∣ (` x) [ ρ ]ᴿ  = ` (ρ _ x)
_  ∣ (λx e) [ ρ ]ᴿ  = λx (_ ∣ e [ ρ ⇑ᴿ _ ]ᴿ)
_  ∣ (Λα e) [ ρ ]ᴿ  = Λα (_ ∣ e [ ↑ᴿ* ρ ]ᴿ)
_  ∣ (e₁ · e₂) [ ρ ]ᴿ  = (_ ∣ e₁ [ ρ ]ᴿ) · (_ ∣ e₂ [ ρ ]ᴿ)
ζ  ∣ (e ·* T′) [ ρ ]ᴿ  = (ζ ∣ e [ ρ ]ᴿ) ·* (T′ [ ζ ]ᴿ)

Weaken : Expr Γ T → Expr (Γ ▷ T′) T
Weaken e = idᴿ ∣ e [ Wkᴿ _ ]ᴿ

weaken* : Expr Γ T → Expr (Γ ▷*) (weaken T)
weaken* e = wkᴿ ∣ e [ wkᴿ* ]ᴿ

--! <
--! Substitution
_∣_⇒ˢ_ : n₁ →ˢ n₂ → Ctx n₁ → Ctx n₂ → Set
η ∣ Γ₁ ⇒ˢ Γ₂ = ∀ T → Γ₁ ∋ T → Expr Γ₂ (T [ η ]ˢ)

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
Idˢ _ = `_

Wkˢ : ∀ T → ⟨ idᴿ ⟩ ∣ Γ ⇒ˢ (Γ ▷ T)
Wkˢ _ = idᴿ ∣⟪ Wkᴿ _ ⟫

wkᴿ*ˢ : ⟨ wkᴿ ⟩ ∣ Γ ⇒ˢ (Γ ▷*)
wkᴿ*ˢ = wkᴿ ∣⟪ wkᴿ* ⟫

-- extending a substitution
-- new symbol?
--! Extension
_∣_∙ˢ_ : ∀ η → Expr Γ₂ (T [ η ]ˢ) → η ∣ Γ₁ ⇒ˢ Γ₂ → η ∣ (Γ₁ ▷ T) ⇒ˢ Γ₂
(_ ∣ e ∙ˢ σ) _ zero     = e
(_ ∣ e ∙ˢ σ) _ (suc x)  = σ _ x

_∣_∙ˢ*_ : ∀ η T → η ∣ Γ₁ ⇒ˢ Γ₂ → (T ∙ˢ η) ∣ (Γ₁ ▷*) ⇒ˢ Γ₂
(_ ∣ T ∙ˢ* σ) _ (suc* x) = σ _ x

-- lifting a substitution
--! Lifting
_∣_⇑ˢ_ : ∀ η → η ∣ Γ₁ ⇒ˢ Γ₂ → ∀ T → η ∣ (Γ₁ ▷ T) ⇒ˢ (Γ₂ ▷ (T [ η ]ˢ))
η ∣ σ ⇑ˢ T = η ∣ (` zero) ∙ˢ λ _ x → idᴿ ∣ (σ _ x) [ Wkᴿ _ ]ᴿ

-- type lifting
--! TLifting
_∣_↑ˢ* : ∀ η → η ∣ Γ₁ ⇒ˢ Γ₂ → (η ↑ˢ) ∣ (Γ₁ ▷*) ⇒ˢ (Γ₂ ▷*)
(η ∣ σ ↑ˢ*) _ (suc* x) = _ ∣ (σ _ x) [ wkᴿ* ]ᴿ

-- expression substitution - traversal
-- new symbol?
--! Traversal
_∣_[_]ˢ : (η : n₁ →ˢ n₂) → Expr Γ₁ T → η ∣ Γ₁ ⇒ˢ Γ₂ → Expr Γ₂ (T [ η ]ˢ)
η  ∣ (` x) [ σ ]ˢ  = σ _ x
η  ∣ (λx e) [ σ ]ˢ  = λx (η ∣ e [ η ∣ σ ⇑ˢ _ ]ˢ)
η  ∣ (Λα e) [ σ ]ˢ  = Λα ((η ↑ˢ) ∣ e [ η ∣ σ ↑ˢ* ]ˢ)
η  ∣ (e · e₁) [ σ ]ˢ  = (η ∣ e [ σ ]ˢ) · (η ∣ e₁ [ σ ]ˢ)
η  ∣ (e ·* T′) [ σ ]ˢ  = (η ∣ e [ σ ]ˢ) ·* (T′ [ η ]ˢ)

--! CompDefinition
_,_∣_⨾ˢ_ : ∀ η₁ η₂ → η₁ ∣ Γ₁ ⇒ˢ Γ₂ → η₂ ∣ Γ₂ ⇒ˢ Γ₃ → (η₁ ⨟ˢ η₂) ∣ Γ₁ ⇒ˢ Γ₃
(_ , _ ∣ σ₁ ⨾ˢ σ₂) _ x = _ ∣ (σ₁ _ x) [ σ₂ ]ˢ

opaque
  η-Id : ⟨ idᴿ ⟩ ∣ (` (zero {Γ = Γ} {T = T})) ∙ˢ (Wkˢ T) ≡ (Idˢ {Γ = Γ ▷ T})
  η-Id = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  η*-Id : ⟨ idᴿ ⟩ ∣ (Idˢ {Γ = Γ}) ↑ˢ* ≡ Idˢ
  η*-Id = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Identityᵣ : ∀ (e : Expr Γ T) → ⟨ idᴿ ⟩ ∣ e [ Idˢ ]ˢ ≡ e
  Identityᵣ (` x)      = refl
  Identityᵣ (λx e)     = cong λx (trans (cong (⟨ idᴿ ⟩ ∣ e [_]ˢ) η-Id) (Identityᵣ e))
  Identityᵣ (Λα e)     = cong Λα (trans (cong (⟨ idᴿ ⟩ ∣ e [_]ˢ) η*-Id) (Identityᵣ e))
  Identityᵣ (e₁ · e₂)  = cong₂ _·_ (Identityᵣ e₁) (Identityᵣ e₂)
  Identityᵣ (e ·* T′)  = cong (_·* T′) (Identityᵣ e)

  Lift-Dist-Compᴿᴿ : (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    ζ₁ , ζ₂ ∣ (ζ₁ ∣ ρ₁ ⇑ᴿ T) ⨾ᴿ (ζ₂ ∣ ρ₂ ⇑ᴿ (T [ ζ₁ ]ᴿ)) ≡ ((ζ₁ ⨟ᴿ ζ₂) ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ⇑ᴿ T)
  Lift-Dist-Compᴿᴿ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  lift*-dist-Compᴿᴿ : (ζ₁ : n₁ →ᴿ n₂) (ζ₂ : n₂ →ᴿ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    (ζ₁ ↑ᴿ) , (ζ₂ ↑ᴿ) ∣ (ζ₁ ∣ ρ₁ ↑ᴿ*) ⨾ᴿ (ζ₂ ∣ ρ₂ ↑ᴿ*) ≡ ((ζ₁ ⨟ᴿ ζ₂) ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ↑ᴿ*)
  lift*-dist-Compᴿᴿ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Compositionalityᴿᴿ : ∀ (e : Expr Γ₁ T) (ζ₁ : n₁ →ᴿ n₂) (ζ₂ : n₂ →ᴿ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    ζ₂ ∣ (ζ₁ ∣ e [ ρ₁ ]ᴿ) [ ρ₂ ]ᴿ ≡ (ζ₁ ⨟ᴿ ζ₂) ∣ e [ ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂ ]ᴿ
  Compositionalityᴿᴿ (` x)     _  _  _  _  = refl
  Compositionalityᴿᴿ (λx e)    _  _  _  _  = cong λx (trans (Compositionalityᴿᴿ e _ _ _ _) (cong (_ ∣ e [_]ᴿ) (Lift-Dist-Compᴿᴿ _ _)))
  Compositionalityᴿᴿ (Λα e)    _  _  _  _  = cong Λα (trans (Compositionalityᴿᴿ e _ _ _ _) (cong (_ ∣ e [_]ᴿ) (lift*-dist-Compᴿᴿ _ _ _ _)))
  Compositionalityᴿᴿ (e₁ · e₂) _  _  _  _  = cong₂ _·_ (Compositionalityᴿᴿ e₁ _ _ _ _) (Compositionalityᴿᴿ e₂ _ _ _ _)
  Compositionalityᴿᴿ (e ·* T′) ζ₁ ζ₂ ρ₁ ρ₂ = cong (_·* (T′ [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ)) (Compositionalityᴿᴿ e _ _ _ _)

  Lift-Dist-Compᴿˢ : (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    ⟨ ζ₁ ⟩ , η₂ ∣ (ζ₁ ∣⟪ ζ₁ ∣ ρ₁ ⇑ᴿ T ⟫) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ (T [ ζ₁ ]ᴿ)) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ (⟨ ζ₁ ⟩ , η₂ ∣ ζ₁ ∣⟪ ρ₁ ⟫ ⨾ˢ σ₂) ⇑ˢ T)
  Lift-Dist-Compᴿˢ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  lift*-dist-Compᴿˢ : (ζ₁ : n₁ →ᴿ n₂) (η₂ : n₂ →ˢ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    ⟨ ζ₁ ↑ᴿ ⟩ , (η₂ ↑ˢ) ∣ ((ζ₁ ↑ᴿ ∣⟪ ζ₁ ∣ ρ₁ ↑ᴿ* ⟫)) ⨾ˢ (η₂ ∣ σ₂ ↑ˢ*) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ (⟨ ζ₁ ⟩ , η₂ ∣ ζ₁ ∣⟪ ρ₁ ⟫ ⨾ˢ σ₂) ↑ˢ*)
  lift*-dist-Compᴿˢ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Compositionalityᴿˢ : ∀ (e : Expr Γ₁ T) (ζ₁ : n₁ →ᴿ n₂) (η₂ : n₂ →ˢ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    η₂ ∣ (ζ₁ ∣ e [ ρ₁ ]ᴿ) [ σ₂ ]ˢ ≡ (⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ e [ ⟨ ζ₁ ⟩ , η₂ ∣ ζ₁ ∣⟪ ρ₁ ⟫ ⨾ˢ σ₂ ]ˢ
  Compositionalityᴿˢ (` x)     _  _  _  _  = refl
  Compositionalityᴿˢ (λx e)    ζ₁ η₂ ρ₁ σ₂ = cong λx (trans (Compositionalityᴿˢ e _ _ _ _) (cong ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ e [_]ˢ) (Lift-Dist-Compᴿˢ ρ₁ σ₂)))
  Compositionalityᴿˢ (Λα e)    ζ₁ η₂ ρ₁ σ₂ = cong Λα (trans (Compositionalityᴿˢ e _ _ _ _) (cong (((⟨ ζ₁ ⟩ ⨟ˢ η₂) ↑ˢ) ∣ e [_]ˢ) (lift*-dist-Compᴿˢ _ η₂ ρ₁ σ₂)))
  Compositionalityᴿˢ (e₁ · e₂) _  _  _  _  = cong₂ _·_ (Compositionalityᴿˢ e₁ _ _ _ _) (Compositionalityᴿˢ e₂ _ _ _ _)
  Compositionalityᴿˢ (e ·* T′) ζ₁ η₂ ρ₁ ρ₂ = cong (_·* (T′ [ ⟨ ζ₁ ⟩ ⨟ˢ η₂ ]ˢ)) (Compositionalityᴿˢ e _ _ _ _)

  η-Idᴿ : idᴿ ∣ (zero {Γ = Γ} {T = T}) ∙ᴿ (Wkᴿ T) ≡ (Idᴿ {Γ = Γ ▷ T})
  η-Idᴿ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  η*-Idᴿ : idᴿ ∣ (Idᴿ {Γ = Γ}) ↑ᴿ* ≡ Idᴿ
  η*-Idᴿ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Coincidence : ∀ (e : Expr Γ₁ T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
      ⟨ ζ ⟩ ∣ e [ ζ ∣⟪ ρ ⟫ ]ˢ ≡ (ζ ∣ e [ ρ ]ᴿ)
  Coincidence e ρ = begin
      _  ≡⟨ sym (Compositionalityᴿˢ e _ _ ρ Idˢ) ⟩
      _  ≡⟨ Identityᵣ (_ ∣ e [ ρ ]ᴿ) ⟩
      _  ∎

Lift-Dist-Compˢᴿ : (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  η₁ , ⟨ ζ₂ ⟩ ∣ (η₁ ∣ σ₁ ⇑ˢ T) ⨾ˢ (ζ₂ ∣⟪ ζ₂ ∣ ρ₂ ⇑ᴿ (T [ η₁ ]ˢ) ⟫) ≡ ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ˢ (ζ₂ ∣⟪ ρ₂ ⟫)) ⇑ˢ T)
Lift-Dist-Compˢᴿ σ₁ ρ₂ = fun-ext λ _ → fun-ext λ
  { zero → refl; (suc x) →
    let e = σ₁ _ x in begin
      _  ≡⟨ Coincidence (idᴿ ∣ e [ Wkᴿ _ ]ᴿ) _ ⟩
      _  ≡⟨ Compositionalityᴿᴿ e idᴿ _ _ _ ⟩
      _  ≡⟨ sym (Compositionalityᴿᴿ e _ idᴿ ρ₂ (Wkᴿ _)) ⟩
      _  ≡⟨ cong (idᴿ ∣_[ Wkᴿ _ ]ᴿ) (sym (Coincidence e _)) ⟩
      _  ∎ }

lift*-dist-Compˢᴿ : (η₁ : n₁ →ˢ n₂) (ζ₂ : n₂ →ᴿ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  (η₁ ↑ˢ) , ⟨ ζ₂ ↑ᴿ ⟩ ∣ (η₁ ∣ σ₁ ↑ˢ*) ⨾ˢ ((ζ₂ ↑ᴿ) ∣⟪ ζ₂ ∣ ρ₂ ↑ᴿ* ⟫) ≡ (η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ˢ (ζ₂ ∣⟪ ρ₂ ⟫)) ↑ˢ*
lift*-dist-Compˢᴿ η₁ ζ₂ σ₁ ρ₂ = fun-ext λ _ → fun-ext λ
  { (suc* x) →
    let e = σ₁ _ x in begin
      _  ≡⟨ Coincidence (wkᴿ ∣ e [ wkᴿ* ]ᴿ) (ζ₂ ∣ ρ₂ ↑ᴿ*) ⟩
      _  ≡⟨ Compositionalityᴿᴿ e _ _ wkᴿ* (ζ₂ ∣ ρ₂ ↑ᴿ*) ⟩
      _  ≡⟨ sym (Compositionalityᴿᴿ e _ _ ρ₂ wkᴿ*) ⟩
      _  ≡⟨ cong (wkᴿ ∣_[ wkᴿ* ]ᴿ) (sym (Coincidence e _)) ⟩
      _  ∎ }

Compositionalityˢᴿ : ∀ (e : Expr Γ₁ T) (η₁ : n₁ →ˢ n₂) (ζ₂ : n₂ →ᴿ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  ζ₂ ∣ (η₁ ∣ e [ σ₁ ]ˢ) [ ρ₂ ]ᴿ ≡ (η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ e [ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ˢ (ζ₂ ∣⟪ ρ₂ ⟫)) ]ˢ
Compositionalityˢᴿ (` x)     _  _  σ₁ _  = sym (Coincidence (σ₁ _ x) _)
Compositionalityˢᴿ (λx e)    η₁ ζ₂ σ₁ ρ₂ = cong λx (trans (Compositionalityˢᴿ e _ _ _ _) (cong ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ e [_]ˢ) (Lift-Dist-Compˢᴿ σ₁ ρ₂)))
Compositionalityˢᴿ (Λα e)    η₁ ζ₂ σ₁ ρ₂ = cong Λα (trans (Compositionalityˢᴿ e _ _ _ _) (cong (((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ↑ˢ) ∣ e [_]ˢ) (lift*-dist-Compˢᴿ η₁ ζ₂ σ₁ ρ₂)))
Compositionalityˢᴿ (e₁ · e₂) _  _  _  _  = cong₂ _·_ (Compositionalityˢᴿ e₁ _ _ _ _) (Compositionalityˢᴿ e₂ _ _ _ _)
Compositionalityˢᴿ (e ·* T′) η₁ ζ₂ σ₁ ρ₂ = cong (_·* (T′ [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ)) (Compositionalityˢᴿ e η₁ ζ₂ σ₁ ρ₂)

Lift-Dist-Compˢˢ : (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  η₁ , η₂ ∣ (η₁ ∣ σ₁ ⇑ˢ T) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ (T [ η₁ ]ˢ)) ≡ ((η₁ ⨟ˢ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ⇑ˢ T)
Lift-Dist-Compˢˢ σ₁ σ₂ = fun-ext λ _ → fun-ext λ
  { zero → refl; (suc x) →
    let e = σ₁ _ x in begin
      _  ≡⟨ Compositionalityᴿˢ e _ _ _ _ ⟩
      _  ≡⟨ cong (_ ∣ e [_]ˢ) (fun-ext (λ _ → fun-ext λ x → sym (Coincidence (σ₂ _ x) _))) ⟩
      _  ≡⟨ sym (Compositionalityˢᴿ e _ idᴿ σ₂ (Wkᴿ _)) ⟩
      _  ∎ }

lift*-dist-Compˢˢ : (η₁ : n₁ →ˢ n₂) (η₂ : n₂ →ˢ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  (η₁ ↑ˢ) , (η₂ ↑ˢ) ∣ (η₁ ∣ σ₁ ↑ˢ*) ⨾ˢ (η₂ ∣ σ₂ ↑ˢ*) ≡ ((η₁ ⨟ˢ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ↑ˢ*)
lift*-dist-Compˢˢ _ η₂ σ₁ σ₂ = fun-ext λ _ → fun-ext λ
  { (suc* x) →
    let e = σ₁ _ x in begin
      _  ≡⟨ Compositionalityᴿˢ e _ _ _ _ ⟩
      _  ≡⟨ cong ((η₂ ⨟ˢ ⟨ wkᴿ ⟩) ∣ e [_]ˢ) (fun-ext (λ _ → fun-ext λ { x → sym (Coincidence (σ₂ _ x) wkᴿ*) })) ⟩
      _  ≡⟨ sym (Compositionalityˢᴿ e _ wkᴿ σ₂ wkᴿ*) ⟩
      _  ∎ }

--! CompositionalityType
Compositionalityˢˢ : ∀ (e : Expr Γ₁ T) (η₁ : n₁ →ˢ n₂) (η₂ : n₂ →ˢ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  η₂ ∣ (η₁ ∣ e [ σ₁ ]ˢ) [ σ₂ ]ˢ ≡ (η₁ ⨟ˢ η₂) ∣ e [ η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂ ]ˢ

--! CompositionalityBody
Compositionalityˢˢ (` x)      η₁ η₂ σ₁ σ₂  = refl
Compositionalityˢˢ (λx e)     η₁ η₂ σ₁ σ₂  = cong λx (begin
    _  ≡⟨ Compositionalityˢˢ e η₁ η₂ (η₁ ∣ σ₁ ⇑ˢ _) (η₂ ∣ σ₂ ⇑ˢ _) ⟩
    _  ≡⟨ cong ((η₁ ⨟ˢ η₂) ∣ e [_]ˢ) (Lift-Dist-Compˢˢ σ₁ σ₂) ⟩
    _  ∎)
Compositionalityˢˢ (Λα e)     η₁ η₂ σ₁ σ₂  = cong Λα (begin
    _  ≡⟨ Compositionalityˢˢ e (η₁ ↑ˢ) (η₂ ↑ˢ) (η₁ ∣ σ₁ ↑ˢ*) (η₂ ∣ σ₂ ↑ˢ*) ⟩
    _  ≡⟨ cong (((η₁ ⨟ˢ η₂) ↑ˢ) ∣ e [_]ˢ) (lift*-dist-Compˢˢ η₁ η₂ σ₁ σ₂) ⟩
    _  ∎)
Compositionalityˢˢ (e₁ · e₂)  η₁ η₂ σ₁ σ₂  = cong₂ _·_ (Compositionalityˢˢ e₁ η₁ η₂ σ₁ σ₂) (Compositionalityˢˢ e₂ η₁ η₂ σ₁ σ₂)
Compositionalityˢˢ (e ·* T′)  η₁ η₂ σ₁ σ₂  = cong (_·* (T′ [ η₁ ⨟ˢ η₂ ]ˢ)) (Compositionalityˢˢ e η₁ η₂ σ₁ σ₂)

-- single substitution, semantics, and progress
--! <
--! Sem >
--! SingleSub {
_[_] : Expr (Γ ▷ T′) T → Expr Γ T′ → Expr Γ T
e [ e′ ] = idˢ ∣ e [ idˢ ∣ e′ ∙ˢ Idˢ ]ˢ

_[*_*] : Expr (Γ ▷*) T → (T′ : Type n) → Expr Γ (T [ T′ ]*)
e [* T′ *] = (T′ ∙ˢ idˢ) ∣ e [ idˢ ∣ T′ ∙ˢ* Idˢ ]ˢ
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
open import Relation.Nullary using (¬_)

--! ProgressDefs {
data Value : Expr Γ T → Set where
  λx : (e : Expr (Γ ▷ T₁) T₂) → Value (λx e)
  Λα : Value e → Value (Λα e)

data Progress : Expr Γ T → Set where
  done : (v : Value e) → Progress e
  step : (e⟶e′ : e ⟶ e′) → Progress e

NoVar : Ctx n → Set
NoVar ∅        = ⊤
NoVar (Γ ▷ T)  = ⊥
NoVar (Γ ▷*)   = NoVar Γ

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
