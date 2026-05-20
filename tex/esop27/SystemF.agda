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

  -- importantly: it is confluent and terminating
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


--! SubFunctorialLift {
lifts*-id : (idˢ {n} ↑ˢ) ≡ idˢ
lifts*-id = refl

lifts*-comp : (η′ ⨟ˢ η) ↑ˢ ≡ (η′ ↑ˢ) ⨟ˢ (η ↑ˢ)
lifts*-comp = refl
--! }

--! SubFunctorialApply {
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
opaque
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

  --! Extension
  _∣_∙ᴿ_ : ∀ ζ → Γ₂ ∋ (T [ ζ ]ᴿ) → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ Γ₂
  (_ ∣ x ∙ᴿ ρ) _ zero     = x
  (_ ∣ _ ∙ᴿ ρ) _ (suc x)  = ρ _ x

  _∣_∙ᴿ*_ : ∀ ξ x → ξ ∣ Γ₁ ⇒ᴿ Γ₂ → (x ∙ᴿ ξ) ∣ (Γ₁ ▷*) ⇒ᴿ Γ₂
  (_ ∣ _ ∙ᴿ* ρ) _ (suc* x) = ρ _ x

  --! Lookup
  -- blocking alias for "apply renaming to variable" — analog of `_&ᴿ_` at type level
  _∣_&ᴿ_ : ∀ ζ → Γ₁ ∋ T → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → Γ₂ ∋ (T [ ζ ]ᴿ)
  ζ ∣ x &ᴿ ρ = ρ _ x

_⨾ᴿ_ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ζ₁ ⨟ᴿ ζ₂) ∣ Γ₁ ⇒ᴿ Γ₃
_⨾ᴿ_ {ζ₁ = ζ₁} {ζ₂ = ζ₂} ρ₁ ρ₂ = (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂)

-- _∣_∙ᴿ*_ : ∀ ζ x → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (x ∙ᴿ ζ) ∣ (Γ₁ ▷*) ⇒ᴿ Γ₂
-- (_ ∣ _ ∙ᴿ* ρ) _ (suc* x) = ρ _ x

--! Lifting
opaque
  _∣_⇑ᴿ_ : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ ζ ]ᴿ))
  (ζ ∣ ρ ⇑ᴿ _) = ζ ∣ zero ∙ᴿ (ζ , idᴿ ∣ ρ ⨾ᴿ (Wkᴿ _))

  --! TLifting
  _∣_↑ᴿ* : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (ζ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
  (ζ ∣ ρ ↑ᴿ*) = (ζ ⨟ᴿ wkᴿ) ∣ zero ∙ᴿ* (ζ , wkᴿ ∣ ρ ⨾ᴿ wkᴿ*)

_⇑ᴿ_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ ζ ]ᴿ))
_⇑ᴿ_ = _ ∣_⇑ᴿ_

↑ᴿ*_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (ζ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
↑ᴿ*_ = _ ∣_↑ᴿ*

-- new symbol?
--! Traversal
opaque
  _∣_[_]ᴿ : (ζ : n₁ →ᴿ n₂) → Expr Γ₁ T → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → Expr Γ₂ (T [ ζ ]ᴿ)
  ζ  ∣ (` x) [ ρ ]ᴿ  = ` (ζ ∣ x &ᴿ ρ)
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

opaque
  -- raising a renaming to a substitution
  _∣⟪_⟫ : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
  (ζ ∣⟪ ρ ⟫) _ x = ` ρ _ x

  --! Ids
  Idˢ : idˢ ∣ Γ ⇒ˢ Γ
  Idˢ _ = `_

  Wkˢ : ∀ T → ⟨ idᴿ ⟩ ∣ Γ ⇒ˢ (Γ ▷ T)
  Wkˢ _ = idᴿ ∣⟪ Wkᴿ _ ⟫

  wkᴿ*ˢ : ⟨ wkᴿ ⟩ ∣ Γ ⇒ˢ (Γ ▷*)
  wkᴿ*ˢ = wkᴿ ∣⟪ wkᴿ* ⟫

  -- extending a substitution
  --! Extension
  _∣_∙ˢ_ : ∀ η → Expr Γ₂ (T [ η ]ˢ) → η ∣ Γ₁ ⇒ˢ Γ₂ → η ∣ (Γ₁ ▷ T) ⇒ˢ Γ₂
  (_ ∣ e ∙ˢ σ) _ zero     = e
  (_ ∣ e ∙ˢ σ) _ (suc x)  = σ _ x

  _∣_∙ˢ*_ : ∀ η T → η ∣ Γ₁ ⇒ˢ Γ₂ → (T ∙ˢ η) ∣ (Γ₁ ▷*) ⇒ˢ Γ₂
  (_ ∣ T ∙ˢ* σ) _ (suc* x) = σ _ x

  --! Lookup
  -- blocking alias for "apply substitution to variable" — analog of `_&ˢ_` at type level
  _∣_&ˢ_ : ∀ η → Γ₁ ∋ T → η ∣ Γ₁ ⇒ˢ Γ₂ → Expr Γ₂ (T [ η ]ˢ)
  η ∣ x &ˢ σ = σ _ x

  -- lifting a substitution
  --! Lifting
  _∣_⇑ˢ_ : ∀ η → η ∣ Γ₁ ⇒ˢ Γ₂ → ∀ T → η ∣ (Γ₁ ▷ T) ⇒ˢ (Γ₂ ▷ (T [ η ]ˢ))
  η ∣ σ ⇑ˢ T = η ∣ (` zero) ∙ˢ λ _ x → idᴿ ∣ (σ _ x) [ Wkᴿ _ ]ᴿ

  -- type lifting
  --! TLifting
  _∣_↑ˢ* : ∀ η → η ∣ Γ₁ ⇒ˢ Γ₂ → (η ↑ˢ) ∣ (Γ₁ ▷*) ⇒ˢ (Γ₂ ▷*)
  (η ∣ σ ↑ˢ*) = (η ⨟ˢ ⟨ wkᴿ ⟩) ∣ (` zero) ∙ˢ* λ _ x → wkᴿ ∣ (σ _ x) [ wkᴿ* ]ᴿ

⟪_⟫ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
⟪_⟫ = _ ∣⟪_⟫


-- expression substitution - traversal
-- new symbol?
opaque
  --! Traversal
  _∣_[_]ˢ : (η : n₁ →ˢ n₂) → Expr Γ₁ T → η ∣ Γ₁ ⇒ˢ Γ₂ → Expr Γ₂ (T [ η ]ˢ)
  η  ∣ (` x) [ σ ]ˢ      = η ∣ x &ˢ σ
  η  ∣ (λx e) [ σ ]ˢ     = λx (η ∣ e [ η ∣ σ ⇑ˢ _ ]ˢ)
  η  ∣ (Λα e) [ σ ]ˢ     = Λα ((η ↑ˢ) ∣ e [ η ∣ σ ↑ˢ* ]ˢ)
  η  ∣ (e · e₁) [ σ ]ˢ   = (η ∣ e [ σ ]ˢ) · (η ∣ e₁ [ σ ]ˢ)
  η  ∣ (e ·* T′) [ σ ]ˢ  = (η ∣ e [ σ ]ˢ) ·* (T′ [ η ]ˢ)

opaque
  --! CompDefinition
  _,_∣_⨾ˢ_ : ∀ η₁ η₂ → η₁ ∣ Γ₁ ⇒ˢ Γ₂ → η₂ ∣ Γ₂ ⇒ˢ Γ₃ → (η₁ ⨟ˢ η₂) ∣ Γ₁ ⇒ˢ Γ₃
  (_ , _ ∣ σ₁ ⨾ˢ σ₂) _ x = _ ∣ (σ₁ _ x) [ σ₂ ]ˢ

_⨾ˢ_ : η₁ ∣ Γ₁ ⇒ˢ Γ₂ → η₂ ∣ Γ₂ ⇒ˢ Γ₃ → (η₁ ⨟ˢ η₂) ∣ Γ₁ ⇒ˢ Γ₃
_⨾ˢ_ {η₁ = η₁} {η₂ = η₂} σ₁ σ₂ = (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂)

opaque
  unfolding Idᴿ Wkᴿ wkᴿ* _,_∣_⨾ᴿ_ _∣_∙ᴿ_ _∣_∙ᴿ*_ _∣_&ᴿ_ _∣_⇑ᴿ_ _∣_↑ᴿ* _∣_[_]ᴿ _∣⟪_⟫ Idˢ Wkˢ wkᴿ*ˢ _∣_∙ˢ_ _∣_∙ˢ*_ _,_∣_⨾ˢ_ _∣_&ˢ_ _∣_⇑ˢ_ _∣_↑ˢ* _∣_[_]ˢ
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

opaque
  unfolding Idᴿ Wkᴿ wkᴿ* _,_∣_⨾ᴿ_ _∣_∙ᴿ_ _∣_∙ᴿ*_ _∣_&ᴿ_ _∣_⇑ᴿ_ _∣_↑ᴿ* _∣_[_]ᴿ _∣⟪_⟫ Idˢ Wkˢ wkᴿ*ˢ _∣_∙ˢ_ _∣_∙ˢ*_ _,_∣_⨾ˢ_ _∣_&ˢ_ _∣_⇑ˢ_ _∣_↑ˢ* _∣_[_]ˢ

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
  Compositionalityˢˢ (λx {T₁ = T₁} e)     η₁ η₂ σ₁ σ₂  = cong λx (begin
        η₂ ∣ η₁ ∣ e [ η₁ ∣ σ₁ ⇑ˢ T₁ ]ˢ [ η₂ ∣ σ₂ ⇑ˢ (T₁ [ η₁ ]ˢ) ]ˢ
      ≡⟨ Compositionalityˢˢ e η₁ η₂ (η₁ ∣ σ₁ ⇑ˢ T₁) (η₂ ∣ σ₂ ⇑ˢ (T₁ [ η₁ ]ˢ)) ⟩
        (η₁ ⨟ˢ η₂) ∣ e [  η₁ , η₂ ∣ η₁ ∣ σ₁ ⇑ˢ T₁ ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ (T₁ [ η₁ ]ˢ)) ]ˢ
      ≡⟨ cong ((η₁ ⨟ˢ η₂) ∣ e [_]ˢ) (Lift-Dist-Compˢˢ σ₁ σ₂) ⟩
        (η₁ ⨟ˢ η₂) ∣ e [ (η₁ ⨟ˢ η₂) ∣ η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂ ⇑ˢ T₁ ]ˢ
      ∎)
  Compositionalityˢˢ (Λα e)     η₁ η₂ σ₁ σ₂  = cong Λα (begin
        (η₂ ↑ˢ) ∣ (η₁ ↑ˢ) ∣ e [ η₁ ∣ σ₁ ↑ˢ* ]ˢ [ η₂ ∣ σ₂ ↑ˢ* ]ˢ
      ≡⟨ Compositionalityˢˢ e (η₁ ↑ˢ) (η₂ ↑ˢ) (η₁ ∣ σ₁ ↑ˢ*) (η₂ ∣ σ₂ ↑ˢ*) ⟩
        ((η₁ ⨟ˢ η₂) ↑ˢ) ∣ e [ (η₁ ↑ˢ) , η₂ ↑ˢ ∣ η₁ ∣ σ₁ ↑ˢ* ⨾ˢ (η₂ ∣ σ₂ ↑ˢ*) ]ˢ
      ≡⟨ cong (((η₁ ⨟ˢ η₂) ↑ˢ) ∣ e [_]ˢ) (lift*-dist-Compˢˢ η₁ η₂ σ₁ σ₂) ⟩
        ((η₁ ⨟ˢ η₂) ↑ˢ) ∣ e [ (η₁ ⨟ˢ η₂) ∣ η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂ ↑ˢ* ]ˢ
      ∎)
  Compositionalityˢˢ (e₁ · e₂)  η₁ η₂ σ₁ σ₂  = cong₂ _·_ 
      (Compositionalityˢˢ e₁ η₁ η₂ σ₁ σ₂) 
      (Compositionalityˢˢ e₂ η₁ η₂ σ₁ σ₂)
  Compositionalityˢˢ (e ·* T′)  η₁ η₂ σ₁ σ₂  = cong (_·* (T′ [ η₁ ⨟ˢ η₂ ]ˢ)) 
    (Compositionalityˢˢ e η₁ η₂ σ₁ σ₂)

-- expression-level σ-calculus laws (mirroring the type-level laws above)
opaque
  unfolding Idᴿ Wkᴿ wkᴿ* _,_∣_⨾ᴿ_ _∣_∙ᴿ_ _∣_∙ᴿ*_ _∣_&ᴿ_ _∣_⇑ᴿ_ _∣_↑ᴿ* _∣_[_]ᴿ _∣⟪_⟫ Idˢ Wkˢ wkᴿ*ˢ _∣_∙ˢ_ _∣_∙ˢ*_ _,_∣_⨾ˢ_ _∣_&ˢ_ _∣_⇑ˢ_ _∣_↑ˢ* _∣_[_]ˢ

  --! ExprRenamingTraversal {
  -- traversal clauses on expressions as rewrite rules (analog of traversal-* type-level)
  Traversal-Varᴿ : ∀ {ζ : n₁ →ᴿ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (x : Γ₁ ∋ T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                   ζ ∣ (` x) [ ρ ]ᴿ ≡ ` (ζ ∣ x &ᴿ ρ)
  Traversal-Varᴿ _ _ = refl

  Traversal-λxᴿ : ∀ {ζ : n₁ →ᴿ n₂} {T₁ T₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr (Γ₁ ▷ T₁) T₂) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                  ζ ∣ (λx e) [ ρ ]ᴿ ≡ λx (ζ ∣ e [ ρ ⇑ᴿ T₁ ]ᴿ)
  Traversal-λxᴿ _ _ = refl

  Traversal-Λαᴿ : ∀ {ζ : n₁ →ᴿ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr (Γ₁ ▷*) T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                  ζ ∣ (Λα e) [ ρ ]ᴿ ≡ Λα ((ζ ↑ᴿ) ∣ e [ ↑ᴿ* ρ ]ᴿ)
  Traversal-Λαᴿ _ _ = refl

  Traversal-·ᴿ : ∀ {ζ : n₁ →ᴿ n₂} {T₁ T₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                 (e₁ : Expr Γ₁ (T₁ ⇒ T₂)) (e₂ : Expr Γ₁ T₁) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                 ζ ∣ (e₁ · e₂) [ ρ ]ᴿ ≡ (ζ ∣ e₁ [ ρ ]ᴿ) · (ζ ∣ e₂ [ ρ ]ᴿ)
  Traversal-·ᴿ _ _ _ = refl

  Traversal-·*ᴿ : ∀ {ζ : n₁ →ᴿ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr Γ₁ (∀α T)) (T′ : Type n₁) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                  ζ ∣ (e ·* T′) [ ρ ]ᴿ ≡ (ζ ∣ e [ ρ ]ᴿ) ·* (T′ [ ζ ]ᴿ)
  Traversal-·*ᴿ _ _ _ = refl
  --! }

  --! ExprSubstitutionTraversal {
  -- traversal clauses on expressions for substitutions
  Traversal-Varˢ : ∀ {η : n₁ →ˢ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (x : Γ₁ ∋ T) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                   η ∣ (` x) [ σ ]ˢ ≡ η ∣ x &ˢ σ
  Traversal-Varˢ _ _ = refl

  Traversal-λxˢ : ∀ {η : n₁ →ˢ n₂} {T₁ T₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr (Γ₁ ▷ T₁) T₂) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                  η ∣ (λx e) [ σ ]ˢ ≡ λx (η ∣ e [ η ∣ σ ⇑ˢ T₁ ]ˢ)
  Traversal-λxˢ _ _ = refl

  Traversal-Λαˢ : ∀ {η : n₁ →ˢ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr (Γ₁ ▷*) T) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                  η ∣ (Λα e) [ σ ]ˢ ≡ Λα ((η ↑ˢ) ∣ e [ η ∣ σ ↑ˢ* ]ˢ)
  Traversal-Λαˢ _ _ = refl

  Traversal-·ˢ : ∀ {η : n₁ →ˢ n₂} {T₁ T₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                 (e₁ : Expr Γ₁ (T₁ ⇒ T₂)) (e₂ : Expr Γ₁ T₁) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                 η ∣ (e₁ · e₂) [ σ ]ˢ ≡ (η ∣ e₁ [ σ ]ˢ) · (η ∣ e₂ [ σ ]ˢ)
  Traversal-·ˢ _ _ _ = refl

  Traversal-·*ˢ : ∀ {η : n₁ →ˢ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr Γ₁ (∀α T)) (T′ : Type n₁) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                  η ∣ (e ·* T′) [ σ ]ˢ ≡ (η ∣ e [ σ ]ˢ) ·* (T′ [ η ]ˢ)
  Traversal-·*ˢ _ _ _ = refl
  --! }

  --! ExprRenamingBeta {
  -- computing renamings on expressions (analog of `beta-* on type level)
  Beta-idᴿ : ∀ {T} {Γ : Ctx n} (x : Γ ∋ T) → idᴿ ∣ x &ᴿ Idᴿ ≡ x
  Beta-idᴿ _ = refl

  Beta-wkᴿ : ∀ {T T'} {Γ : Ctx n} (x : Γ ∋ T) → idᴿ ∣ x &ᴿ Wkᴿ T' ≡ suc x
  Beta-wkᴿ _ = refl

  Beta-wk*ᴿ : ∀ {T} {Γ : Ctx n} (x : Γ ∋ T) → wkᴿ ∣ x &ᴿ wkᴿ* ≡ suc* x
  Beta-wk*ᴿ _ = refl

  Beta-ext-zeroᴿ : ∀ {ζ : n₁ →ᴿ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (x : Γ₂ ∋ (T [ ζ ]ᴿ)) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                   ζ ∣ zero &ᴿ (_∣_∙ᴿ_ {T = T} ζ x ρ) ≡ x
  Beta-ext-zeroᴿ _ _ = refl

  Beta-ext-sucᴿ : ∀ {ζ : n₁ →ᴿ n₂} {T T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (x' : Γ₁ ∋ T'') (x : Γ₂ ∋ (T [ ζ ]ᴿ)) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                  ζ ∣ (suc x') &ᴿ (_∣_∙ᴿ_ {T = T} ζ x ρ) ≡ ζ ∣ x' &ᴿ ρ
  Beta-ext-sucᴿ _ _ _ = refl

  Beta-ext-suc*ᴿ : ∀ {ζ : n₁ →ᴿ n₂} {T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (α : Fin n₂) (x : Γ₁ ∋ T'') (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                   (α ∙ᴿ ζ) ∣ (suc* x) &ᴿ (ζ ∣ α ∙ᴿ* ρ) ≡ ζ ∣ x &ᴿ ρ
  Beta-ext-suc*ᴿ _ _ _ = refl

  Beta-compᴿ : ∀ {ζ₁ : n₁ →ᴿ n₂} {ζ₂ : n₂ →ᴿ n₃} {T}
               {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
               (x : Γ₁ ∋ T) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
               (ζ₁ ⨟ᴿ ζ₂) ∣ x &ᴿ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ≡ ζ₂ ∣ (ζ₁ ∣ x &ᴿ ρ₁) &ᴿ ρ₂
  Beta-compᴿ _ _ _ = refl
  --! }

  --! ExprSubstitutionBeta {
  -- computing substitutions on expressions (analog of beta-* on type level)
  Beta-ext-zeroˢ : ∀ {η : n₁ →ˢ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (e : Expr Γ₂ (T [ η ]ˢ)) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                   η ∣ zero &ˢ (_∣_∙ˢ_ {T = T} η e σ) ≡ e
  Beta-ext-zeroˢ _ _ = refl

  Beta-ext-sucˢ : ∀ {η : n₁ →ˢ n₂} {T T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (x' : Γ₁ ∋ T'') (e : Expr Γ₂ (T [ η ]ˢ)) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                  η ∣ (suc x') &ˢ (_∣_∙ˢ_ {T = T} η e σ) ≡ η ∣ x' &ˢ σ
  Beta-ext-sucˢ _ _ _ = refl

  Beta-ext-suc*ˢ : ∀ {η : n₁ →ˢ n₂} {T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (T' : Type n₂) (x : Γ₁ ∋ T'') (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                   (T' ∙ˢ η) ∣ (suc* x) &ˢ (η ∣ T' ∙ˢ* σ) ≡ η ∣ x &ˢ σ
  Beta-ext-suc*ˢ _ _ _ = refl

  Beta-renameˢ : ∀ {ζ : n₁ →ᴿ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                 (x : Γ₁ ∋ T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                 ⟨ ζ ⟩ ∣ x &ˢ (ζ ∣⟪ ρ ⟫) ≡ ` (ζ ∣ x &ᴿ ρ)
  Beta-renameˢ _ _ = refl

  Beta-compˢ : ∀ {η₁ : n₁ →ˢ n₂} {η₂ : n₂ →ˢ n₃} {T}
               {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
               (x : Γ₁ ∋ T) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
               (η₁ ⨟ˢ η₂) ∣ x &ˢ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ≡ η₂ ∣ (η₁ ∣ x &ˢ σ₁) [ σ₂ ]ˢ
  Beta-compˢ _ _ _ = refl
  --! }

  --! ExprRenLaws {
  -- interaction between expression-renamings (analog of `associativity, etc.)
  Associativityᴿ : ∀ {n₁ n₂ n₃ n₄}
                   (ζ₁ : n₁ →ᴿ n₂) (ζ₂ : n₂ →ᴿ n₃) (ζ₃ : n₃ →ᴿ n₄)
                   {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃} {Γ₄ : Ctx n₄}
                   (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) (ρ₃ : ζ₃ ∣ Γ₃ ⇒ᴿ Γ₄) →
                   ((ζ₁ ⨟ᴿ ζ₂) , ζ₃ ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ⨾ᴿ ρ₃) ≡
                   (ζ₁ , (ζ₂ ⨟ᴿ ζ₃) ∣ ρ₁ ⨾ᴿ (ζ₂ , ζ₃ ∣ ρ₂ ⨾ᴿ ρ₃))
  Associativityᴿ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Distributivityᴿ : ∀ {n₁ n₂ n₃} (ζ : n₁ →ᴿ n₂) (ζ′ : n₂ →ᴿ n₃)
                    {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
                    (T : Type n₁) (x : Γ₂ ∋ (T [ ζ ]ᴿ))
                    (ρ₁ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ′ ∣ Γ₂ ⇒ᴿ Γ₃) →
                    (ζ , ζ′ ∣ (_∣_∙ᴿ_ {T = T} ζ x ρ₁) ⨾ᴿ ρ₂) ≡
                    (_∣_∙ᴿ_ {T = T} (ζ ⨟ᴿ ζ′) (ρ₂ (T [ ζ ]ᴿ) x) (ζ , ζ′ ∣ ρ₁ ⨾ᴿ ρ₂))
  Distributivityᴿ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  Distributivity*ᴿ : ∀ {n₁ n₂ n₃} (ζ : n₁ →ᴿ n₂) (ζ′ : n₂ →ᴿ n₃)
                     {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
                     (α : Fin n₂) (ρ₁ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ′ ∣ Γ₂ ⇒ᴿ Γ₃) →
                     ((α ∙ᴿ ζ) , ζ′ ∣ (ζ ∣ α ∙ᴿ* ρ₁) ⨾ᴿ ρ₂) ≡
                     ((ζ ⨟ᴿ ζ′) ∣ (α &ᴿ ζ′) ∙ᴿ* (ζ , ζ′ ∣ ρ₁ ⨾ᴿ ρ₂))
  Distributivity*ᴿ _ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Interactᴿ : ∀ {n₁ n₂} (ζ : n₁ →ᴿ n₂) {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
              {x : Γ₂ ∋ (T [ ζ ]ᴿ)} (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
              (idᴿ , ζ ∣ (Wkᴿ T) ⨾ᴿ (ζ ∣ x ∙ᴿ ρ)) ≡ ρ
  Interactᴿ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Interact*ᴿ : ∀ {n₁ n₂} (ζ : n₁ →ᴿ n₂) {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
               {α : Fin n₂} (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
               (wkᴿ , (α ∙ᴿ ζ) ∣ wkᴿ* ⨾ᴿ (ζ ∣ α ∙ᴿ* ρ)) ≡ ρ
  Interact*ᴿ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Comp-idᵣᴿ : ∀ {ζ : n₁ →ᴿ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
              (ζ , idᴿ ∣ ρ ⨾ᴿ Idᴿ) ≡ ρ
  Comp-idᵣᴿ _ = fun-ext λ _ → fun-ext λ _ → refl

  Comp-idₗᴿ : ∀ {ζ : n₁ →ᴿ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
              (idᴿ , ζ ∣ Idᴿ ⨾ᴿ ρ) ≡ ρ
  Comp-idₗᴿ _ = fun-ext λ _ → fun-ext λ _ → refl

  η-lawᴿ : ∀ {n₁ n₂} {ζ : n₁ →ᴿ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
           (ρ : ζ ∣ (Γ₁ ▷ T) ⇒ᴿ Γ₂) →
           (ζ ∣ ρ T zero ∙ᴿ (idᴿ , ζ ∣ (Wkᴿ T) ⨾ᴿ ρ)) ≡ ρ
  η-lawᴿ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  η-law*ᴿ : ∀ {n₁ n₂} {ζ : suc n₁ →ᴿ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
            (ρ : ζ ∣ (Γ₁ ▷*) ⇒ᴿ Γ₂) →
            ((wkᴿ ⨟ᴿ ζ) ∣ (zero &ᴿ ζ) ∙ᴿ* (wkᴿ , ζ ∣ wkᴿ* ⨾ᴿ ρ)) ≡ ρ
  η-law*ᴿ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  -- η-id*ᴿ: zero ∙ᴿ* wkᴿ* (an expression-renaming on (Γ ▷*) → (Γ ▷*)) ≡ Idᴿ
  η-Id*ᴿ : ∀ {Γ : Ctx n} → (wkᴿ ∣ zero ∙ᴿ* (wkᴿ* {Γ = Γ})) ≡ Idᴿ
  η-Id*ᴿ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }
  --! }

  --! ExprSubLaws {
  -- interaction between expression-substitutions (analog of `associativity, etc.)
  Associativityˢ : ∀ {n₁ n₂ n₃ n₄}
                   (η₁ : n₁ →ˢ n₂) (η₂ : n₂ →ˢ n₃) (η₃ : n₃ →ˢ n₄)
                   {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃} {Γ₄ : Ctx n₄}
                   (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) (σ₃ : η₃ ∣ Γ₃ ⇒ˢ Γ₄) →
                   ((η₁ ⨟ˢ η₂) , η₃ ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ⨾ˢ σ₃) ≡
                   (η₁ , (η₂ ⨟ˢ η₃) ∣ σ₁ ⨾ˢ (η₂ , η₃ ∣ σ₂ ⨾ˢ σ₃))
  Associativityˢ _ _ _ σ₁ σ₂ σ₃ =
    fun-ext λ _ → fun-ext λ x → Compositionalityˢˢ (σ₁ _ x) _ _ σ₂ σ₃

  Distributivityˢ : ∀ {n₁ n₂ n₃} (η : n₁ →ˢ n₂) (η′ : n₂ →ˢ n₃)
                    {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
                    (T : Type n₁) (e : Expr Γ₂ (T [ η ]ˢ))
                    (σ₁ : η ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η′ ∣ Γ₂ ⇒ˢ Γ₃) →
                    (η , η′ ∣ (_∣_∙ˢ_ {T = T} η e σ₁) ⨾ˢ σ₂) ≡
                    (_∣_∙ˢ_ {T = T} (η ⨟ˢ η′) (η′ ∣ e [ σ₂ ]ˢ) (η , η′ ∣ σ₁ ⨾ˢ σ₂))
  Distributivityˢ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  Distributivity*ˢ : ∀ {n₁ n₂ n₃} (η : n₁ →ˢ n₂) (η′ : n₂ →ˢ n₃)
                     {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
                     (T : Type n₂) (σ₁ : η ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η′ ∣ Γ₂ ⇒ˢ Γ₃) →
                     ((T ∙ˢ η) , η′ ∣ (η ∣ T ∙ˢ* σ₁) ⨾ˢ σ₂) ≡
                     ((η ⨟ˢ η′) ∣ (T [ η′ ]ˢ) ∙ˢ* (η , η′ ∣ σ₁ ⨾ˢ σ₂))
  Distributivity*ˢ _ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Interactˢ : ∀ {n₁ n₂} (η : n₁ →ˢ n₂) {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
              {e : Expr Γ₂ (T [ η ]ˢ)} (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
              (⟨ idᴿ ⟩ , η ∣ (Wkˢ T) ⨾ˢ (η ∣ e ∙ˢ σ)) ≡ σ
  Interactˢ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Interact*ˢ : ∀ {n₁ n₂} (η : n₁ →ˢ n₂) {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
               {T : Type n₂} (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
               (⟨ wkᴿ ⟩ , (T ∙ˢ η) ∣ wkᴿ*ˢ ⨾ˢ (η ∣ T ∙ˢ* σ)) ≡ σ
  Interact*ˢ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Comp-idᵣˢ : ∀ {η : n₁ →ˢ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
              (η , ⟨ idᴿ ⟩ ∣ σ ⨾ˢ Idˢ) ≡ σ
  Comp-idᵣˢ σ = fun-ext λ _ → fun-ext λ x → Identityᵣ (σ _ x)

  Comp-idₗˢ : ∀ {η : n₁ →ˢ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
              (⟨ idᴿ ⟩ , η ∣ Idˢ ⨾ˢ σ) ≡ σ
  Comp-idₗˢ _ = fun-ext λ _ → fun-ext λ _ → refl

  η-lawˢ : ∀ {n₁ n₂} {η : n₁ →ˢ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
           (σ : η ∣ (Γ₁ ▷ T) ⇒ˢ Γ₂) →
           (η ∣ σ T zero ∙ˢ (⟨ idᴿ ⟩ , η ∣ (Wkˢ T) ⨾ˢ σ)) ≡ σ
  η-lawˢ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  η-law*ˢ : ∀ {n₁ n₂} {η : suc n₁ →ˢ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
            (σ : η ∣ (Γ₁ ▷*) ⇒ˢ Γ₂) →
            ((⟨ wkᴿ ⟩ ⨟ˢ η) ∣ (zero &ˢ η) ∙ˢ* (⟨ wkᴿ ⟩ , η ∣ wkᴿ*ˢ ⨾ˢ σ)) ≡ σ
  η-law*ˢ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  -- η-id*ˢ: (` zero) ∙ˢ* wkᴿ*ˢ (an expression-substitution on (Γ ▷*) → (Γ ▷*)) ≡ Idˢ
  η-Id*ˢ : ∀ {Γ : Ctx n} → (⟨ wkᴿ ⟩ ∣ (` zero) ∙ˢ* (wkᴿ*ˢ {Γ = Γ})) ≡ Idˢ
  η-Id*ˢ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }
  --! }

  --! ExprLiftBeta {
  -- σ-calculus form of lifts (analog of type-level `beta-lift`):
  -- ρ ⇑ᴿ T is the σ-form ` zero ∙ᴿ (ρ ⨾ᴿ Wkᴿ); similarly for ↑ᴿ*, ⇑ˢ, ↑ˢ*.
  Beta-liftᴿ : ∀ {ζ : n₁ →ᴿ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T : Type n₁}
               (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
               (ζ ∣ ρ ⇑ᴿ T) ≡ (ζ ∣ zero ∙ᴿ (ζ , idᴿ ∣ ρ ⨾ᴿ Wkᴿ (T [ ζ ]ᴿ)))
  Beta-liftᴿ _ = refl

  Beta-lift*ᴿ : ∀ {ζ : n₁ →ᴿ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                (ζ ∣ ρ ↑ᴿ*) ≡ ((ζ ⨟ᴿ wkᴿ) ∣ zero ∙ᴿ* (ζ , wkᴿ ∣ ρ ⨾ᴿ wkᴿ*))
  Beta-lift*ᴿ _ = refl

  Beta-liftˢ : ∀ {η : n₁ →ˢ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T : Type n₁}
               (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
               (η ∣ σ ⇑ˢ T) ≡ (η ∣ (` zero) ∙ˢ (η , ⟨ idᴿ ⟩ ∣ σ ⨾ˢ Wkˢ (T [ η ]ˢ)))
  Beta-liftˢ σ = fun-ext λ _ → fun-ext λ
    { zero → refl
    ; (suc x) → sym (Coincidence (σ _ x) (Wkᴿ _))
    }

  Beta-lift*ˢ : ∀ {η : n₁ →ˢ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                (η ∣ σ ↑ˢ*) ≡ ((η ⨟ˢ ⟨ wkᴿ ⟩) ∣ (` zero) ∙ˢ* (η , ⟨ wkᴿ ⟩ ∣ σ ⨾ˢ wkᴿ*ˢ))
  Beta-lift*ˢ σ = fun-ext λ _ → fun-ext λ
    { (suc* x) → sym (Coincidence (σ _ x) wkᴿ*)
    }
  --! }

-- σ-calculus rewrite system on expressions (analog of the type-level REWRITE)
{-# REWRITE
  Traversal-Varᴿ
  Traversal-λxᴿ
  Traversal-Λαᴿ
  Traversal-·ᴿ
  Traversal-·*ᴿ

  Traversal-Varˢ
  Traversal-λxˢ
  Traversal-Λαˢ
  Traversal-·ˢ
  Traversal-·*ˢ

  Beta-idᴿ
  Beta-wkᴿ
  Beta-wk*ᴿ
  Beta-ext-zeroᴿ
  Beta-ext-sucᴿ
  Beta-ext-suc*ᴿ
  Beta-compᴿ

  Beta-ext-zeroˢ
  Beta-ext-sucˢ
  Beta-ext-suc*ˢ
  Beta-liftᴿ
  Beta-lift*ᴿ
  Beta-liftˢ
  Beta-lift*ˢ
  Beta-compˢ
  Beta-renameˢ

  Associativityˢ
  Distributivityˢ
  Distributivity*ˢ
  Interactˢ
  Interact*ˢ
  Comp-idᵣˢ
  Comp-idₗˢ
  η-Id
  η-Id*ˢ
  η-lawˢ
  η-law*ˢ

  Associativityᴿ
  Distributivityᴿ
  Distributivity*ᴿ
  Interactᴿ
  Interact*ᴿ
  Comp-idᵣᴿ
  Comp-idₗᴿ
  η-Idᴿ
  η-Id*ᴿ
  η-lawᴿ
  η-law*ᴿ

  Identityᵣ
  Compositionalityᴿˢ
  Compositionalityᴿᴿ
  Compositionalityˢᴿ
  Compositionalityˢˢ

  Coincidence
#-}


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
