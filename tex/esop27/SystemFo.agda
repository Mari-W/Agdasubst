-- rewriting safe, when rewrites terminate, double checked by kernel
{-# OPTIONS --rewriting --confluence-check --double-check #-}
module SystemFo where
open import Agda.Builtin.Equality.Rewrite public

-- standard equational reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning

-- function extensionality (postulated)
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

--! FOKind
data Kind : Set where
  ∗   : Kind
  _⇒_ : Kind → Kind → Kind

variable
  I J K : Kind

--! FOTypeCtx
data Ctx* : Set where
  ∅    : Ctx*
  _▷*_ : Ctx* → Kind → Ctx*

variable
  Φ Φ′ Φ₁ Φ₂ Φ₃ : Ctx*
  Ψ Ψ′ Ψ₁ Ψ₂ Ψ₃ : Ctx*
  Θ Θ′ Θ₁ Θ₂ Θ₃ : Ctx*

--! FOTypeVar
data _∋*_ : Ctx* → Kind → Set where
  zero  : (Φ ▷* K) ∋* K
  suc   : Φ ∋* K → (Φ ▷* J) ∋* K

--! FOType
--! Definition
data Type Φ : Kind → Set where
  `_   : Φ ∋* K → Type Φ K
  λα   : Type (Φ ▷* J) K → Type Φ (J ⇒ K)
  ∀α   : Type (Φ ▷* J) ∗ → Type Φ ∗
  _⇒_  : Type Φ ∗ → Type Φ ∗ → Type Φ ∗

-- type-level application is a postulate so that β≡* and traversal-$ are legal
-- rewrite rules (constructor heads aren't allowed for rewrite rules).
postulate
  _$_  : Type Φ (J ⇒ K) → Type Φ J → Type Φ K
infixl 9 _$_

variable
  α α′ α₁ α₂ α₃ : Φ ∋* K
  T T′ T₁ T₂ T₃ : Type Φ K

--! Renaming
-- renamings (K is explicit so plain fun-ext suffices)
_→ᴿ_ : Ctx* → Ctx* → Set
Φ →ᴿ Ψ = (K : Kind) → Φ ∋* K → Ψ ∋* K

--! RenamingOpaque {
opaque
  -- weakening (J explicit)
  wkᴿ : ∀ J → Φ →ᴿ (Φ ▷* J)
  wkᴿ _ _ α = suc α

  -- identity renaming
  idᴿ : Φ →ᴿ Φ
  idᴿ _ α = α

  -- extend with new variable
  _∙ᴿ_ : ∀ {K} → Ψ ∋* K → Φ →ᴿ Ψ → (Φ ▷* K) →ᴿ Ψ
  (α ∙ᴿ ζ) _ zero    = α
  (_ ∙ᴿ ζ) K (suc α) = ζ K α

  -- apply renaming to variable
  _&ᴿ_ : Φ ∋* K → Φ →ᴿ Ψ → Ψ ∋* K
  _&ᴿ_ {K = K} α ζ = ζ K α

  -- composition
  _⨟ᴿ_ : Φ →ᴿ Ψ → Ψ →ᴿ Θ → Φ →ᴿ Θ
  (ζ₁ ⨟ᴿ ζ₂) K α = ζ₂ K (ζ₁ K α)

-- lifting (J explicit, postfix-with-arg shape)
_↑ᴿ_ : Φ →ᴿ Ψ → ∀ J → (Φ ▷* J) →ᴿ (Ψ ▷* J)
ζ ↑ᴿ J = zero ∙ᴿ (ζ ⨟ᴿ wkᴿ J)

-- apply renaming to type
_[_]ᴿ : Type Φ K → Φ →ᴿ Ψ → Type Ψ K
(` α) [ ζ ]ᴿ           = ` (α &ᴿ ζ)
(λα {J = J} T) [ ζ ]ᴿ  = λα (T [ ζ ↑ᴿ J ]ᴿ)
(∀α {J = J} T) [ ζ ]ᴿ  = ∀α (T [ ζ ↑ᴿ J ]ᴿ)
(T₁ ⇒ T₂) [ ζ ]ᴿ       = (T₁ [ ζ ]ᴿ) ⇒ (T₂ [ ζ ]ᴿ)
--! }

variable
  ζ ζ′ ζ₁ ζ₂ ζ₃ : Φ →ᴿ Ψ

--! Substitution
-- substitutions (K is explicit so plain fun-ext suffices)
_→ˢ_ : Ctx* → Ctx* → Set
Φ →ˢ Ψ = (K : Kind) → Φ ∋* K → Type Ψ K

--! SubstitutionOpaque {
opaque
  -- lift renaming to substitution
  ⟨_⟩ : Φ →ᴿ Ψ → Φ →ˢ Ψ
  ⟨ ζ ⟩ K α = ` (α &ᴿ ζ)

  -- extend with new type
  _∙ˢ_ : ∀ {K} → Type Ψ K → Φ →ˢ Ψ → (Φ ▷* K) →ˢ Ψ
  (T ∙ˢ η) _ zero    = T
  (T ∙ˢ η) K (suc α) = η K α

  -- apply substitution to variable
  _&ˢ_ : Φ ∋* K → Φ →ˢ Ψ → Type Ψ K
  _&ˢ_ {K = K} α η = η K α

  -- lifting (J explicit, postfix-with-arg shape)
  _↑ˢ_ : Φ →ˢ Ψ → ∀ J → (Φ ▷* J) →ˢ (Ψ ▷* J)
  η ↑ˢ J = (` zero) ∙ˢ λ K α → (η K α) [ wkᴿ J ]ᴿ

-- apply substitution to type
_[_]ˢ : Type Φ K → Φ →ˢ Ψ → Type Ψ K
(` α) [ η ]ˢ           = α &ˢ η
(λα {J = J} T) [ η ]ˢ  = λα (T [ η ↑ˢ J ]ˢ)
(∀α {J = J} T) [ η ]ˢ  = ∀α (T [ η ↑ˢ J ]ˢ)
(T₁ ⇒ T₂) [ η ]ˢ       = (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)

-- traversal of the postulated `_$_` is itself postulated (since `_$_` has no
-- defining equations). Adding these as rewrites makes substitution push past `_$_`.
postulate
  traversal-$ᴿ : ∀ {Φ Ψ J K} {T₁ : Type Φ (J ⇒ K)} {T₂ : Type Φ J} {ζ : Φ →ᴿ Ψ} →
                 (T₁ $ T₂) [ ζ ]ᴿ ≡ (T₁ [ ζ ]ᴿ) $ (T₂ [ ζ ]ᴿ)
  traversal-$ˢ : ∀ {Φ Ψ J K} {T₁ : Type Φ (J ⇒ K)} {T₂ : Type Φ J} {η : Φ →ˢ Ψ} →
                 (T₁ $ T₂) [ η ]ˢ ≡ (T₁ [ η ]ˢ) $ (T₂ [ η ]ˢ)

opaque
  -- composition
  _⨟ˢ_ : Φ →ˢ Ψ → Ψ →ˢ Θ → Φ →ˢ Θ
  (η₁ ⨟ˢ η₂) K α = (η₁ K α) [ η₂ ]ˢ
--! }

variable
  η η′ η₁ η₂ η₃ : Φ →ˢ Ψ

opaque
  unfolding wkᴿ ⟨_⟩ _⨟ˢ_

  --! RenamingBeta {
  -- computing renamings
  `beta-ext-zero    : zero  &ᴿ (α ∙ᴿ ζ)              ≡ α
  `beta-ext-suc     : suc α &ᴿ (α′ ∙ᴿ ζ)             ≡ α &ᴿ ζ
  `beta-id          : α &ᴿ idᴿ                       ≡ α
  `beta-wk          : ∀ {J} → α &ᴿ wkᴿ J             ≡ suc {J = J} α
  `beta-comp        : α &ᴿ (ζ₁ ⨟ᴿ ζ₂)                ≡ (α &ᴿ ζ₁) &ᴿ ζ₂
  -- interaction between renamings
  `associativity    : (ζ₁ ⨟ᴿ ζ₂) ⨟ᴿ ζ₃               ≡ ζ₁ ⨟ᴿ (ζ₂ ⨟ᴿ ζ₃)
  `distributivity   : (α ∙ᴿ ζ₁) ⨟ᴿ ζ₂                ≡ (α &ᴿ ζ₂) ∙ᴿ (ζ₁ ⨟ᴿ ζ₂)
  `interact         : ∀ {Φ Ψ K} {α : Ψ ∋* K} {ζ : Φ →ᴿ Ψ} → wkᴿ K ⨟ᴿ (α ∙ᴿ ζ) ≡ ζ
  `comp-idᵣ         : ζ ⨟ᴿ idᴿ                       ≡ ζ
  `comp-idₗ         : idᴿ ⨟ᴿ ζ                       ≡ ζ
  `η-id             : ∀ {Φ J} → zero {Φ}{J} ∙ᴿ wkᴿ J ≡ idᴿ
  `η-law            : ∀ {Φ Ψ J} {ζ : (Φ ▷* J) →ᴿ Ψ} → (zero {Φ}{J} &ᴿ ζ) ∙ᴿ (wkᴿ J ⨟ᴿ ζ) ≡ ζ
  --! }

  --! SubstitutionBeta {
  -- computing substitutions
  beta-ext-zero     : zero  &ˢ (T ∙ˢ η)              ≡ T
  beta-ext-suc      : suc α &ˢ (T ∙ˢ η)              ≡ α &ˢ η
  beta-rename       : α &ˢ ⟨ ζ ⟩                     ≡ ` (α &ᴿ ζ)
  beta-comp         : α &ˢ (η₁ ⨟ˢ η₂)                ≡ (α &ˢ η₁) [ η₂ ]ˢ
  beta-lift         : ∀ {Φ Ψ J} {η : Φ →ˢ Ψ} →
                      η ↑ˢ J ≡ (`_ {Ψ ▷* J} (zero {K = J})) ∙ˢ (η ⨟ˢ ⟨ wkᴿ J ⟩)
  -- interaction between substitutions
  associativity     : (η₁ ⨟ˢ η₂) ⨟ˢ η₃               ≡ η₁ ⨟ˢ (η₂ ⨟ˢ η₃)
  distributivity    : (T ∙ˢ η₁) ⨟ˢ η₂                ≡ (T [ η₂ ]ˢ) ∙ˢ (η₁ ⨟ˢ η₂)
  interact          : ∀ {Φ Ψ K} {T : Type Ψ K} {η : Φ →ˢ Ψ} → ⟨ wkᴿ K ⟩ ⨟ˢ (T ∙ˢ η) ≡ η
  comp-idᵣ          : η ⨟ˢ ⟨ idᴿ ⟩                   ≡ η
  comp-idₗ          : ⟨ idᴿ ⟩ ⨟ˢ η                   ≡ η
  η-id              : ∀ {Φ J} → (`_ {Φ ▷* J} (zero {K = J})) ∙ˢ ⟨ wkᴿ J ⟩ ≡ ⟨ idᴿ ⟩
  η-law             : ∀ {Φ Ψ J} {η : (Φ ▷* J) →ˢ Ψ} → (zero {Φ}{J} &ˢ η) ∙ˢ (⟨ wkᴿ J ⟩ ⨟ˢ η) ≡ η
  --! }

  -- monad laws (composing renamings and substitutions)
  --! Monad
  identityᵣ          : T [ idᴿ ]ᴿ        ≡ T
  compositionalityᴿˢ : (T [ ζ₁ ]ᴿ) [ η₂ ]ˢ ≡ T [ ⟨ ζ₁ ⟩ ⨟ˢ η₂ ]ˢ
  compositionalityᴿᴿ : (T [ ζ₁ ]ᴿ) [ ζ₂ ]ᴿ ≡ T [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ
  compositionalityˢᴿ : (T [ η₁ ]ˢ) [ ζ₂ ]ᴿ ≡ T [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ
  compositionalityˢˢ : (T [ η₁ ]ˢ) [ η₂ ]ˢ ≡ T [ η₁ ⨟ˢ η₂ ]ˢ

  -- coincidence laws (transforming substitutions to renamings)
  --! Coincidence
  coincidence        : T [ ⟨ ζ ⟩ ]ˢ      ≡ T [ ζ ]ᴿ
  coincidence-comp   : ⟨ ζ₁ ⟩ ⨟ˢ ⟨ ζ₂ ⟩  ≡ ⟨ ζ₁ ⨟ᴿ ζ₂ ⟩

  identityᵣˢ         : T [ ⟨ idᴿ ⟩ ]ˢ    ≡ T

  -- proofs
  `beta-ext-zero = refl
  `beta-ext-suc  = refl
  `beta-id       = refl
  `beta-wk       = refl
  `beta-comp     = refl

  `associativity  = refl
  `distributivity = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }
  `interact       = refl
  `comp-idᵣ       = refl
  `comp-idₗ       = refl
  `η-id           = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }
  `η-law          = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }

  beta-ext-zero = refl
  beta-ext-suc  = refl
  beta-rename   = refl
  beta-comp     = refl
  beta-lift     = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → sym coincidence }

  associativity {η₁ = η₁} = fun-ext λ K → fun-ext (λ α → compositionalityˢˢ {T = η₁ K α})
  distributivity = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }
  interact       = refl
  comp-idᵣ       = fun-ext λ _ → fun-ext (λ _ → identityᵣˢ)
  comp-idₗ       = refl
  η-id           = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }
  η-law          = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }


  lift-idᴿ : ∀ {Φ} J → (idᴿ {Φ}) ↑ᴿ J ≡ idᴿ
  lift-idᴿ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }
  identityᵣ {T = (` α)}              = refl
  identityᵣ {T = (λα {J = J} T)}     = cong λα (trans (cong (T [_]ᴿ) (lift-idᴿ J)) (identityᵣ {T = T}))
  identityᵣ {T = (∀α {J = J} T)}     = cong ∀α (trans (cong (T [_]ᴿ) (lift-idᴿ J)) (identityᵣ {T = T}))
  identityᵣ {T = (T₁ ⇒ T₂)}          = cong₂ _⇒_ (identityᵣ {T = T₁}) (identityᵣ {T = T₂})

  lift-coincidence : ∀ {Φ Ψ} J {ζ : Φ →ᴿ Ψ} → ⟨ ζ ⟩ ↑ˢ J ≡ ⟨ ζ ↑ᴿ J ⟩
  lift-coincidence _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }

  coincidence {T = ` α}                       = refl
  coincidence {T = λα {J = J} T} {ζ = ζ}      = cong λα (trans (cong (T [_]ˢ) (lift-coincidence J)) coincidence)
  coincidence {T = ∀α {J = J} T} {ζ = ζ}      = cong ∀α (trans (cong (T [_]ˢ) (lift-coincidence J)) coincidence)
  coincidence {T = T₁ ⇒ T₂}                   = cong₂ _⇒_ coincidence coincidence

  coincidence-comp = fun-ext λ _ → fun-ext λ _ → refl

  lift-compositionalityᴿᴿ : ∀ {Φ Ψ Θ} J {ζ₁ : Φ →ᴿ Ψ} {ζ₂ : Ψ →ᴿ Θ} → (ζ₁ ↑ᴿ J) ⨟ᴿ (ζ₂ ↑ᴿ J) ≡ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ J
  lift-compositionalityᴿᴿ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }

  compositionalityᴿᴿ {T = ` α}              = refl
  compositionalityᴿᴿ {T = λα {J = J} T}     = cong λα (trans compositionalityᴿᴿ (cong (T [_]ᴿ) (lift-compositionalityᴿᴿ J)))
  compositionalityᴿᴿ {T = ∀α {J = J} T}     = cong ∀α (trans compositionalityᴿᴿ (cong (T [_]ᴿ) (lift-compositionalityᴿᴿ J)))
  compositionalityᴿᴿ {T = T₁ ⇒ T₂}          = cong₂ _⇒_ compositionalityᴿᴿ compositionalityᴿᴿ

  lift-compositionalityᴿˢ : ∀ {Φ Ψ Θ} J {ζ₁ : Φ →ᴿ Ψ} {η₂ : Ψ →ˢ Θ} → (⟨ ζ₁ ↑ᴿ J ⟩ ⨟ˢ (η₂ ↑ˢ J)) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ↑ˢ J)
  lift-compositionalityᴿˢ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }

  compositionalityᴿˢ {T = ` α}              = refl
  compositionalityᴿˢ {T = λα {J = J} T}     = cong λα (trans (compositionalityᴿˢ {T = T}) (cong (T [_]ˢ) (lift-compositionalityᴿˢ J)))
  compositionalityᴿˢ {T = ∀α {J = J} T}     = cong ∀α (trans (compositionalityᴿˢ {T = T}) (cong (T [_]ˢ) (lift-compositionalityᴿˢ J)))
  compositionalityᴿˢ {T = T₁ ⇒ T₂}          = cong₂ _⇒_ (compositionalityᴿˢ {T = T₁}) (compositionalityᴿˢ {T = T₂})

  lift-compositionalityˢᴿ : ∀ {Φ Ψ Θ} J {η₁ : Φ →ˢ Ψ} {ζ₂ : Ψ →ᴿ Θ} → ((η₁ ↑ˢ J) ⨟ˢ ⟨ ζ₂ ↑ᴿ J ⟩) ≡ ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ↑ˢ J)
  lift-compositionalityˢᴿ J {η₁ = η₁} {ζ₂ = ζ₂} = fun-ext λ K → fun-ext λ { zero → refl; (suc α) →
    let T = η₁ K α in
    begin
      (T [ wkᴿ J ]ᴿ) [ ⟨ ζ₂ ↑ᴿ J ⟩ ]ˢ  ≡⟨ coincidence ⟩
      (T [ wkᴿ J ]ᴿ) [ ζ₂ ↑ᴿ J ]ᴿ      ≡⟨ compositionalityᴿᴿ ⟩
      T [ wkᴿ J ⨟ᴿ (ζ₂ ↑ᴿ J) ]ᴿ        ≡⟨ sym compositionalityᴿᴿ ⟩
      (T [ ζ₂ ]ᴿ) [ wkᴿ J ]ᴿ           ≡⟨ cong (_[ wkᴿ J ]ᴿ) (sym coincidence) ⟩
      (T [ ⟨ ζ₂ ⟩ ]ˢ) [ wkᴿ J ]ᴿ       ∎ }

  compositionalityˢᴿ {T = ` α}              = sym coincidence
  compositionalityˢᴿ {T = λα {J = J} T}     = cong λα (trans (compositionalityˢᴿ {T = T}) (cong (T [_]ˢ) (lift-compositionalityˢᴿ J)))
  compositionalityˢᴿ {T = ∀α {J = J} T}     = cong ∀α (trans (compositionalityˢᴿ {T = T}) (cong (T [_]ˢ) (lift-compositionalityˢᴿ J)))
  compositionalityˢᴿ {T = T₁ ⇒ T₂}          = cong₂ _⇒_ (compositionalityˢᴿ {T = T₁}) (compositionalityˢᴿ {T = T₂})

  lift-compositionalityˢˢ : ∀ {Φ Ψ Θ} J {η₁ : Φ →ˢ Ψ} {η₂ : Ψ →ˢ Θ} → ((η₁ ↑ˢ J) ⨟ˢ (η₂ ↑ˢ J)) ≡ ((η₁ ⨟ˢ η₂) ↑ˢ J)
  lift-compositionalityˢˢ J {η₁ = η₁} {η₂ = η₂} = fun-ext λ K → fun-ext λ { zero → refl; (suc α) →
    let T = η₁ K α in
    begin
      (T [ wkᴿ J ]ᴿ) [ η₂ ↑ˢ J ]ˢ      ≡⟨ compositionalityᴿˢ {T = T} ⟩
      T [ ⟨ wkᴿ J ⟩ ⨟ˢ (η₂ ↑ˢ J) ]ˢ    ≡⟨ cong (T [_]ˢ) (fun-ext λ _ → fun-ext λ α → sym (coincidence {T = η₂ _ α})) ⟩
      T [ η₂ ⨟ˢ ⟨ wkᴿ J ⟩ ]ˢ           ≡⟨ sym (compositionalityˢᴿ {T = T}) ⟩
      (T [ η₂ ]ˢ) [ wkᴿ J ]ᴿ           ∎ }

  compositionalityˢˢ {T = ` α}              = refl
  compositionalityˢˢ {T = λα {J = J} T}     = cong λα (trans (compositionalityˢˢ {T = T}) (cong (T [_]ˢ) (lift-compositionalityˢˢ J)))
  compositionalityˢˢ {T = ∀α {J = J} T}     = cong ∀α (trans (compositionalityˢˢ {T = T}) (cong (T [_]ˢ) (lift-compositionalityˢˢ J)))
  compositionalityˢˢ {T = T₁ ⇒ T₂}          = cong₂ _⇒_ (compositionalityˢˢ {T = T₁}) (compositionalityˢˢ {T = T₂})

  identityᵣˢ {T = ` α}              = refl
  identityᵣˢ {T = λα T}             = cong λα (trans (cong (T [_]ˢ) η-id) identityᵣˢ)
  identityᵣˢ {T = ∀α T}             = cong ∀α (trans (cong (T [_]ˢ) η-id) identityᵣˢ)
  identityᵣˢ {T = T₁ ⇒ T₂}          = cong₂ _⇒_ identityᵣˢ identityᵣˢ

-- additional coincidence lemmas (mirroring SystemF.agda) needed to close the
-- rewrite system on the term-level _·*_ traversal. Each lemma describes a
-- σ-form that arises when the existing rewrites fire on a specific pattern.
opaque
  unfolding wkᴿ ⟨_⟩ _⨟ˢ_

  -- "single substitution under renaming": lifting ζ and post-composing with a
  -- single-substitution `_∙ˢ⟨idᴿ⟩` collapses to direct single substitution
  -- with ζ as the tail. Justifies (T [ T′ ]*) [ ζ ]ᴿ ≡ (T [ ζ ↑ᴿ ]ᴿ) [ T′[ζ]ᴿ ]*.
  coincidence-pop-ᴿ : ∀ {Φ Ψ J} {ζ : Φ →ᴿ Ψ} {T′ : Type Φ J} →
                       (⟨ ζ ↑ᴿ J ⟩ ⨟ˢ ((T′ [ ζ ]ᴿ) ∙ˢ ⟨ idᴿ ⟩)) ≡ ((T′ [ ζ ]ᴿ) ∙ˢ ⟨ ζ ⟩)
  coincidence-pop-ᴿ = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }

  -- variant of coincidence-pop-ᴿ where the renaming is itself a composition
  -- ζ₁ ⨟ᴿ ζ₂; the tail keeps ⟨ ζ₁ ⟩ ⨟ˢ ⟨ ζ₂ ⟩ (not yet folded by coincidence-comp).
  coincidence-pop-ᴿ-⨟ : ∀ {Φ Ψ Θ J} {ζ₁ : Φ →ᴿ Ψ} {ζ₂ : Ψ →ᴿ Θ} {T : Type Φ J} →
                       ⟨ zero ∙ᴿ (ζ₁ ⨟ᴿ (ζ₂ ⨟ᴿ wkᴿ J)) ⟩ ⨟ˢ ((T [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ) ∙ˢ ⟨ idᴿ ⟩)
                       ≡ (T [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ) ∙ˢ (⟨ ζ₁ ⟩ ⨟ˢ ⟨ ζ₂ ⟩)
  coincidence-pop-ᴿ-⨟ = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }

  -- "lift fusion" for renaming-then-substitution: ↑ᴿ(ζ₁) ⨟ˢ ↑ˢ(η₂) ≡ ↑ˢ(⟨ζ₁⟩ ⨟ˢ η₂),
  -- expressed in expanded form (post-`beta-lift`). Justifies the equation
  -- (T [ ζ₁ ↑ᴿ ]ᴿ) [ η₂ ↑ˢ ]ˢ ≡ T [ (⟨ ζ₁ ⟩ ⨟ˢ η₂) ↑ˢ ]ˢ as a rewrite.
  coincidence-↑ᴿ-↑ˢ : ∀ {Φ Ψ Θ J} {ζ₁ : Φ →ᴿ Ψ} {η₂ : Ψ →ˢ Θ} →
                       ⟨ zero ∙ᴿ (ζ₁ ⨟ᴿ wkᴿ J) ⟩ ⨟ˢ ((`_ {Θ ▷* J} (zero {K = J})) ∙ˢ (η₂ ⨟ˢ ⟨ wkᴿ J ⟩))
                       ≡ (`_ {Θ ▷* J} (zero {K = J})) ∙ˢ (⟨ ζ₁ ⟩ ⨟ˢ (η₂ ⨟ˢ ⟨ wkᴿ J ⟩))
  coincidence-↑ᴿ-↑ˢ = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }

  -- substitution analogue of coincidence-pop-ᴿ: a "shifted renaming"
  -- ⟨ ζ ⨟ᴿ wkᴿ ⟩ followed by a single-substitution simplifies (the wkᴿ skips
  -- the head). Justifies (T [ T′ ]*) [ η ]ˢ ≡ (T [ η ↑ˢ ]ˢ) [ T′[η]ˢ ]*.
  coincidence-pop-ˢ : ∀ {Φ Ψ Θ J} {η₁ : Φ →ˢ Ψ} {ζ₂ : Ψ →ᴿ Θ} {T′ : Type Φ J} →
                       ((T′ [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ) ∙ˢ (η₁ ⨟ˢ (⟨ ζ₂ ⨟ᴿ wkᴿ J ⟩ ⨟ˢ ((T′ [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ) ∙ˢ ⟨ idᴿ ⟩))))
                       ≡ ((T′ [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ) ∙ˢ (η₁ ⨟ˢ ⟨ ζ₂ ⟩))
  coincidence-pop-ˢ = fun-ext λ _ → fun-ext λ { zero → refl; (suc _) → refl }

{-# REWRITE
  `beta-id
  `beta-wk
  `beta-ext-zero
  `beta-ext-suc
  `beta-comp

  `associativity
  `distributivity
  `interact
  `comp-idᵣ
  `comp-idₗ
  `η-id
  `η-law

  beta-ext-zero
  beta-ext-suc
  beta-comp
  beta-rename
  beta-lift

  associativity
  distributivity
  interact
  comp-idᵣ
  comp-idₗ
  η-id
  η-law

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

  traversal-$ᴿ
  traversal-$ˢ
#-}

idˢ : Φ →ˢ Φ
idˢ = ⟨ idᴿ ⟩

-- functorial action
lift*-id : ∀ {Φ J} → (idᴿ {Φ}) ↑ᴿ J ≡ idᴿ
lift*-id = refl

lift*-comp : (ζ′ ⨟ᴿ ζ) ↑ᴿ J ≡ (ζ′ ↑ᴿ J) ⨟ᴿ (ζ ↑ᴿ J)
lift*-comp = refl

ren*-id : T [ idᴿ ]ᴿ ≡ T
ren*-id = refl

ren*-comp : T [ ζ′ ⨟ᴿ ζ ]ᴿ ≡ (T [ ζ′ ]ᴿ) [ ζ ]ᴿ
ren*-comp = refl

lifts*-id : ∀ {Φ J} → (idˢ {Φ}) ↑ˢ J ≡ idˢ
lifts*-id = refl

lifts*-comp : (η′ ⨟ˢ η) ↑ˢ J ≡ (η′ ↑ˢ J) ⨟ˢ (η ↑ˢ J)
lifts*-comp = refl

sub*-id : T [ idˢ ]ˢ ≡ T
sub*-id = refl

sub*-var : (` α) [ η ]ˢ ≡ α &ˢ η
sub*-var = refl

sub*-comp : T [ η ⨟ˢ η′ ]ˢ ≡ (T [ η ]ˢ) [ η′ ]ˢ
sub*-comp = refl

--! Weaken
weaken : ∀ J → Type Φ K → Type (Φ ▷* J) K
weaken J T = T [ wkᴿ J ]ᴿ

--! Subzero
_[_]* : Type (Φ ▷* J) K → Type Φ J → Type Φ K
T [ T′ ]* = T [ T′ ∙ˢ idˢ ]ˢ

data _≡β_ {Φ} : ∀{J} → Type Φ J → Type Φ J → Set where
  β≡β : ∀{K J}(B : Type (Φ ▷* J) K)(A : Type Φ J) → ((λα B) $ A) ≡β (B [ A ]*)
  -- structural rules

  refl≡β  : ∀{J}
    → (A : Type Φ J)
      ------------
    → A ≡β A
    
  sym≡β   : ∀{J}{A B : Type Φ J}
    → A ≡β B
      ------
    → B ≡β A
  trans≡β : ∀{J}{A B C : Type Φ J}
    → A ≡β B
    → B ≡β C
      ------
    → A ≡β C
 
  ⇒≡β : {A A' B B' : Type Φ ∗}
    → A ≡β A'
    → B ≡β B'
      ---------------------
    → (A ⇒ B) ≡β (A' ⇒ B')
    
  Π≡β : ∀{J}{B B' : Type (Φ ▷* J) ∗}
    → B ≡β B'
      -------
    → ∀α B ≡β ∀α B'

  ƛ≡β : ∀{K J}{B B' : Type (Φ ▷* J) K}
    → B ≡β B'
      ---------------
    → λα B ≡β λα B'
    
  ·≡β : ∀{K J}{A A' : Type Φ (K ⇒ J)}{B B' : Type Φ K}
    → A ≡β A'
    → B ≡β B'
      --------------------
    → (A $ B) ≡β (A' $ B') 

-- type equality
--! FOTypeBeta
postulate
  β≡* : ∀ {Φ J K} {T₁ : Type (Φ ▷* J) K} {T₂ : Type Φ J} →
        _$_ {Φ}{J}{K} (λα {Φ}{J}{K} T₁) T₂ ≡ T₁ [ T₂ ]*

-- term contexts
--! Ctx
data Ctx : Ctx* → Set where
  ∅    : Ctx ∅
  _▷_  : Ctx Φ → Type Φ ∗ → Ctx Φ
  _▷*  : Ctx Φ → ∀ {J} → Ctx (Φ ▷* J)

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx Φ

-- term variables
--! Var
data _∋_ : Ctx Φ → Type Φ ∗ → Set where
  zero  : (Γ ▷ T) ∋ T
  suc   : Γ ∋ T → (Γ ▷ T′) ∋ T
  suc*  : ∀ {J} → Γ ∋ T → ((Γ ▷*) {J}) ∋ weaken J T

variable
  x x′ x₁ x₂ x₃ : Γ ∋ T

--! FO >
--! Definition
data Expr {Φ} Γ : Type Φ ∗ → Set where
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
          (T′ : Type Φ K) →
          Expr Γ (T [ T′ ]*)
  conv  : Expr Γ T → T ≡β T′ → Expr Γ T′ 

variable
  e e′ e₁ e₁′ e₂ e₃ : Expr Γ T

--! Renaming
_∣_⇒ᴿ_ : Φ →ᴿ Ψ → Ctx Φ → Ctx Ψ → Set
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
wkᴿ* : ∀ J → wkᴿ J ∣ Γ ⇒ᴿ ((Γ ▷*) {J})
wkᴿ* _ _ x = suc* x

--! Composition
_,_∣_⨾ᴿ_ : ∀ (ζ₁ : Φ →ᴿ Ψ) (ζ₂ : Ψ →ᴿ Θ) → ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ζ₁ ⨟ᴿ ζ₂) ∣ Γ₁ ⇒ᴿ Γ₃
(_ , _ ∣ ρ₁ ⨾ᴿ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_⨾ᴿ_ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ζ₁ ⨟ᴿ ζ₂) ∣ Γ₁ ⇒ᴿ Γ₃
_⨾ᴿ_ = _,_∣_⨾ᴿ_ _ _

--! Extension
_∣_∙ᴿ_ : ∀ (ζ : Φ →ᴿ Ψ) → Γ₂ ∋ (T [ ζ ]ᴿ) → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ Γ₂
(_ ∣ x ∙ᴿ ρ) _ zero     = x
(_ ∣ _ ∙ᴿ ρ) _ (suc x)  = ρ _ x

--! Lifting
_∣_⇑ᴿ_ : ∀ (ζ : Φ →ᴿ Ψ) → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ ζ ]ᴿ))
(_ ∣ _ ⇑ᴿ _) _ zero    = zero
(_ ∣ ρ ⇑ᴿ _) _ (suc x) = suc (ρ _ x)

_⇑ᴿ_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ ζ ]ᴿ))
_⇑ᴿ_ = _ ∣_⇑ᴿ_

--! TLifting
_∣_↑ᴿ*_ : ∀ (ζ : Φ →ᴿ Ψ) → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ J → (ζ ↑ᴿ J) ∣ ((Γ₁ ▷*) {J}) ⇒ᴿ ((Γ₂ ▷*) {J})
(_ ∣ ρ ↑ᴿ* _) _ (suc* x) = suc* (ρ _ x)

↑ᴿ*_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ J → (ζ ↑ᴿ J) ∣ ((Γ₁ ▷*) {J}) ⇒ᴿ ((Γ₂ ▷*) {J})
↑ᴿ*_ = _ ∣_↑ᴿ*_

postulate 
  lemᴿ : T₁ ≡β T → (T₁ [ ζ ]ᴿ) ≡β (T [ ζ ]ᴿ)

--! Traversal
_∣_[_]ᴿ : (ζ : Φ →ᴿ Ψ) → Expr Γ₁ T → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → Expr Γ₂ (T [ ζ ]ᴿ)
_  ∣ (` x) [ ρ ]ᴿ      = ` (ρ _ x)
_  ∣ (λx e) [ ρ ]ᴿ     = λx (_ ∣ e [ ρ ⇑ᴿ _ ]ᴿ)
_  ∣ (Λα e) [ ρ ]ᴿ     = Λα (_ ∣ e [ _ ∣ ρ ↑ᴿ* _ ]ᴿ)
_  ∣ (e₁ · e₂) [ ρ ]ᴿ  = (_ ∣ e₁ [ ρ ]ᴿ) · (_ ∣ e₂ [ ρ ]ᴿ)
ζ  ∣ (e ·* T′) [ ρ ]ᴿ  = (ζ ∣ e [ ρ ]ᴿ) ·* (T′ [ ζ ]ᴿ)
ζ  ∣ conv e x [ ρ ]ᴿ  = conv (ζ ∣ e [ ρ ]ᴿ) (lemᴿ x)

Weaken : Expr Γ T → Expr (Γ ▷ T′) T
Weaken e = idᴿ ∣ e [ Wkᴿ _ ]ᴿ

weaken* : ∀ J → Expr Γ T → Expr ((Γ ▷*) {J}) (weaken J T)
weaken* J e = wkᴿ J ∣ e [ wkᴿ* J ]ᴿ

--! <
--! Substitution
_∣_⇒ˢ_ : Φ →ˢ Ψ → Ctx Φ → Ctx Ψ → Set
η ∣ Γ₁ ⇒ˢ Γ₂ = ∀ T → Γ₁ ∋ T → Expr Γ₂ (T [ η ]ˢ)

--! Sub >
variable
  σ σ′ σ₁ σ₂ σ₃ : η ∣ Γ₁ ⇒ˢ Γ₂

-- raising a renaming to a substitution
_∣⟪_⟫ : ∀ (ζ : Φ →ᴿ Ψ) → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
(ζ ∣⟪ ρ ⟫) _ x = ` ρ _ x

⟪_⟫ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
⟪_⟫ = _ ∣⟪_⟫

--! Ids
Idˢ : idˢ ∣ Γ ⇒ˢ Γ
Idˢ _ = `_

Wkˢ : ∀ T → ⟨ idᴿ ⟩ ∣ Γ ⇒ˢ (Γ ▷ T)
Wkˢ _ = idᴿ ∣⟪ Wkᴿ _ ⟫

wkᴿ*ˢ : ∀ J → ⟨ wkᴿ J ⟩ ∣ Γ ⇒ˢ ((Γ ▷*) {J})
wkᴿ*ˢ J = wkᴿ J ∣⟪ wkᴿ* J ⟫

-- extending a substitution
--! Extension
_∣_∙ˢ_ : ∀ (η : Φ →ˢ Ψ) → Expr Γ₂ (T [ η ]ˢ) → η ∣ Γ₁ ⇒ˢ Γ₂ → η ∣ (Γ₁ ▷ T) ⇒ˢ Γ₂
(_ ∣ e ∙ˢ σ) _ zero     = e
(_ ∣ e ∙ˢ σ) _ (suc x)  = σ _ x

_∣_∙ˢ*_ : ∀ (η : Φ →ˢ Ψ) → ∀ {J} (T : Type Ψ J) → η ∣ Γ₁ ⇒ˢ Γ₂ → (T ∙ˢ η) ∣ ((Γ₁ ▷*) {J}) ⇒ˢ Γ₂
(_ ∣ T ∙ˢ* σ) _ (suc* x) = σ _ x

-- lifting a substitution
--! Lifting
_∣_⇑ˢ_ : ∀ (η : Φ →ˢ Ψ) → η ∣ Γ₁ ⇒ˢ Γ₂ → ∀ T → η ∣ (Γ₁ ▷ T) ⇒ˢ (Γ₂ ▷ (T [ η ]ˢ))
(η ∣ _ ⇑ˢ T) _ zero    = ` zero
(η ∣ σ ⇑ˢ T) _ (suc x) = Weaken (σ _ x)

-- type lifting
--! TLifting
_∣_↑ˢ*_ : ∀ (η : Φ →ˢ Ψ) → η ∣ Γ₁ ⇒ˢ Γ₂ → ∀ J → (η ↑ˢ J) ∣ ((Γ₁ ▷*) {J}) ⇒ˢ ((Γ₂ ▷*) {J})
(η ∣ σ ↑ˢ* J) _ (suc* x) = wkᴿ J ∣ (σ _ x) [ wkᴿ* J ]ᴿ


postulate 
  lemˢ : T₁ ≡β T → (T₁ [ η ]ˢ) ≡β (T [ η ]ˢ)


-- expression substitution - traversal
--! Traversal
_∣_[_]ˢ : (η : Φ →ˢ Ψ) → Expr Γ₁ T → η ∣ Γ₁ ⇒ˢ Γ₂ → Expr Γ₂ (T [ η ]ˢ)
η  ∣ (` x) [ σ ]ˢ      = σ _ x
η  ∣ (λx e) [ σ ]ˢ     = λx (η ∣ e [ η ∣ σ ⇑ˢ _ ]ˢ)
η  ∣ (Λα e) [ σ ]ˢ     = Λα ((η ↑ˢ _) ∣ e [ η ∣ σ ↑ˢ* _ ]ˢ)
η  ∣ (e · e₁) [ σ ]ˢ   = (η ∣ e [ σ ]ˢ) · (η ∣ e₁ [ σ ]ˢ)
η  ∣ (e ·* T′) [ σ ]ˢ  = (η ∣ e [ σ ]ˢ) ·* (T′ [ η ]ˢ)
η  ∣ conv e x [ σ ]ˢ  = conv (η ∣ e [ σ ]ˢ) (lemˢ {η = η} x)

--! CompDefinition
_,_∣_⨾ˢ_ : ∀ (η₁ : Φ →ˢ Ψ) (η₂ : Ψ →ˢ Θ) → η₁ ∣ Γ₁ ⇒ˢ Γ₂ → η₂ ∣ Γ₂ ⇒ˢ Γ₃ → (η₁ ⨟ˢ η₂) ∣ Γ₁ ⇒ˢ Γ₃
(_ , _ ∣ σ₁ ⨾ˢ σ₂) _ x = _ ∣ (σ₁ _ x) [ σ₂ ]ˢ

-- single substitution, semantics, and progress
--! <
--! Sem >
--! SingleSub {
_[_] : Expr (Γ ▷ T′) T → Expr Γ T′ → Expr Γ T
e [ e′ ] = idˢ ∣ e [ idˢ ∣ e′ ∙ˢ Idˢ ]ˢ

_[*_*] : Expr (Γ ▷*) T → (T′ : Type Φ J) → Expr Γ (T [ T′ ]*)
e [* T′ *] = (T′ ∙ˢ idˢ) ∣ e [ idˢ ∣ T′ ∙ˢ* Idˢ ]ˢ
--! }

--! Definition
data _⟶_ : Expr Γ T → Expr Γ T → Set where
  β-λ   : (λx e₁ · e₂) ⟶ (e₁ [ e₂ ])
  β-Λ   : (Λα e ·* T′) ⟶ (e [* T′ *])
  ξ-·   : e₁ ⟶ e₁′ → (e₁ · e₂) ⟶ (e₁′ · e₂)
  ξ-·*  : e ⟶ e′ → (e ·* T) ⟶ (e′ ·* T)
  ξ-Λ   : e ⟶ e′ → (Λα e) ⟶ (Λα e′)
  ξ-conv : ∀{eq : T ≡β T′} → e ⟶ e′ → conv e eq ⟶ conv e′ eq
  β-conv : ∀{eq : T ≡β T} → conv e eq ⟶ e

data _⟶*_ : Expr Γ T → Expr Γ T → Set where
  ⟶refl  : e ⟶* e
  ⟶trans : e₁ ⟶ e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; contradiction)

--! ProgressDefs {
data Value : Expr Γ T → Set where
  λx : (e : Expr (Γ ▷ T₁) T₂) → Value (λx e)
  Λα : Value e → Value (Λα e)

data Progress : Expr Γ T → Set where
  done : (v : Value e) → Progress e
  step : (e⟶e′ : e ⟶ e′) → Progress e

data NoVar : Ctx Φ → Set where
  ∅   : NoVar ∅
  _▷* : NoVar Γ → NoVar {Φ ▷* J} (Γ ▷*)

noVar : NoVar Γ → ¬ (Γ ∋ T)
noVar (nv ▷*) (suc* x) = noVar nv x
--! }

--! FORewrite
{-# REWRITE β≡* #-}

admissible : ∀{A B : Type Φ J} → A ≡β B → A ≡ B
admissible (β≡β B A)      = refl
admissible (refl≡β A)     = refl
admissible (sym≡β x)      = sym (admissible x)
admissible (trans≡β x x₁) = trans (admissible x) (admissible x₁)
admissible (⇒≡β x x₁)     = cong₂ _⇒_ (admissible x) (admissible x₁)
admissible (Π≡β x)        = cong ∀α (admissible x)
admissible (ƛ≡β x)        = cong λα (admissible x)
admissible (·≡β x x₁)     = cong₂ _$_ (admissible x) (admissible x₁)

--! Progress
progress : NoVar Γ → (e : Expr Γ T) → Progress e
progress nv (` x) = ⊥-elim (noVar nv x)
progress nv (λx e) = done (λx e)
progress nv (e · e′)
  with progress nv e
... | done (λx e₁) = step β-λ
... | step e⟶e′ = step (ξ-· e⟶e′)
progress nv (Λα e)
  with progress (nv ▷*) e
... | done v = done (Λα v)
... | step e⟶e′ = step (ξ-Λ e⟶e′)
progress nv (e ·* T′)
  with progress nv e
... | done (Λα v) = step β-Λ
... | step e⟶e′ = step (ξ-·* e⟶e′)
progress nv (conv e eq) 
  with refl ← admissible eq
  with progress nv e
... | done v = step β-conv
... | step e⟶e′ = step (ξ-conv e⟶e′)

-- execution

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; ∃-syntax; _,_; _×_)

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
`α = ` zero
`β : Type ((Φ ▷* K) ▷* J) K
`β = ` (suc zero)
`κ `γ : Type (((Φ ▷* K) ▷* I) ▷* J) K
`κ = ` (suc (suc zero))
`γ = `κ

Λκ Λβ : Expr (Γ ▷*) T → Expr Γ (∀α T)
Λκ = Λα
Λβ = Λα

`x : Expr (Γ ▷ T) T
`x = ` zero
`y `g : Expr ((Γ ▷ T) ▷ T₁) T
`y = ` (suc zero)
`g = ` (suc zero)
`z `f : Expr (((Γ ▷ T) ▷ T₂) ▷ T₁) T
`z = ` (suc (suc zero))
`f = `z

-- Church numerals

-- ∀ α (α→α) → α→α

--! <
--! <
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
succᶜ = λx (Λα (λg (λx (`g · ((((` (suc (suc (suc* zero)))) ·* `α) · `g) · `x)))))

--! FCNTwo
twoᶜ : Expr ∅ ℕᶜ
twoᶜ = succᶜ · (succᶜ · zeroᶜ)

fourᶜ : Expr ∅ ℕᶜ
fourᶜ = succᶜ · (succᶜ · (succᶜ · (succᶜ · zeroᶜ)))

--! FCNFour
two+twoᶜ : Expr ∅ ℕᶜ
two+twoᶜ = ((twoᶜ ·* ℕᶜ) · succᶜ) · twoᶜ
