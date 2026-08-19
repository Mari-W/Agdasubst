-- ════════════════════════════════════════════════════════════════════
-- SYSTEM F, intrinsically typed, with a σ-CALCULUS INSTALLED AS AGDA
-- REWRITE RULES.  This is the paper's main development.
--
-- What it shows:
--
--  (1) A CONFLUENT curation of the σ-calculus with first-class
--      renamings — λσ⇑-style: lifting is a first-class opaque symbol,
--      there are no η-rules, and coincidence is oriented ˢ→ᴿ.  The
--      whole set is registered with REWRITE pragmas and certified by
--      Agda's --local-confluence-check (§3).
--
--  (2) TRANSFER HEAVEN at the type level: with those rules installed
--      every index equation of the intrinsically typed syntax holds
--      definitionally, so renaming and substitution on expressions are
--      defined, traversed and composed without a single transport
--      (§5, §6).
--
--  (3) TRANSFER HELL at the expression level: the expression-level
--      mirror of the σ-calculus is an exact equational theory — every
--      law in §7 is an Agda theorem — yet it cannot be installed as a
--      rewrite system.  §7 records why.
--
-- The only postulate is fun-ext.
-- ════════════════════════════════════════════════════════════════════
{-# OPTIONS --rewriting --local-confluence-check #-}
module SystemF where
open import Agda.Builtin.Equality.Rewrite public

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; module ≡-Reasoning)
open ≡-Reasoning

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin using (zero; suc) renaming (Fin to Var)

infixr 5 _⇒_
infix 6 `_

-- ══════════════ §1  Types ══════════════════════════════════════════
--! SF >
--! Type >
--! Definition
data Type (n : Nat) : Set where
  `_   : Var n → Type n
  ∀α   : Type (1 + n) → Type n
  _⇒_  : Type n → Type n → Type n

--! Example
_ : Type 0                      -- a closed type:  ∀α. α→α
_ = ∀α (` zero ⇒ ` zero)
_ : Type 0 -- ∀αβ. α→β→α
_ = ∀α (∀α (` suc zero ⇒ ` zero ⇒ ` suc zero))

variable
  n n′ n₁ n₂ n₃ : Nat
  α α′ α₁ α₂ α₃ : Var n
  T T′ T₁ T₂ T₃ : Type n

-- ══════════════ §2  Renaming and substitution on types ═════════════

--! Renaming
-- renamings
Ren : Nat → Nat → Set
Ren n₁ n₂ = Var n₁ → Var n₂

--! RenamingOpaque {
opaque
  -- weakening
  wkᴿ : Ren n (1 + n)
  wkᴿ = suc

  -- identity renaming
  idᴿ : Ren n n
  idᴿ α = α

  -- extend with new variable
  _∙ᴿ_ : Var n₂ → Ren n₁ n₂ → Ren (1 + n₁) n₂
  (α ∙ᴿ ζ) zero     = α
  (_ ∙ᴿ ζ) (suc α)  = ζ α

  -- apply renaming to variable
  _&ᴿ_ : Var n₁ → Ren n₁ n₂ → Var n₂
  α &ᴿ ζ = ζ α

  -- left-to-right composition
  _⨟ᴿ_ : Ren n₁ n₂ → Ren n₂ n₃ → Ren n₁ n₃
  (ζ₁ ⨟ᴿ ζ₂) α = ζ₂ (ζ₁ α)

-- lifting: FIRST-CLASS (opaque) — eliminating it forces the η-rules
-- into the rewrite system, and η is incompatible with confluence
opaque
  _↑ᴿ : Ren n₁ n₂ → Ren (1 + n₁) (1 + n₂)
  _↑ᴿ ζ = zero ∙ᴿ (ζ ⨟ᴿ wkᴿ)

-- apply renaming to a type (transparent: these clauses ARE the
-- traversal rules, and expression indices under Λ can only be
-- decomposed by them)
_[_]ᴿ : Type n₁ → Ren n₁ n₂ → Type n₂
(` α) [ ζ ]ᴿ      = ` (α &ᴿ ζ)
(∀α T) [ ζ ]ᴿ     = ∀α (T [ ζ ↑ᴿ ]ᴿ)
(T₁ ⇒ T₂) [ ζ ]ᴿ  = (T₁ [ ζ ]ᴿ) ⇒ (T₂ [ ζ ]ᴿ)
--! }

variable
  ζ ζ′ ζ₁ ζ₂ ζ₃ : Ren n₁ n₂

--! Substitution
-- substitutions
Sub : Nat → Nat → Set
Sub n₁ n₂ = Var n₁ → Type n₂

--! SubstitutionOpaque {
opaque
  -- lift renaming to substitution
  ⟨_⟩ : Ren n₁ n₂ → Sub n₁ n₂
  ⟨ ζ ⟩ α = ` (α &ᴿ ζ)

  -- extend with new type
  _∙ˢ_ : Type n₂ → Sub n₁ n₂ → Sub (1 + n₁) n₂
  (T ∙ˢ η) zero     = T
  (T ∙ˢ η) (suc α)  = η α

  -- apply substitution to variable
  _&ˢ_ : Var n₁ → Sub n₁ n₂ → Type n₂
  α &ˢ η = η α


-- lifting: FIRST-CLASS (opaque)
opaque
  _↑ˢ : Sub n₁ n₂ → Sub (1 + n₁) (1 + n₂)
  _↑ˢ η = (` zero) ∙ˢ λ α → (η α) [ wkᴿ ]ᴿ

-- apply substitution to a type (transparent: these clauses ARE the
-- traversal rules)
_[_]ˢ : Type n₁ → Sub n₁ n₂ → Type n₂
(` α) [ η ]ˢ      = α &ˢ η
(∀α T) [ η ]ˢ     = ∀α (T [ η ↑ˢ ]ˢ)
(T₁ ⇒ T₂) [ η ]ˢ  = (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)

opaque
  -- left-to-right composition
  _⨟ˢ_ : Sub n₁ n₂ → Sub n₂ n₃ → Sub n₁ n₃
  (η₁ ⨟ˢ η₂) α = (η₁ α) [ η₂ ]ˢ
--! }

variable
  η η′ η₁ η₂ η₃ : Sub n₁ n₂

-- ══════════════ §3  The σ-calculus, confluent curation ═════════════
-- λσ⇑-style: lifting is a first-class symbol, composition at a
-- variable PUSHES on the renaming side and FOLDS on the substitution
-- side, there are NO η-rules, and coincidence is oriented ˢ→ᴿ, so the
-- ᴿ-world is the normal form of a renaming-shaped substitution.  The
-- curation is what makes the set locally confluent; the naive
-- traversal-plus-composition set is not.
opaque
  unfolding wkᴿ idᴿ _∙ᴿ_ _&ᴿ_ _⨟ᴿ_ _↑ᴿ ⟨_⟩ _∙ˢ_ _&ˢ_ _↑ˢ _⨟ˢ_
  --! RenamingBeta {
  `beta-ext-zero    : zero  &ᴿ (α ∙ᴿ ζ)          ≡ α
  `beta-ext-suc     : suc α &ᴿ (α′ ∙ᴿ ζ)         ≡ α &ᴿ ζ
  `beta-id          : α &ᴿ idᴿ                   ≡ α
  `beta-wk          : α &ᴿ wkᴿ                   ≡ suc α
  `beta-lift-zero   : zero &ᴿ (ζ ↑ᴿ)             ≡ zero
  `beta-lift-suc    : suc α &ᴿ (ζ ↑ᴿ)            ≡ suc (α &ᴿ ζ)
  -- composition at a variable PUSHES here (the substitution side
  -- folds instead).  A fold rule at this level would pair unjoinably
  -- with the applied rules `beta-id and `beta-wk, whose variable
  -- arguments are bare metavariables, so nested applications simply
  -- stay applied.  For the same reason `distributivity below is a
  -- lemma and not a rewrite; the applied-⨟ family replaces it.
  `beta-comp        : α &ᴿ (ζ₁ ⨟ᴿ ζ₂)            ≡ (α &ᴿ ζ₁) &ᴿ ζ₂
  `associativity    : (ζ₁ ⨟ᴿ ζ₂) ⨟ᴿ ζ₃           ≡ ζ₁ ⨟ᴿ (ζ₂ ⨟ᴿ ζ₃)
  `distributivity   : (α ∙ᴿ ζ₁) ⨟ᴿ ζ₂            ≡ (α &ᴿ ζ₂) ∙ᴿ (ζ₁ ⨟ᴿ ζ₂)
  `interact         : wkᴿ ⨟ᴿ (α ∙ᴿ ζ)            ≡ ζ
  `interact-⨟       : wkᴿ ⨟ᴿ ((α ∙ᴿ ζ) ⨟ᴿ ζ′)    ≡ ζ ⨟ᴿ ζ′
  `comp-idᵣ         : ζ ⨟ᴿ idᴿ                   ≡ ζ
  `comp-idₗ         : idᴿ ⨟ᴿ ζ                   ≡ ζ
  `lift-id          : (idᴿ {n}) ↑ᴿ               ≡ idᴿ
  `lift-wk          : wkᴿ ⨟ᴿ (ζ ↑ᴿ)              ≡ ζ ⨟ᴿ wkᴿ
  `lift-cons        : (ζ ↑ᴿ) ⨟ᴿ (α ∙ᴿ ζ′)        ≡ α ∙ᴿ (ζ ⨟ᴿ ζ′)
  `lift-cons-⨟      : (ζ ↑ᴿ) ⨟ᴿ ((α ∙ᴿ ζ′) ⨟ᴿ ζ₃) ≡ (α &ᴿ ζ₃) ∙ᴿ (ζ ⨟ᴿ (ζ′ ⨟ᴿ ζ₃))
  `lift-fusion      : (ζ₁ ↑ᴿ) ⨟ᴿ (ζ₂ ↑ᴿ)         ≡ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ
  `lift-wk-⨟        : wkᴿ ⨟ᴿ ((ζ ↑ᴿ) ⨟ᴿ ζ′)      ≡ ζ ⨟ᴿ (wkᴿ ⨟ᴿ ζ′)
  `lift-fusion-⨟    : (ζ₁ ↑ᴿ) ⨟ᴿ ((ζ₂ ↑ᴿ) ⨟ᴿ ζ′) ≡ ((ζ₁ ⨟ᴿ ζ₂) ↑ᴿ) ⨟ᴿ ζ′
  --! }
  -- η-rules: LEMMAS ONLY — the applied rules evaluate the η-redex's
  -- head, so no orientation of these is locally confluent
  `η-id             : zero {n} ∙ᴿ wkᴿ            ≡ idᴿ
  `η-law            : (zero &ᴿ ζ) ∙ᴿ (wkᴿ ⨟ᴿ ζ)  ≡ ζ

  --! SubstitutionBeta {
  beta-ext-zero     : zero  &ˢ (T ∙ˢ η)              ≡ T
  beta-ext-suc      : suc α &ˢ (T ∙ˢ η)              ≡ α &ˢ η
  beta-rename       : α &ˢ ⟨ ζ ⟩                     ≡ ` (α &ᴿ ζ)
  beta-lift-zero    : zero &ˢ (η ↑ˢ)                 ≡ ` zero
  beta-lift-suc     : suc α &ˢ (η ↑ˢ)                ≡ α &ˢ (η ⨟ˢ ⟨ wkᴿ ⟩)
  beta-⟨⟩-⨟         : α &ˢ (⟨ ζ ⟩ ⨟ˢ η)              ≡ (α &ᴿ ζ) &ˢ η
  beta-lift-zero-⨟  : zero &ˢ ((η ↑ˢ) ⨟ˢ η′)         ≡ zero &ˢ η′
  beta-lift-suc-⨟   : suc α &ˢ ((η ↑ˢ) ⨟ˢ η′)        ≡ α &ˢ (η ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ η′))
  beta-fold         : (α &ˢ η₁) [ η₂ ]ˢ              ≡ α &ˢ (η₁ ⨟ˢ η₂)
  beta-fold-ˢᴿ      : (α &ˢ η) [ ζ ]ᴿ                ≡ α &ˢ (η ⨟ˢ ⟨ ζ ⟩)
  beta-lift-ren-∙   : (α &ᴿ (ζ ↑ᴿ)) &ˢ (T ∙ˢ η)      ≡ α &ˢ (T ∙ˢ (⟨ ζ ⟩ ⨟ˢ η))
  --! }
  --! SubstitutionInteraction {
  associativity     : (η₁ ⨟ˢ η₂) ⨟ˢ η₃               ≡ η₁ ⨟ˢ (η₂ ⨟ˢ η₃)
  distributivity    : (T ∙ˢ η₁) ⨟ˢ η₂                ≡ (T [ η₂ ]ˢ) ∙ˢ (η₁ ⨟ˢ η₂)
  interact          : ⟨ wkᴿ ⟩ ⨟ˢ (T ∙ˢ η)            ≡ η
  comp-idᵣ          : η ⨟ˢ ⟨ idᴿ ⟩                   ≡ η
  comp-idₗ          : ⟨ idᴿ ⟩ ⨟ˢ η                   ≡ η
  lift-id           : (⟨ idᴿ {n} ⟩ ↑ˢ)               ≡ ⟨ idᴿ ⟩
  lift-wk           : ⟨ wkᴿ ⟩ ⨟ˢ (η ↑ˢ)              ≡ η ⨟ˢ ⟨ wkᴿ ⟩
  lift-cons         : (η ↑ˢ) ⨟ˢ (T ∙ˢ η′)            ≡ T ∙ˢ (η ⨟ˢ η′)
  lift-fusion       : (η₁ ↑ˢ) ⨟ˢ (η₂ ↑ˢ)             ≡ (η₁ ⨟ˢ η₂) ↑ˢ
  lift-wk-⨟         : ⟨ wkᴿ ⟩ ⨟ˢ ((η ↑ˢ) ⨟ˢ η′)      ≡ η ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ η′)
  lift-fusion-⨟     : (η₁ ↑ˢ) ⨟ˢ ((η₂ ↑ˢ) ⨟ˢ η′)     ≡ ((η₁ ⨟ˢ η₂) ↑ˢ) ⨟ˢ η′
  -- embedded composition: BARE pairs fold toward ᴿ (⟨⟩-comp), while
  -- composites under a continuation split (⟨⟩-split-⨟) — the pair
  -- normalizes bare forms to ⟨ζ₁⨟ᴿζ₂⟩ and continued forms to
  -- right-nested ⟨⟩-chains, and each closes the other's peaks
  ⟨⟩-comp           : ⟨ ζ₁ ⟩ ⨟ˢ ⟨ ζ₂ ⟩               ≡ ⟨ ζ₁ ⨟ᴿ ζ₂ ⟩
  ⟨⟩-split          : ⟨ ζ₁ ⨟ᴿ ζ₂ ⟩                   ≡ ⟨ ζ₁ ⟩ ⨟ˢ ⟨ ζ₂ ⟩
  ⟨⟩-split-⨟        : ⟨ ζ₁ ⨟ᴿ ζ₂ ⟩ ⨟ˢ η              ≡ ⟨ ζ₁ ⟩ ⨟ˢ (⟨ ζ₂ ⟩ ⨟ˢ η)
  ⟨⟩-↑-cons         : ⟨ ζ ↑ᴿ ⟩ ⨟ˢ (T ∙ˢ η)           ≡ T ∙ˢ (⟨ ζ ⟩ ⨟ˢ η)
  -- the embedded interaction laws for wk-precomposition
  ⟨⟩-wk-cons        : ⟨ wkᴿ ⟩ ⨟ˢ ⟨ α ∙ᴿ ζ ⟩          ≡ ⟨ ζ ⟩
  ⟨⟩-wk-cons-⨟      : ⟨ wkᴿ ⟩ ⨟ˢ (⟨ α ∙ᴿ ζ ⟩ ⨟ˢ η)   ≡ ⟨ ζ ⟩ ⨟ˢ η
  ⟨⟩-wk-lift        : ⟨ wkᴿ ⟩ ⨟ˢ ⟨ ζ ↑ᴿ ⟩            ≡ ⟨ ζ ⟩ ⨟ˢ ⟨ wkᴿ ⟩
  ⟨⟩-wk-lift-⨟      : ⟨ wkᴿ ⟩ ⨟ˢ (⟨ ζ ↑ᴿ ⟩ ⨟ˢ η)     ≡ ⟨ ζ ⟩ ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ η)
  -- the embedded lift-fusion laws.  Only the RR flavour is a REWRITE:
  -- the RS/SR flavours produce (⟨ζ⟩ ⨟ η) ↑ˢ forms whose lift-id
  -- instances hit the irreducible ⟨ζ↑ᴿ⟩ ≠ ⟨ζ⟩↑ˢ canonical-form split
  -- (registering lift-⟨⟩ in either direction is non-confluent)
  ⟨⟩-lift-lift      : ⟨ ζ₁ ↑ᴿ ⟩ ⨟ˢ ⟨ ζ₂ ↑ᴿ ⟩         ≡ ⟨ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ ⟩
  ⟨⟩-lift-lift-⨟    : ⟨ ζ₁ ↑ᴿ ⟩ ⨟ˢ (⟨ ζ₂ ↑ᴿ ⟩ ⨟ˢ η)  ≡ ⟨ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ ⟩ ⨟ˢ η
  `beta-lift-fusion : (α &ᴿ (ζ₁ ↑ᴿ)) &ᴿ (ζ₂ ↑ᴿ)      ≡ α &ᴿ ((ζ₁ ⨟ᴿ ζ₂) ↑ᴿ)
  ⟨⟩-lift-RS        : ⟨ ζ ↑ᴿ ⟩ ⨟ˢ (η ↑ˢ)             ≡ (⟨ ζ ⟩ ⨟ˢ η) ↑ˢ
  ⟨⟩-lift-RS-⨟      : ⟨ ζ ↑ᴿ ⟩ ⨟ˢ ((η ↑ˢ) ⨟ˢ η′)     ≡ ((⟨ ζ ⟩ ⨟ˢ η) ↑ˢ) ⨟ˢ η′
  beta-lift-ren-↑   : (α &ᴿ (ζ ↑ᴿ)) &ˢ (η ↑ˢ)        ≡ α &ˢ ((⟨ ζ ⟩ ⨟ˢ η) ↑ˢ)
  beta-lift-ren-↑-⨟ : (α &ᴿ (ζ ↑ᴿ)) &ˢ ((η ↑ˢ) ⨟ˢ η′) ≡ α &ˢ (((⟨ ζ ⟩ ⨟ˢ η) ↑ˢ) ⨟ˢ η′)
  ⟨⟩-lift-SR-comp   : (η ↑ˢ) ⨟ˢ ⟨ (ζ ↑ᴿ) ⨟ᴿ ζ′ ⟩     ≡ ((η ⨟ˢ ⟨ ζ ⟩) ↑ˢ) ⨟ˢ ⟨ ζ′ ⟩
  ⟨⟩-lift-SR        : (η ↑ˢ) ⨟ˢ ⟨ ζ ↑ᴿ ⟩             ≡ (η ⨟ˢ ⟨ ζ ⟩) ↑ˢ
  ⟨⟩-lift-SR-⨟      : (η ↑ˢ) ⨟ˢ (⟨ ζ ↑ᴿ ⟩ ⨟ˢ η′)     ≡ ((η ⨟ˢ ⟨ ζ ⟩) ↑ˢ) ⨟ˢ η′
  --! }
  -- η-rules: lemmas only (see above)
  η-id              : (` zero {n}) ∙ˢ ⟨ wkᴿ ⟩        ≡ ⟨ idᴿ ⟩
  η-law             : (zero &ˢ η) ∙ˢ (⟨ wkᴿ ⟩ ⨟ˢ η)  ≡ η
  -- lift-elimination: LEMMA only — as a rule it drags η-id into the
  -- join of identityᵣˢ with the ∀-clause, and η is fatal for confluence
  beta-lift         : η ↑ˢ                           ≡ (` zero) ∙ˢ (η ⨟ˢ ⟨ wkᴿ ⟩)

  --! Monad
  identityᵣ                  : T [ idᴿ ]ᴿ           ≡ T
  compositionalityᴿᴿ         : (T [ ζ₁ ]ᴿ) [ ζ₂ ]ᴿ  ≡ T [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ
  compositionalityᴿˢ         : (T [ ζ₁ ]ᴿ) [ η₂ ]ˢ  ≡ T [ ⟨ ζ₁ ⟩ ⨟ˢ η₂ ]ˢ
  compositionalityˢᴿ         : (T [ η₁ ]ˢ) [ ζ₂ ]ᴿ  ≡ T [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ
  compositionalityˢˢ         : (T [ η₁ ]ˢ) [ η₂ ]ˢ  ≡ T [ η₁ ⨟ˢ η₂ ]ˢ

  -- THE transfer law, between the two worlds.  Only `coincidence` is
  -- registered, i.e. it is oriented ˢ→ᴿ: a renaming-shaped
  -- substitution normalises to a renaming, so the substitution
  -- traversal disappears from every goal that has one.  `ren-to-sub`
  -- is its converse, kept as a lemma.
  --! Coincidence
  coincidence       : T [ ⟨ ζ ⟩ ]ˢ      ≡ T [ ζ ]ᴿ
  ren-to-sub        : T [ ζ ]ᴿ          ≡ T [ ⟨ ζ ⟩ ]ˢ

  identityᵣˢ        : T [ ⟨ idᴿ ⟩ ]ˢ     ≡ T

  `beta-ext-zero  = refl
  `beta-ext-suc   = refl
  `beta-id        = refl
  `beta-wk        = refl
  `beta-lift-zero = refl
  `beta-lift-suc  = refl
  `beta-comp      = refl

  `associativity   = refl
  `distributivity  = fun-ext λ { zero → refl; (suc α) → refl }
  `interact        = refl
  `interact-⨟      = refl
  `comp-idᵣ        = refl
  `comp-idₗ        = refl
  `lift-id         = fun-ext λ { zero → refl; (suc α) → refl }
  `lift-wk         = refl
  `lift-cons       = fun-ext λ { zero → refl; (suc α) → refl }
  `lift-cons-⨟     = fun-ext λ { zero → refl; (suc α) → refl }
  `lift-fusion     = fun-ext λ { zero → refl; (suc α) → refl }
  `lift-wk-⨟       = fun-ext λ α → refl
  `lift-fusion-⨟   = fun-ext λ { zero → refl; (suc α) → refl }
  `η-id            = fun-ext λ { zero → refl; (suc α) → refl }
  `η-law           = fun-ext λ { zero → refl; (suc α) → refl }

  beta-ext-zero  = refl
  beta-ext-suc   = refl
  beta-rename    = refl
  beta-lift-zero = refl
  beta-lift-suc {α = α} {η = η} = sym (coincidence {T = η α})
  beta-⟨⟩-⨟      = refl
  beta-lift-zero-⨟ = refl
  beta-lift-suc-⨟ {α = α} {η = η} {η′ = η′} = compositionalityᴿˢ {T = η α}
  beta-fold      = refl
  beta-fold-ˢᴿ {α = α} {η = η} = sym (coincidence {T = η α})
  beta-lift-ren-∙ {α = zero}   = refl
  beta-lift-ren-∙ {α = suc α}  = refl

  associativity {η₁ = η₁} = fun-ext (λ α → compositionalityˢˢ {T = η₁ α})
  distributivity  = fun-ext λ { zero → refl; (suc α) → refl }
  interact        = refl
  comp-idᵣ        = fun-ext (λ α → identityᵣˢ)
  comp-idₗ        = refl
  lift-id         = fun-ext λ { zero → refl; (suc α) → refl }
  lift-wk {η = η} = fun-ext λ α → sym (coincidence {T = η α})
  lift-cons {η = η} {T = T} {η′ = η′} = fun-ext λ
    { zero → refl
    ; (suc α) → trans (compositionalityᴿˢ {T = η α})
                      (cong ((η α) [_]ˢ) (interact {T = T} {η = η′})) }
  lift-wk-⨟ {η = η} {η′ = η′} = fun-ext λ α → compositionalityᴿˢ {T = η α}
  lift-fusion-⨟ {η₁ = η₁} {η₂ = η₂} {η′ = η′} =
    trans (sym (associativity {η₁ = η₁ ↑ˢ} {η₂ = η₂ ↑ˢ} {η₃ = η′}))
          (cong (_⨟ˢ η′) lift-fusion)
  ⟨⟩-comp         = fun-ext λ α → refl
  ⟨⟩-split        = fun-ext λ α → refl
  ⟨⟩-split-⨟      = fun-ext λ α → refl
  ⟨⟩-wk-cons      = fun-ext λ α → refl
  ⟨⟩-wk-cons-⨟    = fun-ext λ α → refl
  ⟨⟩-wk-lift      = fun-ext λ α → refl
  ⟨⟩-wk-lift-⨟    = fun-ext λ α → refl
  ⟨⟩-lift-lift    = fun-ext λ { zero → refl; (suc α) → refl }
  ⟨⟩-lift-lift-⨟  = fun-ext λ { zero → refl; (suc α) → refl }
  `beta-lift-fusion {α = zero}  = refl
  `beta-lift-fusion {α = suc α} = refl
  ⟨⟩-lift-RS      = fun-ext λ { zero → refl; (suc α) → refl }
  ⟨⟩-lift-RS-⨟    = fun-ext λ { zero → refl; (suc α) → refl }
  beta-lift-ren-↑ {α = zero}  = refl
  beta-lift-ren-↑ {α = suc α} = refl
  beta-lift-ren-↑-⨟ {α = zero}  = refl
  beta-lift-ren-↑-⨟ {α = suc α} = refl
  ⟨⟩-↑-cons       = fun-ext λ { zero → refl; (suc α) → refl }
  η-id            = fun-ext λ { zero → refl; (suc α) → refl }
  η-law           = fun-ext λ { zero → refl; (suc α) → refl }
  beta-lift       = cong ((` zero) ∙ˢ_) (sym (fun-ext λ x → coincidence))

  identityᵣ {T = (` α)}      = refl
  identityᵣ {T = (∀α T)}     = cong ∀α (trans (cong (T [_]ᴿ) `lift-id) (identityᵣ {T = T}))
  identityᵣ {T = (T₁ ⇒ T₂)}  = cong₂ _⇒_ (identityᵣ {T = T₁}) (identityᵣ {T = T₂})

  lift-coincidence : ∀ {n₁ n₂} {ζ : Ren n₁ n₂} → (⟨ ζ ⟩ ↑ˢ) ≡ ⟨ ζ ↑ᴿ ⟩
  lift-coincidence = fun-ext λ { zero → refl; (suc α) → refl }

  coincidence {T = ` α}            = refl
  coincidence {T = ∀α T} {ζ = ζ}   = cong ∀α (trans (cong (T [_]ˢ) lift-coincidence) coincidence)
  coincidence {T = T₁ ⇒ T₂}        = cong₂ _⇒_ coincidence coincidence

  ren-to-sub = sym coincidence

  lift-compositionalityᴿᴿ : ∀ {n₁ n₂ n₃} {ζ₁ : Ren n₁ n₂} {ζ₂ : Ren n₂ n₃} → (ζ₁ ↑ᴿ) ⨟ᴿ (ζ₂ ↑ᴿ) ≡ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ
  lift-compositionalityᴿᴿ = fun-ext λ { zero → refl; (suc α) → refl }

  compositionalityᴿᴿ {T = ` α}      = refl
  compositionalityᴿᴿ {T = ∀α T}     = cong ∀α (trans compositionalityᴿᴿ (cong (T [_]ᴿ) lift-compositionalityᴿᴿ))
  compositionalityᴿᴿ {T = T₁ ⇒ T₂}  = cong₂ _⇒_ compositionalityᴿᴿ compositionalityᴿᴿ

  lift-compositionalityᴿˢ : ∀ {n₁ n₂ n₃} {ζ₁ : Ren n₁ n₂} {η₂ : Sub n₂ n₃} → (⟨ ζ₁ ↑ᴿ ⟩ ⨟ˢ (η₂ ↑ˢ)) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ↑ˢ)
  lift-compositionalityᴿˢ = fun-ext λ { zero → refl; (suc α) → refl }

  compositionalityᴿˢ {T = ` α}      = refl
  compositionalityᴿˢ {T = ∀α T}     = cong ∀α (trans (compositionalityᴿˢ {T = T}) (cong (T [_]ˢ) lift-compositionalityᴿˢ))
  compositionalityᴿˢ {T = T₁ ⇒ T₂}  = cong₂ _⇒_ (compositionalityᴿˢ {T = T₁}) (compositionalityᴿˢ {T = T₂})

  lift-compositionalityˢᴿ : ∀ {n₁ n₂ n₃} {η₁ : Sub n₁ n₂} {ζ₂ : Ren n₂ n₃} → ((η₁ ↑ˢ) ⨟ˢ ⟨ ζ₂ ↑ᴿ ⟩) ≡ ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ↑ˢ)
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

  lift-compositionalityˢˢ : ∀ {n₁ n₂ n₃} {η₁ : Sub n₁ n₂} {η₂ : Sub n₂ n₃} → ((η₁ ↑ˢ) ⨟ˢ (η₂ ↑ˢ)) ≡ ((η₁ ⨟ˢ η₂) ↑ˢ)
  lift-compositionalityˢˢ {η₁ = η₁} {η₂ = η₂} = fun-ext λ { zero → refl; (suc α) →
    let T = η₁ α in
    begin
      (T [ wkᴿ ]ᴿ) [ η₂ ↑ˢ ]ˢ        ≡⟨ compositionalityᴿˢ {T = T} ⟩
      T [ ⟨ wkᴿ ⟩ ⨟ˢ (η₂ ↑ˢ) ]ˢ      ≡⟨ cong (T [_]ˢ) (fun-ext λ α → sym (coincidence {T = η₂ α})) ⟩
      T [ η₂ ⨟ˢ ⟨ wkᴿ ⟩ ]ˢ           ≡⟨ sym (compositionalityˢᴿ {T = T}) ⟩
      (T [ η₂ ]ˢ) [ wkᴿ ]ᴿ           ∎ }

  lift-fusion     = lift-compositionalityˢˢ
  ⟨⟩-lift-SR      = lift-compositionalityˢᴿ
  ⟨⟩-lift-SR-comp {η = η} {ζ = ζ} {ζ′ = ζ′} = fun-ext λ { zero → refl; (suc α) →
    let T = η α in
    begin
      (T [ wkᴿ ]ᴿ) [ ⟨ (ζ ↑ᴿ) ⨟ᴿ ζ′ ⟩ ]ˢ
    ≡⟨ compositionalityᴿˢ {T = T} {ζ₁ = wkᴿ} {η₂ = ⟨ (ζ ↑ᴿ) ⨟ᴿ ζ′ ⟩} ⟩
      T [ ⟨ wkᴿ ⟩ ⨟ˢ ⟨ (ζ ↑ᴿ) ⨟ᴿ ζ′ ⟩ ]ˢ
    ≡⟨ cong (T [_]ˢ) (⟨⟩-comp {ζ₁ = wkᴿ} {ζ₂ = (ζ ↑ᴿ) ⨟ᴿ ζ′}) ⟩
      T [ ⟨ wkᴿ ⨟ᴿ ((ζ ↑ᴿ) ⨟ᴿ ζ′) ⟩ ]ˢ
    ≡⟨⟩
      T [ ⟨ ζ ⨟ᴿ (wkᴿ ⨟ᴿ ζ′) ⟩ ]ˢ
    ≡⟨ cong (T [_]ˢ) (sym (⟨⟩-comp {ζ₁ = ζ} {ζ₂ = wkᴿ ⨟ᴿ ζ′})) ⟩
      T [ ⟨ ζ ⟩ ⨟ˢ ⟨ wkᴿ ⨟ᴿ ζ′ ⟩ ]ˢ
    ≡⟨ cong (λ ξ → T [ ⟨ ζ ⟩ ⨟ˢ ξ ]ˢ) (sym (⟨⟩-comp {ζ₁ = wkᴿ} {ζ₂ = ζ′})) ⟩
      T [ ⟨ ζ ⟩ ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ ⟨ ζ′ ⟩) ]ˢ
    ≡⟨ cong (T [_]ˢ) (sym (associativity {η₁ = ⟨ ζ ⟩} {η₂ = ⟨ wkᴿ ⟩} {η₃ = ⟨ ζ′ ⟩})) ⟩
      T [ (⟨ ζ ⟩ ⨟ˢ ⟨ wkᴿ ⟩) ⨟ˢ ⟨ ζ′ ⟩ ]ˢ
    ≡⟨ sym (compositionalityˢˢ {T = T} {η₁ = ⟨ ζ ⟩ ⨟ˢ ⟨ wkᴿ ⟩} {η₂ = ⟨ ζ′ ⟩}) ⟩
      (T [ ⟨ ζ ⟩ ⨟ˢ ⟨ wkᴿ ⟩ ]ˢ) [ ⟨ ζ′ ⟩ ]ˢ
    ≡⟨ cong (_[ ⟨ ζ′ ⟩ ]ˢ) (sym (compositionalityˢᴿ {T = T} {η₁ = ⟨ ζ ⟩} {ζ₂ = wkᴿ})) ⟩
      ((T [ ⟨ ζ ⟩ ]ˢ) [ wkᴿ ]ᴿ) [ ⟨ ζ′ ⟩ ]ˢ    ∎ }
  ⟨⟩-lift-SR-⨟ {η = η} {ζ = ζ} {η′ = η′} =
    trans (sym (associativity {η₁ = η ↑ˢ} {η₂ = ⟨ ζ ↑ᴿ ⟩} {η₃ = η′}))
          (cong (_⨟ˢ η′) lift-compositionalityˢᴿ)

  compositionalityˢˢ {T = ` α}      = refl
  compositionalityˢˢ {T = ∀α T}     = cong ∀α (trans (compositionalityˢˢ {T = T}) (cong (T [_]ˢ) lift-compositionalityˢˢ))
  compositionalityˢˢ {T = T₁ ⇒ T₂}  = cong₂ _⇒_ (compositionalityˢˢ {T = T₁}) (compositionalityˢˢ {T = T₂})

  identityᵣˢ {T = ` α}      = refl
  identityᵣˢ {T = ∀α T}     = cong ∀α (trans (cong (T [_]ˢ) lift-id) identityᵣˢ)
  identityᵣˢ {T = T₁ ⇒ T₂}  = cong₂ _⇒_ identityᵣˢ identityᵣˢ

{-# REWRITE
  `beta-id `beta-wk `beta-ext-zero `beta-ext-suc
  `beta-lift-zero `beta-lift-suc `beta-comp `beta-lift-fusion
  `associativity `interact `interact-⨟ `comp-idᵣ `comp-idₗ
  `lift-id `lift-wk `lift-fusion `lift-wk-⨟ `lift-fusion-⨟
  identityᵣ compositionalityᴿᴿ

  beta-ext-zero beta-ext-suc beta-rename
  beta-lift-zero beta-lift-suc beta-⟨⟩-⨟ beta-lift-zero-⨟ beta-lift-suc-⨟ beta-fold
  beta-lift-ren-∙ beta-fold-ˢᴿ
  associativity distributivity interact comp-idᵣ comp-idₗ
  lift-id lift-wk lift-cons lift-fusion lift-wk-⨟ lift-fusion-⨟
  ⟨⟩-↑-cons

  lift-coincidence ⟨⟩-comp ⟨⟩-split-⨟
  ⟨⟩-wk-cons ⟨⟩-wk-cons-⨟ ⟨⟩-wk-lift ⟨⟩-wk-lift-⨟ ⟨⟩-lift-lift ⟨⟩-lift-lift-⨟
  ⟨⟩-lift-RS ⟨⟩-lift-RS-⨟ ⟨⟩-lift-SR ⟨⟩-lift-SR-⨟ ⟨⟩-lift-SR-comp
  beta-lift-ren-↑ beta-lift-ren-↑-⨟
  compositionalityᴿˢ compositionalityˢᴿ compositionalityˢˢ
  coincidence
#-}

idˢ : Sub n n
idˢ = ⟨ idᴿ ⟩

-- With the σ-calculus installed, the functor laws for substitution
-- hold definitionally.  The laws marked `*` are σ-calculus laws.
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

-- ══════════════ §4  Expressions ════════════════════════════════════
-- Two abbreviations used by the syntax below: `weaken` is the index of
-- the suc* constructor, `_[_]*` the index of type application.  Both
-- are TRANSPARENT, so the σ-rules see through them and no separate
-- family of interaction laws is needed.
--! Weaken
weaken : Type n → Type (1 + n)
weaken T = T [ wkᴿ ]ᴿ

--! Subzero
_[_]* : Type (1 + n) → Type n → Type n
T [ T′ ]* = T [ T′ ∙ˢ idˢ ]ˢ

--! Ctx
data Ctx : Nat → Set where
  ∅    : Ctx zero
  _▷_  : Ctx n → Type n → Ctx n
  _▷*  : Ctx n → Ctx (1 + n)

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx n

--! Var
data _∋_ : Ctx n → Type n → Set where
  zero  : (Γ ▷ T) ∋ T
  suc   : Γ ∋ T → (Γ ▷ T′) ∋ T
  suc*  : Γ ∋ T → (Γ ▷*) ∋ weaken T

variable
  x x′ x₁ x₂ x₃ : Γ ∋ T

--! <
--! Expr >
--! Definition
data Expr (Γ : Ctx n) : Type n → Set where
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
  e e′ e₁ e₁′ e₂ e₂′ e₃ : Expr Γ T

-- ══════════════ §5  Renaming and substitution on expressions ═══════
-- Every clause below is TRANSPORT-FREE: the type-level rewrite set
-- makes each index equation definitional.  That is transfer heaven.

--! Renaming
_∣_⇒ᴿ_ : Ren n₁ n₂ → Ctx n₁ → Ctx n₂ → Set
ζ ∣ Γ₁ ⇒ᴿ Γ₂ = ∀ T → (x : Γ₁ ∋ T) → Γ₂ ∋ (T [ ζ ]ᴿ)

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

--! Lifting
opaque
  _∣_⇑ᴿ_ : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ ζ ]ᴿ))
  (ζ ∣ ρ ⇑ᴿ _) = ζ ∣ zero ∙ᴿ (ζ , idᴿ ∣ ρ ⨾ᴿ (Wkᴿ _))

  --! TLifting
  -- directly on suc*: the index equation
  --   (weaken T) [ ζ ↑ᴿ ]ᴿ ≡ weaken (T [ ζ ]ᴿ)
  -- is definitional via the ⟨⟩-wk-lift bridge rule
  _∣_↑ᴿ* : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (ζ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
  (ζ ∣ ρ ↑ᴿ*) _ (suc* x) = suc* (ρ _ x)

_⇑ᴿ_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ∀ T → ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ ζ ]ᴿ))
_⇑ᴿ_ = _ ∣_⇑ᴿ_

↑ᴿ*_ : ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (ζ ↑ᴿ) ∣ (Γ₁ ▷*) ⇒ᴿ (Γ₂ ▷*)
↑ᴿ*_ = _ ∣_↑ᴿ*

--! Traversal
-- transparent: clause matching is constructor-driven, so it commutes
-- with index rewriting (registered traversal RULES do not)
_∣_[_]ᴿ : (ζ : Ren n₁ n₂) → Expr Γ₁ T → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → Expr Γ₂ (T [ ζ ]ᴿ)
ζ  ∣ (` x) [ ρ ]ᴿ      = ` (ζ ∣ x &ᴿ ρ)
_  ∣ (λx e) [ ρ ]ᴿ     = λx (_ ∣ e [ ρ ⇑ᴿ _ ]ᴿ)
_  ∣ (Λα e) [ ρ ]ᴿ     = Λα (_ ∣ e [ ↑ᴿ* ρ ]ᴿ)
_  ∣ (e₁ · e₂) [ ρ ]ᴿ  = (_ ∣ e₁ [ ρ ]ᴿ) · (_ ∣ e₂ [ ρ ]ᴿ)
ζ  ∣ (e ·* T′) [ ρ ]ᴿ  = (ζ ∣ e [ ρ ]ᴿ) ·* (T′ [ ζ ]ᴿ)

Weaken : Expr Γ T → Expr (Γ ▷ T′) T
Weaken e = idᴿ ∣ e [ Wkᴿ _ ]ᴿ

weaken* : Expr Γ T → Expr (Γ ▷*) (weaken T)
weaken* e = wkᴿ ∣ e [ wkᴿ* ]ᴿ



--! <
--! Substitution
_∣_⇒ˢ_ : Sub n₁ n₂ → Ctx n₁ → Ctx n₂ → Set
η ∣ Γ₁ ⇒ˢ Γ₂ = ∀ T → (x : Γ₁ ∋ T) → Expr Γ₂ (T [ η ]ˢ)

--! Sub >
variable
  σ σ′ σ₁ σ₂ σ₃ : η ∣ Γ₁ ⇒ˢ Γ₂

opaque
  _∣⟪_⟫ : ∀ ζ → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
  (ζ ∣⟪ ρ ⟫) _ x = ` ρ _ x

  --! Extension
  _∣_∙ˢ_ : ∀ η → (e : Expr Γ₂ (T [ η ]ˢ)) → (σ : η ∣ Γ₁ ⇒ˢ Γ₂) → η ∣ (Γ₁ ▷ T) ⇒ˢ Γ₂
  (_ ∣ e ∙ˢ σ) _ zero     = e
  (_ ∣ e ∙ˢ σ) _ (suc x)  = σ _ x

  --! TExtension
  _∣_∙ˢ*_ : ∀ η T → (σ : η ∣ Γ₁ ⇒ˢ Γ₂) → (T ∙ˢ η) ∣ (Γ₁ ▷*) ⇒ˢ Γ₂
  (_ ∣ T ∙ˢ* σ) _ (suc* x) = σ _ x

  --! Lookup
  _∣_&ˢ_ : ∀ {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} (η : Sub n₁ n₂)
    → (x : Γ₁ ∋ T) → (σ : η ∣ Γ₁ ⇒ˢ Γ₂) → Expr Γ₂ (T [ η ]ˢ)
  η ∣ x &ˢ σ = σ _ x

  --! Lifting
  _∣_⇑ˢ_ : ∀ η → (σ : η ∣ Γ₁ ⇒ˢ Γ₂) → ∀ T → η ∣ (Γ₁ ▷ T) ⇒ˢ (Γ₂ ▷ (T [ η ]ˢ))
  η ∣ σ ⇑ˢ T = η ∣ (` zero) ∙ˢ λ _ x → idᴿ ∣ (σ _ x) [ Wkᴿ (T [ η ]ˢ) ]ᴿ

  --! TLifting
  -- directly on suc*: (weaken T) [ η ↑ˢ ]ˢ ≡ (T [ η ]ˢ) [ wkᴿ ]ᴿ is
  -- definitional via lift-wk and coincidence
  _∣_⇑ˢ* : ∀ η → (σ : η ∣ Γ₁ ⇒ˢ Γ₂) → (η ↑ˢ) ∣ (Γ₁ ▷*) ⇒ˢ (Γ₂ ▷*)
  (η ∣ σ ⇑ˢ*) _ (suc* x) = wkᴿ ∣ (σ _ x) [ wkᴿ* ]ᴿ

⟪_⟫ : (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) → ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
⟪_⟫ = _ ∣⟪_⟫

-- the σ-side constants are TRANSPARENT ⟪⟫-embeddings of the ᴿ-side
-- ones, mirroring the type level where idˢ = ⟨idᴿ⟩ and ⟨wkᴿ⟩ plays the
-- wkˢ-role transparently — Coincidence then erases their traversals
--! Ids
Idˢ : idˢ ∣ Γ ⇒ˢ Γ
Idˢ = idᴿ ∣⟪ Idᴿ ⟫

Wkˢ : ∀ T → ⟨ idᴿ ⟩ ∣ Γ ⇒ˢ (Γ ▷ T)
Wkˢ _ = idᴿ ∣⟪ Wkᴿ _ ⟫

wkˢ* : ⟨ wkᴿ ⟩ ∣ Γ ⇒ˢ (Γ ▷*)
wkˢ* = wkᴿ ∣⟪ wkᴿ* ⟫




--! Traversal
_∣_[_]ˢ : (η : Sub n₁ n₂) → (e : Expr Γ₁ T) → (σ : η ∣ Γ₁ ⇒ˢ Γ₂) → Expr Γ₂ (T [ η ]ˢ)
η  ∣ (` x) [ σ ]ˢ      = η ∣ x &ˢ σ
η  ∣ (λx e) [ σ ]ˢ     = λx (η ∣ e [ η ∣ σ ⇑ˢ _ ]ˢ)
η  ∣ (Λα e) [ σ ]ˢ     = Λα ((η ↑ˢ) ∣ e [ η ∣ σ ⇑ˢ* ]ˢ)
η  ∣ (e · e₁) [ σ ]ˢ   = (η ∣ e [ σ ]ˢ) · (η ∣ e₁ [ σ ]ˢ)
η  ∣ (e ·* T) [ σ ]ˢ   = (η ∣ e [ σ ]ˢ) ·* (T [ η ]ˢ)

-- ══════════════ §6  Compositionality and coincidence ═══════════════
opaque
  --! CompDefinition
  _,_∣_⨾ˢ_ : ∀ η₁ η₂ → (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) → (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) → (η₁ ⨟ˢ η₂) ∣ Γ₁ ⇒ˢ Γ₃
  (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) _ x = η₂ ∣ (σ₁ _ x) [ σ₂ ]ˢ

_⨾ˢ_ : η₁ ∣ Γ₁ ⇒ˢ Γ₂ → η₂ ∣ Γ₂ ⇒ˢ Γ₃ → (η₁ ⨟ˢ η₂) ∣ Γ₁ ⇒ˢ Γ₃
_⨾ˢ_ {η₁ = η₁} {η₂ = η₂} σ₁ σ₂ = (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂)

opaque
  unfolding Idᴿ Wkᴿ wkᴿ* _,_∣_⨾ᴿ_ _∣_∙ᴿ_ _∣_∙ᴿ*_ _∣_&ᴿ_ _∣_⇑ᴿ_ _∣_↑ᴿ* _∣⟪_⟫ _∣_∙ˢ_ _∣_∙ˢ*_ _,_∣_⨾ˢ_ _∣_&ˢ_ _∣_⇑ˢ_ _∣_⇑ˢ*

  --! EtaIdSub
  η-Idˢ : ⟨ idᴿ ⟩ ∣ (` zero) ∙ˢ (Wkˢ T) ≡ Idˢ {Γ = Γ ▷ T}

  η-Idˢ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  η*-Idˢ : ⟨ idᴿ ⟩ ∣ (Idˢ {Γ = Γ}) ⇑ˢ* ≡ Idˢ
  η*-Idˢ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Identityᵣ : ∀ (e : Expr Γ T) → ⟨ idᴿ ⟩ ∣ e [ Idˢ ]ˢ ≡ e
  Identityᵣ (` x)      = refl
  Identityᵣ (λx e)     = cong λx (trans (cong (⟨ idᴿ ⟩ ∣ e [_]ˢ) η-Idˢ) (Identityᵣ e))
  Identityᵣ (Λα e)     = cong Λα (trans (cong (⟨ idᴿ ⟩ ∣ e [_]ˢ) η*-Idˢ) (Identityᵣ e))
  Identityᵣ (e₁ · e₂)  = cong₂ _·_ (Identityᵣ e₁) (Identityᵣ e₂)
  Identityᵣ (e ·* T′)  = cong (_·* T′) (Identityᵣ e)

  Lift-Dist-Compᴿᴿ : (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    ζ₁ , ζ₂ ∣ (ζ₁ ∣ ρ₁ ⇑ᴿ T) ⨾ᴿ (ζ₂ ∣ ρ₂ ⇑ᴿ (T [ ζ₁ ]ᴿ)) ≡ ((ζ₁ ⨟ᴿ ζ₂) ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ⇑ᴿ T)
  Lift-Dist-Compᴿᴿ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  Lift*-Dist-Compᴿᴿ : (ζ₁ : Ren n₁ n₂) (ζ₂ : Ren n₂ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    (ζ₁ ↑ᴿ) , (ζ₂ ↑ᴿ) ∣ (ζ₁ ∣ ρ₁ ↑ᴿ*) ⨾ᴿ (ζ₂ ∣ ρ₂ ↑ᴿ*) ≡ ((ζ₁ ⨟ᴿ ζ₂) ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ↑ᴿ*)
  Lift*-Dist-Compᴿᴿ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Compositionalityᴿᴿ : ∀ (e : Expr Γ₁ T) (ζ₁ : Ren n₁ n₂) (ζ₂ : Ren n₂ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    ζ₂ ∣ (ζ₁ ∣ e [ ρ₁ ]ᴿ) [ ρ₂ ]ᴿ ≡ (ζ₁ ⨟ᴿ ζ₂) ∣ e [ ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂ ]ᴿ
  Compositionalityᴿᴿ (` x)     _  _  _  _   = refl
  Compositionalityᴿᴿ (λx e)    _  _  _  _   = cong λx (trans (Compositionalityᴿᴿ e _ _ _ _) (cong (_ ∣ e [_]ᴿ) (Lift-Dist-Compᴿᴿ _ _)))
  Compositionalityᴿᴿ (Λα e)    _  _  _  _   = cong Λα (trans (Compositionalityᴿᴿ e _ _ _ _) (cong (_ ∣ e [_]ᴿ) (Lift*-Dist-Compᴿᴿ _ _ _ _)))
  Compositionalityᴿᴿ (e₁ · e₂) _  _  _  _   = cong₂ _·_ (Compositionalityᴿᴿ e₁ _ _ _ _) (Compositionalityᴿᴿ e₂ _ _ _ _)
  Compositionalityᴿᴿ (e ·* T′) ζ₁ ζ₂ ρ₁ ρ₂  = cong (_·* (T′ [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ)) (Compositionalityᴿᴿ e _ _ _ _)

  Lift-Dist-Compᴿˢ : (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    ⟨ ζ₁ ⟩ , η₂ ∣ (ζ₁ ∣⟪ ζ₁ ∣ ρ₁ ⇑ᴿ T ⟫) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ (T [ ζ₁ ]ᴿ)) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ (⟨ ζ₁ ⟩ , η₂ ∣ ζ₁ ∣⟪ ρ₁ ⟫ ⨾ˢ σ₂) ⇑ˢ T)
  Lift-Dist-Compᴿˢ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  Lift*-Dist-Compᴿˢ : (ζ₁ : Ren n₁ n₂) (η₂ : Sub n₂ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    ⟨ ζ₁ ↑ᴿ ⟩ , (η₂ ↑ˢ) ∣ ((ζ₁ ↑ᴿ ∣⟪ ζ₁ ∣ ρ₁ ↑ᴿ* ⟫)) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ*) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ (⟨ ζ₁ ⟩ , η₂ ∣ ζ₁ ∣⟪ ρ₁ ⟫ ⨾ˢ σ₂) ⇑ˢ*)
  Lift*-Dist-Compᴿˢ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Compositionalityᴿˢ : ∀ (e : Expr Γ₁ T) (ζ₁ : Ren n₁ n₂) (η₂ : Sub n₂ n₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    η₂ ∣ (ζ₁ ∣ e [ ρ₁ ]ᴿ) [ σ₂ ]ˢ ≡ (⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ e [ ⟨ ζ₁ ⟩ , η₂ ∣ ζ₁ ∣⟪ ρ₁ ⟫ ⨾ˢ σ₂ ]ˢ
  Compositionalityᴿˢ (` x)     _  _  _  _   = refl
  Compositionalityᴿˢ (λx e)    ζ₁ η₂ ρ₁ σ₂  = cong λx (trans (Compositionalityᴿˢ e _ _ _ _) (cong ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ e [_]ˢ) (Lift-Dist-Compᴿˢ ρ₁ σ₂)))
  Compositionalityᴿˢ (Λα e)    ζ₁ η₂ ρ₁ σ₂  = cong Λα (trans (Compositionalityᴿˢ e _ _ _ _) (cong (((⟨ ζ₁ ⟩ ⨟ˢ η₂) ↑ˢ) ∣ e [_]ˢ) (Lift*-Dist-Compᴿˢ _ η₂ ρ₁ σ₂)))
  Compositionalityᴿˢ (e₁ · e₂) _  _  _  _   = cong₂ _·_ (Compositionalityᴿˢ e₁ _ _ _ _) (Compositionalityᴿˢ e₂ _ _ _ _)
  Compositionalityᴿˢ (e ·* T′) ζ₁ η₂ ρ₁ ρ₂  = cong (_·* (T′ [ ⟨ ζ₁ ⟩ ⨟ˢ η₂ ]ˢ)) (Compositionalityᴿˢ e _ _ _ _)

  η-Idᴿ : idᴿ ∣ (zero {Γ = Γ} {T = T}) ∙ᴿ (Wkᴿ T) ≡ (Idᴿ {Γ = Γ ▷ T})
  η-Idᴿ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  -- mirror of `lift-id, λ-dimension (the Λ-dimension is η*-Idᴿ below)
  Lift-Idᴿ : idᴿ ∣ (Idᴿ {Γ = Γ}) ⇑ᴿ T ≡ Idᴿ
  Lift-Idᴿ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  η*-Idᴿ : idᴿ ∣ (Idᴿ {Γ = Γ}) ↑ᴿ* ≡ Idᴿ
  η*-Idᴿ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  -- mirror of identityᵣ (the registered ᴿ-flavour; Identityᵣ above is
  -- the identityᵣˢ-mirror and stays a lemma, exactly as at type level)
  Identityᵣᴿ : ∀ (e : Expr Γ T) → idᴿ ∣ e [ Idᴿ ]ᴿ ≡ e
  Identityᵣᴿ (` x)      = refl
  Identityᵣᴿ (λx e)     = cong λx (trans (cong (idᴿ ∣ e [_]ᴿ) Lift-Idᴿ) (Identityᵣᴿ e))
  Identityᵣᴿ (Λα e)     = cong Λα (trans (cong (idᴿ ∣ e [_]ᴿ) η*-Idᴿ) (Identityᵣᴿ e))
  Identityᵣᴿ (e₁ · e₂)  = cong₂ _·_ (Identityᵣᴿ e₁) (Identityᵣᴿ e₂)
  Identityᵣᴿ (e ·* T′)  = cong (_·* T′) (Identityᵣᴿ e)

  Coincidence : ∀ (e : Expr Γ₁ T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
      ⟨ ζ ⟩ ∣ e [ ζ ∣⟪ ρ ⟫ ]ˢ ≡ (ζ ∣ e [ ρ ]ᴿ)
  Coincidence e ρ = begin
      _  ≡⟨ sym (Compositionalityᴿˢ e _ _ ρ Idˢ) ⟩
      _  ≡⟨ Identityᵣ (_ ∣ e [ ρ ]ᴿ) ⟩
      _  ∎



opaque
  unfolding Idᴿ Wkᴿ wkᴿ* _,_∣_⨾ᴿ_ _∣_∙ᴿ_ _∣_∙ᴿ*_ _∣_&ᴿ_ _∣_⇑ᴿ_ _∣_↑ᴿ* _∣⟪_⟫ _∣_∙ˢ_ _∣_∙ˢ*_ _,_∣_⨾ˢ_ _∣_&ˢ_ _∣_⇑ˢ_ _∣_⇑ˢ*

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

  Lift*-Dist-Compˢᴿ : (η₁ : Sub n₁ n₂) (ζ₂ : Ren n₂ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    (η₁ ↑ˢ) , ⟨ ζ₂ ↑ᴿ ⟩ ∣ (η₁ ∣ σ₁ ⇑ˢ*) ⨾ˢ ((ζ₂ ↑ᴿ) ∣⟪ ζ₂ ∣ ρ₂ ↑ᴿ* ⟫) ≡ (η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ˢ (ζ₂ ∣⟪ ρ₂ ⟫)) ⇑ˢ*
  Lift*-Dist-Compˢᴿ η₁ ζ₂ σ₁ ρ₂ = fun-ext λ _ → fun-ext λ
    { (suc* x) →
      let e = σ₁ _ x in begin
        _  ≡⟨ Coincidence (wkᴿ ∣ e [ wkᴿ* ]ᴿ) (ζ₂ ∣ ρ₂ ↑ᴿ*) ⟩
        _  ≡⟨ Compositionalityᴿᴿ e _ _ wkᴿ* (ζ₂ ∣ ρ₂ ↑ᴿ*) ⟩
        _  ≡⟨ sym (Compositionalityᴿᴿ e _ _ ρ₂ wkᴿ*) ⟩
        _  ≡⟨ cong (wkᴿ ∣_[ wkᴿ* ]ᴿ) (sym (Coincidence e _)) ⟩
        _  ∎ }

  Compositionalityˢᴿ : ∀ (e : Expr Γ₁ T) (η₁ : Sub n₁ n₂) (ζ₂ : Ren n₂ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
    ζ₂ ∣ (η₁ ∣ e [ σ₁ ]ˢ) [ ρ₂ ]ᴿ ≡ (η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ e [ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ˢ (ζ₂ ∣⟪ ρ₂ ⟫)) ]ˢ
  Compositionalityˢᴿ (` x)     _  _  σ₁ _   = sym (Coincidence (σ₁ _ x) _)
  Compositionalityˢᴿ (λx e)    η₁ ζ₂ σ₁ ρ₂  = cong λx (trans (Compositionalityˢᴿ e _ _ _ _) (cong ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ e [_]ˢ) (Lift-Dist-Compˢᴿ σ₁ ρ₂)))
  Compositionalityˢᴿ (Λα e)    η₁ ζ₂ σ₁ ρ₂  = cong Λα (trans (Compositionalityˢᴿ e _ _ _ _) (cong (((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ↑ˢ) ∣ e [_]ˢ) (Lift*-Dist-Compˢᴿ η₁ ζ₂ σ₁ ρ₂)))
  Compositionalityˢᴿ (e₁ · e₂) _  _  _  _   = cong₂ _·_ (Compositionalityˢᴿ e₁ _ _ _ _) (Compositionalityˢᴿ e₂ _ _ _ _)
  Compositionalityˢᴿ (e ·* T′) η₁ ζ₂ σ₁ ρ₂  = cong (_·* (T′ [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ)) (Compositionalityˢᴿ e η₁ ζ₂ σ₁ ρ₂)

  Lift-Dist-Compˢˢ : (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    η₁ , η₂ ∣ (η₁ ∣ σ₁ ⇑ˢ T) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ (T [ η₁ ]ˢ)) ≡ ((η₁ ⨟ˢ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ⇑ˢ T)
  Lift-Dist-Compˢˢ σ₁ σ₂ = fun-ext λ _ → fun-ext λ
    { zero → refl; (suc x) →
      let e = σ₁ _ x in begin
        _  ≡⟨ Compositionalityᴿˢ e _ _ _ _ ⟩
        _  ≡⟨ cong (_ ∣ e [_]ˢ) (fun-ext (λ _ → fun-ext λ x → sym (Coincidence (σ₂ _ x) _))) ⟩
        _  ≡⟨ sym (Compositionalityˢᴿ e _ idᴿ σ₂ (Wkᴿ _)) ⟩
        _  ∎ }

  Lift*-Dist-Compˢˢ : (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
    (η₁ ↑ˢ) , (η₂ ↑ˢ) ∣ (η₁ ∣ σ₁ ⇑ˢ*) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ*) ≡ ((η₁ ⨟ˢ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ⇑ˢ*)
  Lift*-Dist-Compˢˢ _ η₂ σ₁ σ₂ = fun-ext λ _ → fun-ext λ
    { (suc* x) →
      let e = σ₁ _ x in begin
        _  ≡⟨ Compositionalityᴿˢ e _ _ _ _ ⟩
        _  ≡⟨ cong ((η₂ ⨟ˢ ⟨ wkᴿ ⟩) ∣ e [_]ˢ) (fun-ext (λ _ → fun-ext λ { x → sym (Coincidence (σ₂ _ x) wkᴿ*) })) ⟩
        _  ≡⟨ sym (Compositionalityˢᴿ e _ wkᴿ σ₂ wkᴿ*) ⟩
        _  ∎ }

  --! CompositionalityType
  Compositionalityˢˢ : ∀ (e : Expr Γ₁ T) (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃)
    → (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃)
    → η₂ ∣ (η₁ ∣ e [ σ₁ ]ˢ) [ σ₂ ]ˢ ≡ (η₁ ⨟ˢ η₂) ∣ e [ η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂ ]ˢ

  --! CompositionalityBody
  Compositionalityˢˢ (` x)      η₁ η₂ σ₁ σ₂  = refl
  Compositionalityˢˢ (λx {T₁ = T₁} e)     η₁ η₂ σ₁ σ₂  = cong λx (begin
        η₂ ∣ (η₁ ∣ e [ η₁ ∣ σ₁ ⇑ˢ T₁ ]ˢ) [ η₂ ∣ σ₂ ⇑ˢ (T₁ [ η₁ ]ˢ) ]ˢ
      ≡⟨ Compositionalityˢˢ e η₁ η₂ (η₁ ∣ σ₁ ⇑ˢ T₁) (η₂ ∣ σ₂ ⇑ˢ (T₁ [ η₁ ]ˢ)) ⟩ -- IH
        (η₁ ⨟ˢ η₂) ∣ e [  η₁ , η₂ ∣ (η₁ ∣ σ₁ ⇑ˢ T₁) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ (T₁ [ η₁ ]ˢ)) ]ˢ
      ≡⟨ cong ((η₁ ⨟ˢ η₂) ∣ e [_]ˢ) (Lift-Dist-Compˢˢ σ₁ σ₂) ⟩
        (η₁ ⨟ˢ η₂) ∣ e [ (η₁ ⨟ˢ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ⇑ˢ T₁ ]ˢ
      ∎)
  Compositionalityˢˢ (Λα e)     η₁ η₂ σ₁ σ₂  = cong Λα (begin
        (η₂ ↑ˢ) ∣ ((η₁ ↑ˢ) ∣ e [ η₁ ∣ σ₁ ⇑ˢ* ]ˢ) [ η₂ ∣ σ₂ ⇑ˢ* ]ˢ
      ≡⟨ Compositionalityˢˢ e (η₁ ↑ˢ) (η₂ ↑ˢ) (η₁ ∣ σ₁ ⇑ˢ*) (η₂ ∣ σ₂ ⇑ˢ*) ⟩ -- IH
        ((η₁ ⨟ˢ η₂) ↑ˢ) ∣ e [ (η₁ ↑ˢ) , η₂ ↑ˢ ∣ (η₁ ∣ σ₁ ⇑ˢ*) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ*) ]ˢ
      ≡⟨ cong (((η₁ ⨟ˢ η₂) ↑ˢ) ∣ e [_]ˢ) (Lift*-Dist-Compˢˢ η₁ η₂ σ₁ σ₂) ⟩
        ((η₁ ⨟ˢ η₂) ↑ˢ) ∣ e [ (η₁ ⨟ˢ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ⇑ˢ* ]ˢ
      ∎)
  Compositionalityˢˢ (e₁ · e₂)  η₁ η₂ σ₁ σ₂  = cong₂ _·_
      (Compositionalityˢˢ e₁ η₁ η₂ σ₁ σ₂) -- IH
      (Compositionalityˢˢ e₂ η₁ η₂ σ₁ σ₂) -- IH
  Compositionalityˢˢ (e ·* T′)  η₁ η₂ σ₁ σ₂  = cong (_·* (T′ [ η₁ ⨟ˢ η₂ ]ˢ))
    (Compositionalityˢˢ e η₁ η₂ σ₁ σ₂) -- IH



-- ══════════════ §7  The expression-level equational theory ═════════
-- Every law below mirrors a type-level law of §3 exactly, under the
-- dictionary  Ren ↦ ⇒ᴿ,  Sub ↦ ⇒ˢ,  ⟨⟩ ↦ ⟪⟫,  ↑ ↦ ⇑ (λ-dimension) and
-- ⇑* (Λ-dimension), and each is an Agda THEOREM.  As an equational
-- theory the mirror is therefore exact.  As a REWRITE system it is
-- not, for two independent reasons:
--
--   MATCHING.  A rule whose stored index is  T [ η₁ ]ˢ  fires only
--   when T is a variable, because _[_]ˢ computes on every type
--   constructor.  The index would have to be INERT to be matched and
--   COMPUTING to be usable, and it is the same symbol.
--
--   CONFLUENCE.  Registering the mirror leaves critical pairs that do
--   not join, and they are overwhelmingly pairs of an expression-level
--   rule against a TYPE-level rule rather than against each other.
--
-- So none of these laws is registered.  Each is applied EXPLICITLY, by
-- subst or cong, at its use sites.  That is transfer hell, stated
-- rather than papered over.
opaque
  unfolding Idᴿ Wkᴿ wkᴿ* _,_∣_⨾ᴿ_ _∣_∙ᴿ_ _∣_∙ᴿ*_ _∣_&ᴿ_ _∣_⇑ᴿ_ _∣_↑ᴿ* _∣⟪_⟫ _∣_∙ˢ_ _∣_∙ˢ*_ _,_∣_⨾ˢ_ _∣_&ˢ_ _∣_⇑ˢ_ _∣_⇑ˢ*

  --! ExprRenamingTraversal {
  Traversal-Varᴿ : ∀ {ζ : Ren n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (x : Γ₁ ∋ T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                   ζ ∣ (` x) [ ρ ]ᴿ ≡ ` (ζ ∣ x &ᴿ ρ)
  Traversal-Varᴿ _ _ = refl

  Traversal-λxᴿ : ∀ {ζ : Ren n₁ n₂} {T₁ T₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr (Γ₁ ▷ T₁) T₂) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                  ζ ∣ (λx e) [ ρ ]ᴿ ≡ λx (ζ ∣ e [ ρ ⇑ᴿ T₁ ]ᴿ)
  Traversal-λxᴿ _ _ = refl

  Traversal-Λαᴿ : ∀ {ζ : Ren n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr (Γ₁ ▷*) T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                  ζ ∣ (Λα e) [ ρ ]ᴿ ≡ Λα ((ζ ↑ᴿ) ∣ e [ ↑ᴿ* ρ ]ᴿ)
  Traversal-Λαᴿ _ _ = refl

  Traversal-·ᴿ : ∀ {ζ : Ren n₁ n₂} {T₁ T₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                 (e₁ : Expr Γ₁ (T₁ ⇒ T₂)) (e₂ : Expr Γ₁ T₁) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                 ζ ∣ (e₁ · e₂) [ ρ ]ᴿ ≡ (ζ ∣ e₁ [ ρ ]ᴿ) · (ζ ∣ e₂ [ ρ ]ᴿ)
  Traversal-·ᴿ _ _ _ = refl

  Traversal-·*ᴿ : ∀ {ζ : Ren n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr Γ₁ (∀α T)) (T′ : Type n₁) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                  ζ ∣ (e ·* T′) [ ρ ]ᴿ ≡ (ζ ∣ e [ ρ ]ᴿ) ·* (T′ [ ζ ]ᴿ)
  Traversal-·*ᴿ _ _ _ = refl
  --! }

  --! ExprSubstitutionTraversal {
  Traversal-Varˢ : ∀ {η : Sub n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (x : Γ₁ ∋ T) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                   η ∣ (` x) [ σ ]ˢ ≡ η ∣ x &ˢ σ
  Traversal-Varˢ _ _ = refl

  Traversal-λxˢ : ∀ {η : Sub n₁ n₂} {T₁ T₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr (Γ₁ ▷ T₁) T₂) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                  η ∣ (λx e) [ σ ]ˢ ≡ λx (η ∣ e [ η ∣ σ ⇑ˢ T₁ ]ˢ)
  Traversal-λxˢ _ _ = refl

  Traversal-Λαˢ : ∀ {η : Sub n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr (Γ₁ ▷*) T) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                  η ∣ (Λα e) [ σ ]ˢ ≡ Λα ((η ↑ˢ) ∣ e [ η ∣ σ ⇑ˢ* ]ˢ)
  Traversal-Λαˢ _ _ = refl

  Traversal-·ˢ : ∀ {η : Sub n₁ n₂} {T₁ T₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                 (e₁ : Expr Γ₁ (T₁ ⇒ T₂)) (e₂ : Expr Γ₁ T₁) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                 η ∣ (e₁ · e₂) [ σ ]ˢ ≡ (η ∣ e₁ [ σ ]ˢ) · (η ∣ e₂ [ σ ]ˢ)
  Traversal-·ˢ _ _ _ = refl

  Traversal-·*ˢ : ∀ {η : Sub n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (e : Expr Γ₁ (∀α T)) (T′ : Type n₁) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                  η ∣ (e ·* T′) [ σ ]ˢ ≡ (η ∣ e [ σ ]ˢ) ·* (T′ [ η ]ˢ)
  Traversal-·*ˢ _ _ _ = refl
  --! }

  -- weaken* computes on variables, the Λ-dimension analogue of the
  -- ᴿ-traversal's `-clause at wkᴿ*
  Weaken*-var : ∀ {n} {T} {Γ : Ctx n} (x : Γ ∋ T) →
                weaken* (` x) ≡ ` (suc* x)
  Weaken*-var _ = refl

  --! ExprRenamingBeta {
  Beta-idᴿ : ∀ {T} {Γ : Ctx n} (x : Γ ∋ T) → idᴿ ∣ x &ᴿ Idᴿ ≡ x
  Beta-idᴿ _ = refl

  Beta-wkᴿ : ∀ {T T'} {Γ : Ctx n} (x : Γ ∋ T) → idᴿ ∣ x &ᴿ Wkᴿ T' ≡ suc x
  Beta-wkᴿ _ = refl

  Beta-wk*ᴿ : ∀ {T} {Γ : Ctx n} (x : Γ ∋ T) → wkᴿ ∣ x &ᴿ wkᴿ* ≡ suc* x
  Beta-wk*ᴿ _ = refl

  Beta-ext-zeroᴿ : ∀ {ζ : Ren n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (x : Γ₂ ∋ (T [ ζ ]ᴿ)) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                   ζ ∣ zero &ᴿ (_∣_∙ᴿ_ {T = T} ζ x ρ) ≡ x
  Beta-ext-zeroᴿ _ _ = refl

  Beta-ext-sucᴿ : ∀ {ζ : Ren n₁ n₂} {T T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (x' : Γ₁ ∋ T'') (x : Γ₂ ∋ (T [ ζ ]ᴿ)) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                  ζ ∣ (suc x') &ᴿ (_∣_∙ᴿ_ {T = T} ζ x ρ) ≡ ζ ∣ x' &ᴿ ρ
  Beta-ext-sucᴿ _ _ _ = refl

  Beta-ext-suc*ᴿ : ∀ {ζ : Ren n₁ n₂} {T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (α : Var n₂) (x : Γ₁ ∋ T'') (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                   (α ∙ᴿ ζ) ∣ (suc* x) &ᴿ (ζ ∣ α ∙ᴿ* ρ) ≡ ζ ∣ x &ᴿ ρ
  Beta-ext-suc*ᴿ _ _ _ = refl

  -- composition at a variable FOLDS — the opposite of the type-level
  -- `beta-comp!  The push orientation's LHS is inherently NON-linear
  -- here: the composite ζ₁⨟ᴿζ₂ must be spelled both as the traversal
  -- index and inside the ⨾ᴿ-term, so a type-level rule rewriting the
  -- index occurrence alone (e.g. `lift-fusion-⨟) leaves a stuck term
  -- push can never refire on.  The fold LHS mentions every index
  -- exactly once (bare metas) and stays confluent.
  Beta-compᴿ : ∀ {ζ₁ : Ren n₁ n₂} {ζ₂ : Ren n₂ n₃} {T}
               {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
               (x : Γ₁ ∋ T) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
               ζ₂ ∣ (ζ₁ ∣ x &ᴿ ρ₁) &ᴿ ρ₂ ≡ (ζ₁ ⨟ᴿ ζ₂) ∣ x &ᴿ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂)
  Beta-compᴿ _ _ _ = refl
  --! }

  --! ExprSubstitutionBeta {
  Beta-ext-zeroˢ : ∀ {η : Sub n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (e : Expr Γ₂ (T [ η ]ˢ)) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                   η ∣ zero &ˢ (_∣_∙ˢ_ {T = T} η e σ) ≡ e
  Beta-ext-zeroˢ _ _ = refl

  Beta-ext-sucˢ : ∀ {η : Sub n₁ n₂} {T T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (x' : Γ₁ ∋ T'') (e : Expr Γ₂ (T [ η ]ˢ)) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                  η ∣ (suc x') &ˢ (_∣_∙ˢ_ {T = T} η e σ) ≡ η ∣ x' &ˢ σ
  Beta-ext-sucˢ _ _ _ = refl

  Beta-ext-suc*ˢ : ∀ {η : Sub n₁ n₂} {T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                   (T' : Type n₂) (x : Γ₁ ∋ T'') (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                   (T' ∙ˢ η) ∣ (suc* x) &ˢ (η ∣ T' ∙ˢ* σ) ≡ η ∣ x &ˢ σ
  Beta-ext-suc*ˢ _ _ _ = refl

  Beta-renameˢ : ∀ {ζ : Ren n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                 (x : Γ₁ ∋ T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                 ⟨ ζ ⟩ ∣ x &ˢ (ζ ∣⟪ ρ ⟫) ≡ ` (ζ ∣ x &ᴿ ρ)
  Beta-renameˢ _ _ = refl

  Beta-compˢ : ∀ {η₁ : Sub n₁ n₂} {η₂ : Sub n₂ n₃} {T}
               {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
               (x : Γ₁ ∋ T) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
               η₂ ∣ (η₁ ∣ x &ˢ σ₁) [ σ₂ ]ˢ ≡ (η₁ ⨟ˢ η₂) ∣ x &ˢ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂)
  Beta-compˢ _ _ _ = refl

  -- ⇑-applied rules: lifting is first-class (the ⇑-elimination rules
  -- below are η-shaped lemmas), so applications compute via these
  Beta-⇑ᴿ-zero : ∀ {ζ : Ren n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T : Type n₁}
                 (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                 ζ ∣ zero &ᴿ (ζ ∣ ρ ⇑ᴿ T) ≡ zero
  Beta-⇑ᴿ-zero _ = refl

  Beta-⇑ᴿ-suc : ∀ {ζ : Ren n₁ n₂} {T T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                (x : Γ₁ ∋ T'') (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                ζ ∣ (suc {T′ = T} x) &ᴿ (ζ ∣ ρ ⇑ᴿ T) ≡ suc (ζ ∣ x &ᴿ ρ)
  Beta-⇑ᴿ-suc _ _ = refl

  Beta-↑ᴿ*-suc* : ∀ {ζ : Ren n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (x : Γ₁ ∋ T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
                  (ζ ↑ᴿ) ∣ (suc* x) &ᴿ (ζ ∣ ρ ↑ᴿ*) ≡ suc* (ζ ∣ x &ᴿ ρ)
  Beta-↑ᴿ*-suc* _ _ = refl

  Beta-⇑ˢ-zero : ∀ {η : Sub n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T : Type n₁}
                 (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                 η ∣ zero &ˢ (η ∣ σ ⇑ˢ T) ≡ ` zero
  Beta-⇑ˢ-zero _ = refl

  Beta-⇑ˢ-suc : ∀ {η : Sub n₁ n₂} {T T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                (x : Γ₁ ∋ T'') (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                η ∣ (suc {T′ = T} x) &ˢ (η ∣ σ ⇑ˢ T) ≡ idᴿ ∣ (η ∣ x &ˢ σ) [ Wkᴿ (T [ η ]ˢ) ]ᴿ
  Beta-⇑ˢ-suc _ _ = refl

  -- mirror of beta-lift-suc, Λ-dim: the RHS is spelled with the
  -- first-class expression weaken* (opaque — the raw spelling
  -- wkᴿ∣_[wkᴿ*]ᴿ and the index (weaken T)[η↑ˢ]ˢ normalize apart)
  Beta-⇑ˢ*-suc* : ∀ {η : Sub n₁ n₂} {T''} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                  (x : Γ₁ ∋ T'') (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                  (η ↑ˢ) ∣ (suc* x) &ˢ (η ∣ σ ⇑ˢ*) ≡ weaken* (η ∣ x &ˢ σ)
  Beta-⇑ˢ*-suc* _ _ = refl

  -- weakening by a type binder is undone by any Λ-dimension
  -- extension: the mirror of the type-level `interact`.
  Weaken*-cons : ∀ {η : Sub n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                 (e : Expr Γ₁ T) (A : Type n₂) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
                 (A ∙ˢ η) ∣ (weaken* e) [ η ∣ A ∙ˢ* σ ]ˢ ≡ η ∣ e [ σ ]ˢ
  Weaken*-cons e A σ = Compositionalityᴿˢ e wkᴿ _ wkᴿ* (_ ∣ A ∙ˢ* σ)
  --! }

  -- closure rules for the suc*-rules above: the type-level rules
  -- `lift-id and lift-coincidence rewrite the ↑-node spelled in the
  -- rules' index argument, so the instantiated forms need their own
  -- (index-inert) rules — a finite family, since idᴿ/⟨⟩ are inert
  Beta-↑ᴿ*-suc*-id : ∀ {T} {Γ₁ Γ₂ : Ctx n} (x : Γ₁ ∋ T) (ρ : idᴿ ∣ Γ₁ ⇒ᴿ Γ₂) →
                     idᴿ ∣ (suc* x) &ᴿ (idᴿ ∣ ρ ↑ᴿ*) ≡ suc* (idᴿ ∣ x &ᴿ ρ)
  Beta-↑ᴿ*-suc*-id _ _ = refl

  Beta-⇑ˢ*-suc*-id : ∀ {T} {Γ₁ Γ₂ : Ctx n} (x : Γ₁ ∋ T) (σ : ⟨ idᴿ ⟩ ∣ Γ₁ ⇒ˢ Γ₂) →
                     ⟨ idᴿ ⟩ ∣ (suc* x) &ˢ (⟨ idᴿ ⟩ ∣ σ ⇑ˢ*) ≡ weaken* (⟨ idᴿ ⟩ ∣ x &ˢ σ)
  Beta-⇑ˢ*-suc*-id _ _ = refl

  Beta-⇑ˢ*-suc*-⟨⟩ : ∀ {ζ : Ren n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
                     (x : Γ₁ ∋ T) (σ : ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂) →
                     ⟨ ζ ↑ᴿ ⟩ ∣ (suc* x) &ˢ (⟨ ζ ⟩ ∣ σ ⇑ˢ*) ≡ weaken* (⟨ ζ ⟩ ∣ x &ˢ σ)
  Beta-⇑ˢ*-suc*-⟨⟩ _ _ = refl

  --! ExprRenLaws {
  Associativityᴿ : ∀ {n₁ n₂ n₃ n₄}
                   (ζ₁ : Ren n₁ n₂) (ζ₂ : Ren n₂ n₃) (ζ₃ : Ren n₃ n₄)
                   {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃} {Γ₄ : Ctx n₄}
                   (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) (ρ₃ : ζ₃ ∣ Γ₃ ⇒ᴿ Γ₄) →
                   ((ζ₁ ⨟ᴿ ζ₂) , ζ₃ ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ⨾ᴿ ρ₃) ≡
                   (ζ₁ , (ζ₂ ⨟ᴿ ζ₃) ∣ ρ₁ ⨾ᴿ (ζ₂ , ζ₃ ∣ ρ₂ ⨾ᴿ ρ₃))
  Associativityᴿ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Distributivityᴿ : ∀ {n₁ n₂ n₃} (ζ : Ren n₁ n₂) (ζ′ : Ren n₂ n₃)
                    {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
                    (T : Type n₁) (x : Γ₂ ∋ (T [ ζ ]ᴿ))
                    (ρ₁ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ′ ∣ Γ₂ ⇒ᴿ Γ₃) →
                    (ζ , ζ′ ∣ (_∣_∙ᴿ_ {T = T} ζ x ρ₁) ⨾ᴿ ρ₂) ≡
                    (_∣_∙ᴿ_ {T = T} (ζ ⨟ᴿ ζ′) (ρ₂ (T [ ζ ]ᴿ) x) (ζ , ζ′ ∣ ρ₁ ⨾ᴿ ρ₂))
  Distributivityᴿ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  Interactᴿ : ∀ {n₁ n₂} (ζ : Ren n₁ n₂) {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
              {x : Γ₂ ∋ (T [ ζ ]ᴿ)} (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
              (idᴿ , ζ ∣ (Wkᴿ T) ⨾ᴿ (ζ ∣ x ∙ᴿ ρ)) ≡ ρ
  Interactᴿ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Interact*ᴿ : ∀ {n₁ n₂} (ζ : Ren n₁ n₂) {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
               {α : Var n₂} (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
               (wkᴿ , (α ∙ᴿ ζ) ∣ wkᴿ* ⨾ᴿ (ζ ∣ α ∙ᴿ* ρ)) ≡ ρ
  Interact*ᴿ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Comp-idᵣᴿ : ∀ {ζ : Ren n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
              (ζ , idᴿ ∣ ρ ⨾ᴿ Idᴿ) ≡ ρ
  Comp-idᵣᴿ _ = fun-ext λ _ → fun-ext λ _ → refl

  Comp-idₗᴿ : ∀ {ζ : Ren n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
              (idᴿ , ζ ∣ Idᴿ ⨾ᴿ ρ) ≡ ρ
  Comp-idₗᴿ _ = fun-ext λ _ → fun-ext λ _ → refl

  η-lawᴿ : ∀ {n₁ n₂} {ζ : Ren n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
           (ρ : ζ ∣ (Γ₁ ▷ T) ⇒ᴿ Γ₂) →
           (ζ ∣ ρ T zero ∙ᴿ (idᴿ , ζ ∣ (Wkᴿ T) ⨾ᴿ ρ)) ≡ ρ
  η-lawᴿ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  --! }

  Associativityˢ : ∀ {n₁ n₂ n₃ n₄}
                   (η₁ : Sub n₁ n₂) (η₂ : Sub n₂ n₃) (η₃ : Sub n₃ n₄)
                   {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃} {Γ₄ : Ctx n₄}
                   (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) (σ₃ : η₃ ∣ Γ₃ ⇒ˢ Γ₄) →
                   ((η₁ ⨟ˢ η₂) , η₃ ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ⨾ˢ σ₃) ≡
                   (η₁ , (η₂ ⨟ˢ η₃) ∣ σ₁ ⨾ˢ (η₂ , η₃ ∣ σ₂ ⨾ˢ σ₃))
  Associativityˢ _ _ _ σ₁ σ₂ σ₃ =
    fun-ext λ _ → fun-ext λ x → Compositionalityˢˢ (σ₁ _ x) _ _ σ₂ σ₃

  Distributivityˢ : ∀ {n₁ n₂ n₃} (η : Sub n₁ n₂) (η′ : Sub n₂ n₃)
                    {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
                    (T : Type n₁) (e : Expr Γ₂ (T [ η ]ˢ))
                    (σ₁ : η ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η′ ∣ Γ₂ ⇒ˢ Γ₃) →
                    (η , η′ ∣ (_∣_∙ˢ_ {T = T} η e σ₁) ⨾ˢ σ₂) ≡
                    (_∣_∙ˢ_ {T = T} (η ⨟ˢ η′) (η′ ∣ e [ σ₂ ]ˢ) (η , η′ ∣ σ₁ ⨾ˢ σ₂))
  Distributivityˢ _ _ _ _ _ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  Distributivity*ˢ : ∀ {n₁ n₂ n₃} (η : Sub n₁ n₂) (η′ : Sub n₂ n₃)
                     {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {Γ₃ : Ctx n₃}
                     (T : Type n₂) (σ₁ : η ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η′ ∣ Γ₂ ⇒ˢ Γ₃) →
                     ((T ∙ˢ η) , η′ ∣ (η ∣ T ∙ˢ* σ₁) ⨾ˢ σ₂) ≡
                     ((η ⨟ˢ η′) ∣ (T [ η′ ]ˢ) ∙ˢ* (η , η′ ∣ σ₁ ⨾ˢ σ₂))
  Distributivity*ˢ _ _ _ _ _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }

  Interactˢ : ∀ {n₁ n₂} (η : Sub n₁ n₂) {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
              {e : Expr Γ₂ (T [ η ]ˢ)} (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
              (⟨ idᴿ ⟩ , η ∣ (Wkˢ T) ⨾ˢ (η ∣ e ∙ˢ σ)) ≡ σ
  Interactˢ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Interact*ˢ : ∀ {n₁ n₂} (η : Sub n₁ n₂) {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
               {T : Type n₂} (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
               (⟨ wkᴿ ⟩ , (T ∙ˢ η) ∣ wkˢ* ⨾ˢ (η ∣ T ∙ˢ* σ)) ≡ σ
  Interact*ˢ _ _ = fun-ext λ _ → fun-ext λ _ → refl

  Comp-idᵣˢ : ∀ {η : Sub n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
              (η , ⟨ idᴿ ⟩ ∣ σ ⨾ˢ Idˢ) ≡ σ
  Comp-idᵣˢ σ = fun-ext λ _ → fun-ext λ x → Identityᵣ (σ _ x)

  Comp-idₗˢ : ∀ {η : Sub n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
              (⟨ idᴿ ⟩ , η ∣ Idˢ ⨾ˢ σ) ≡ σ
  Comp-idₗˢ _ = fun-ext λ _ → fun-ext λ _ → refl

  η-lawˢ : ∀ {n₁ n₂} {η : Sub n₁ n₂} {T} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
           (σ : η ∣ (Γ₁ ▷ T) ⇒ˢ Γ₂) →
           (η ∣ σ T zero ∙ˢ (⟨ idᴿ ⟩ , η ∣ (Wkˢ T) ⨾ˢ σ)) ≡ σ
  η-lawˢ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }


  --! ExprLiftBeta {
  Beta-liftᴿ : ∀ {ζ : Ren n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T : Type n₁}
               (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
               (ζ ∣ ρ ⇑ᴿ T) ≡ (ζ ∣ zero ∙ᴿ (ζ , idᴿ ∣ ρ ⨾ᴿ Wkᴿ (T [ ζ ]ᴿ)))
  Beta-liftᴿ _ = refl

  Beta-liftˢ : ∀ {η : Sub n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T : Type n₁}
               (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
               (η ∣ σ ⇑ˢ T) ≡ (η ∣ (` zero) ∙ˢ (η , ⟨ idᴿ ⟩ ∣ σ ⨾ˢ Wkˢ (T [ η ]ˢ)))
  Beta-liftˢ σ = fun-ext λ _ → fun-ext λ
    { zero → refl
    ; (suc x) → sym (Coincidence (σ _ x) (Wkᴿ _))
    }
  --! }

  -- the expression-level mirror of lift-coincidence: lifting an
  -- embedded renaming collapses back into an embedding
  ⟪⟫-⇑ : ∀ {ζ : Ren n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂} {T : Type n₁}
         (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
         (⟨ ζ ⟩ ∣ (ζ ∣⟪ ρ ⟫) ⇑ˢ T) ≡ (ζ ∣⟪ ζ ∣ ρ ⇑ᴿ T ⟫)
  ⟪⟫-⇑ _ = fun-ext λ _ → fun-ext λ { zero → refl; (suc x) → refl }

  ⟪⟫-⇑* : ∀ {ζ : Ren n₁ n₂} {Γ₁ : Ctx n₁} {Γ₂ : Ctx n₂}
          (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
          (⟨ ζ ⟩ ∣ (ζ ∣⟪ ρ ⟫) ⇑ˢ*) ≡ ((ζ ↑ᴿ) ∣⟪ ζ ∣ ρ ↑ᴿ* ⟫)
  ⟪⟫-⇑* _ = fun-ext λ _ → fun-ext λ { (suc* x) → refl }



-- ══════════════ §8  Semantics: full β-reduction and progress ═══════
--! <
--! Sem >
--! SingleSub
_[_] : Expr (Γ ▷ T′) T → Expr Γ T′ → Expr Γ T
e [ e′ ] = idˢ ∣ e [ idˢ ∣ e′ ∙ˢ Idˢ ]ˢ

--! SingleTypeSub
_[*_*] : Expr (Γ ▷*) T → (T′ : Type n) → Expr Γ (T [ T′ ]*)
e [* T′ *] = (T′ ∙ˢ idˢ) ∣ e [ idˢ ∣ T′ ∙ˢ* Idˢ ]ˢ

--! Definition
-- FULL β-reduction: a congruence rule for EVERY subterm position,
-- including under λ and under Λ and in argument position.  Anything
-- weaker cannot reach the canonical forms of System F, which live
-- under three binders (Λα λx λy. x).
data _⟶_ : Expr Γ T → Expr Γ T → Set where
  β-λ   :                (λx e₁ · e₂)  ⟶ (e₁ [ e₂ ])
  β-Λ   :                (Λα e ·* T′)  ⟶ (e [* T′ *])
  ξ-·₁  : e₁ ⟶ e₁′  →  (e₁ · e₂)     ⟶ (e₁′ · e₂)
  ξ-·₂  : e₂ ⟶ e₂′  →  (e₁ · e₂)     ⟶ (e₁ · e₂′)
  ξ-λ   : e ⟶ e′    →  (λx {T₁ = T₁} e) ⟶ (λx e′)
  ξ-·*  : e ⟶ e′    →  (e ·* T)      ⟶ (e′ ·* T)
  ξ-Λ   : e ⟶ e′    →  (Λα e)        ⟶ (Λα e′)

data _⟶*_ : Expr Γ T → Expr Γ T → Set where
  ⟶refl  : e ⟶* e
  ⟶step  : e₁ ⟶ e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

-- β-normal forms: under full reduction the right notion of "done" is a
-- normal form, not a value.
--! ProgressDefs {
data Neutral : Expr Γ T → Set
data Normal  : Expr Γ T → Set
data Neutral where
  `_    : (x : Γ ∋ T)                 → Neutral (` x)
  _·_   : Neutral e₁ → Normal e₂      → Neutral (e₁ · e₂)
  _·*_  : Neutral e → (T′ : Type n)   → Neutral (e ·* T′)
data Normal where
  ne    : Neutral e                   → Normal e
  λx    : Normal e                    → Normal (λx {T₁ = T₁} e)
  Λα    : Normal e                    → Normal (Λα e)
data Progress : Expr Γ T → Set where
  done  : (nf : Normal e)     → Progress e
  step  : (e⟶e′ : e ⟶ e′)  → Progress e
--! }


--! NewNoVarDefs
NoVar : Ctx n → Set
NoVar Γ = ∀ {T′} → ¬ (Γ ∋ T′)

--! NewProgress
-- Under full reduction progress needs NO hypothesis on the context:
-- every term either is normal or steps.  (NoVar re-enters only at the
-- very end, to rule out the neutral normal forms.)
progress : (e : Expr Γ T) → Progress e
progress (` x)    = done (ne (` x))
progress (λx e)
  with progress e
... | done nf      = done (λx nf)
... | step e⟶e′  = step (ξ-λ e⟶e′)
progress (Λα e)
  with progress e
... | done nf      = done (Λα nf)
... | step e⟶e′  = step (ξ-Λ e⟶e′)
progress (e₁ · e₂)
  with progress e₁
... | step e⟶e′  = step (ξ-·₁ e⟶e′)
... | done (λx _)  = step β-λ
... | done (ne n₁)
  with progress e₂
... | step e⟶e′  = step (ξ-·₂ e⟶e′)
... | done nf₂     = done (ne (n₁ · nf₂))
progress (e ·* T′)
  with progress e
... | step e⟶e′  = step (ξ-·* e⟶e′)
... | done (Λα _)  = step β-Λ
... | done (ne n)  = done (ne (n ·* T′))

-- in a context with no term variables there are no neutral terms
NoVar⇒¬Neutral : NoVar Γ → {e : Expr Γ T} → ¬ Neutral e
NoVar⇒¬Neutral nv (` x)     = nv x
NoVar⇒¬Neutral nv (n · _)   = NoVar⇒¬Neutral nv n
NoVar⇒¬Neutral nv (n ·* _)  = NoVar⇒¬Neutral nv n

-- ══════════════ §9  Church numerals, the running examples ══════════
--! <
--! <
--! <
--! FCNType
ℕᶜ : Type 0
ℕᶜ = ∀α ((` zero ⇒ ` zero) ⇒ (` zero ⇒ ` zero))
--! FCNZero
zeroᶜ : Expr ∅ ℕᶜ
zeroᶜ = Λα (λx (λx (` zero)))
--! FCNOne
oneᶜ : Expr ∅ ℕᶜ
oneᶜ = Λα (λx (λx ((` suc zero) · (` zero))))
--! FCNSucc
succᶜ : Expr ∅ (ℕᶜ ⇒ ℕᶜ)
succᶜ = λx (Λα (λx (λx ((` suc zero) ·
          ((((` suc (suc (suc* zero))) ·* (` zero)) · (` suc zero)) · (` zero))))))
--! FCNTwo
twoᶜ : Expr ∅ ℕᶜ
twoᶜ = succᶜ · (succᶜ · zeroᶜ)
