{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════
-- FINITELY STRATIFIED SYSTEM F, intrinsically typed.
--
-- Proves CANONICITY: every closed term of base type reduces to a
-- constructor, via a Girard-style logical relation.
--
-- Three features shape the development:
--
--  (1) ONLY TYPE-LEVEL REWRITES.  The type-level σ-laws of SystemF.agda
--      §3 are registered and certified by --local-confluence-check; the
--      expression-level laws of §9 are ordinary theorems.
--
--  (2) NO --type-in-type.  The object language is finitely stratified
--      (Leivant; cf. Thiemann & Weidner, "Towards Tagless Interpretation
--      of Stratified System F", TyDe'23, and Saffrich, Thiemann &
--      Weidner, TyDe'24): every type carries a universe level, ∀ at
--      level l binds a variable of level l and lands STRICTLY above it.
--      Object levels are interpreted as Agda universe levels, so the
--      logical relation is predicative.
--
--  (3) FULL β-reduction — a congruence in every position, including
--      under λ and Λ — which is what canonicity for System F actually
--      requires: the canonical booleans live under three binders.
--
-- The only postulate is fun-ext.
-- ════════════════════════════════════════════════════════════════════
module SystemF-strat where

--! ST >

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst; subst₂; module ≡-Reasoning)
open ≡-Reasoning
open import Axiom.Extensionality.Propositional using (Extensionality)

postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

-- maps take their level EXPLICITLY, so plain fun-ext applies twice
ext² : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : ∀ a → B a → Set ℓ₃}
       {f g : ∀ a (b : B a) → C a b} → (∀ a b → f a b ≡ g a b) → f ≡ g
ext² h = fun-ext λ a → fun-ext λ b → h a b

infixr 5 _⇒_
infix  6 `_

-- ══════════════ §1  Level contexts and stratified types ════════════

data LCtx : Set where
  ∅   : LCtx
  _∙_ : Level → LCtx → LCtx

variable
  l l′ l₁ l₂ l₃ : Level
  Δ Δ₁ Δ₂ Δ₃ Δ₄ : LCtx

data _∋ˡ_ : LCtx → Level → Set where
  here  : (l ∙ Δ) ∋ˡ l
  there : Δ ∋ˡ l → (l′ ∙ Δ) ∋ˡ l

variable α α′ α₁ α₂ : Δ ∋ˡ l

--! StratTypes
-- ∀ at level l binds a variable of level l and lands at lsuc l ⊔ l′,
-- STRICTLY above l.  That is the whole stratification.
data Type (Δ : LCtx) : Level → Set where
  `_   : Δ ∋ˡ l → Type Δ l
  base : (l : Level) → Type Δ l  -- BASE type at EVERY level: without a
                                 -- closed type at level l, ∀ at level l
                                 -- could never be instantiated, and the
                                 -- Λ-case of the fundamental theorem could
                                 -- not even form its extended environment
  _⇒_  : Type Δ l₁ → Type Δ l₂ → Type Δ (l₁ ⊔ l₂)
  ∀α_  : Type (l ∙ Δ) l′ → Type Δ (lsuc l ⊔ l′)

variable T T′ T₁ T₂ T₃ : Type Δ l

-- ══════════════ §2  Renaming on types ══════════════════════════════
-- This is the σ-calculus of SystemF.agda §3, ported to level contexts:
-- λσ⇑-style, lifting FIRST-CLASS (opaque), composition at a variable
-- PUSHES for renamings and FOLDS for substitutions, no η-rules, and
-- coincidence oriented ˢ→ᴿ.  The curation is what makes it confluent;
-- a naive traversal-composition set is not.

Ren : LCtx → LCtx → Set
Ren Δ₁ Δ₂ = ∀ l → Δ₁ ∋ˡ l → Δ₂ ∋ˡ l

opaque
  wkᴿ : Ren Δ (l ∙ Δ)
  wkᴿ _ = there

  idᴿ : Ren Δ Δ
  idᴿ _ α = α

  _∙ᴿ_ : Δ₂ ∋ˡ l → Ren Δ₁ Δ₂ → Ren (l ∙ Δ₁) Δ₂
  (α ∙ᴿ ζ) _ here      = α
  (_ ∙ᴿ ζ) _ (there α) = ζ _ α

  _&ᴿ_ : Δ₁ ∋ˡ l → Ren Δ₁ Δ₂ → Δ₂ ∋ˡ l
  α &ᴿ ζ = ζ _ α

  _⨟ᴿ_ : Ren Δ₁ Δ₂ → Ren Δ₂ Δ₃ → Ren Δ₁ Δ₃
  (ζ₁ ⨟ᴿ ζ₂) _ α = ζ₂ _ (ζ₁ _ α)

opaque
  unfolding _∙ᴿ_ _⨟ᴿ_ wkᴿ
  _↑ᴿ : Ren Δ₁ Δ₂ → Ren (l ∙ Δ₁) (l ∙ Δ₂)
  _↑ᴿ ζ = here ∙ᴿ (ζ ⨟ᴿ wkᴿ)

_[_]ᴿ : Type Δ₁ l → Ren Δ₁ Δ₂ → Type Δ₂ l
(` α)     [ ζ ]ᴿ = ` (α &ᴿ ζ)
(base l)  [ ζ ]ᴿ = base l
(∀α T)    [ ζ ]ᴿ = ∀α (T [ ζ ↑ᴿ ]ᴿ)
(T₁ ⇒ T₂) [ ζ ]ᴿ = (T₁ [ ζ ]ᴿ) ⇒ (T₂ [ ζ ]ᴿ)

variable ζ ζ′ ζ₁ ζ₂ ζ₃ : Ren Δ₁ Δ₂

-- ══════════════ §3  Substitution on types ══════════════════════════

Sub : LCtx → LCtx → Set
Sub Δ₁ Δ₂ = ∀ l → Δ₁ ∋ˡ l → Type Δ₂ l

opaque
  ⟨_⟩ : Ren Δ₁ Δ₂ → Sub Δ₁ Δ₂
  ⟨ ζ ⟩ _ α = ` (α &ᴿ ζ)

  _∙ˢ_ : Type Δ₂ l → Sub Δ₁ Δ₂ → Sub (l ∙ Δ₁) Δ₂
  (T ∙ˢ η) _ here      = T
  (T ∙ˢ η) _ (there α) = η _ α

  _&ˢ_ : Δ₁ ∋ˡ l → Sub Δ₁ Δ₂ → Type Δ₂ l
  α &ˢ η = η _ α

opaque
  unfolding _∙ˢ_ wkᴿ
  _↑ˢ : Sub Δ₁ Δ₂ → Sub (l ∙ Δ₁) (l ∙ Δ₂)
  _↑ˢ η = (` here) ∙ˢ (λ _ α → (η _ α) [ wkᴿ ]ᴿ)

_[_]ˢ : Type Δ₁ l → Sub Δ₁ Δ₂ → Type Δ₂ l
(` α)     [ η ]ˢ = α &ˢ η
(base l)  [ η ]ˢ = base l
(∀α T)    [ η ]ˢ = ∀α (T [ η ↑ˢ ]ˢ)
(T₁ ⇒ T₂) [ η ]ˢ = (T₁ [ η ]ˢ) ⇒ (T₂ [ η ]ˢ)

opaque
  _⨟ˢ_ : Sub Δ₁ Δ₂ → Sub Δ₂ Δ₃ → Sub Δ₁ Δ₃
  (η₁ ⨟ˢ η₂) _ α = (η₁ _ α) [ η₂ ]ˢ

variable η η′ η₁ η₂ η₃ : Sub Δ₁ Δ₂

-- ══════════════ §4  The σ-calculus, confluent curation ═════════════

opaque
  unfolding wkᴿ idᴿ _∙ᴿ_ _&ᴿ_ _⨟ᴿ_ _↑ᴿ ⟨_⟩ _∙ˢ_ _&ˢ_ _↑ˢ _⨟ˢ_

  `beta-ext-zero    : here &ᴿ (α ∙ᴿ ζ)            ≡ α
  `beta-ext-suc     : (there {l′ = l′} α) &ᴿ (α′ ∙ᴿ ζ) ≡ α &ᴿ ζ
  `beta-id          : α &ᴿ idᴿ                    ≡ α
  `beta-wk          : α &ᴿ (wkᴿ {l = l′})         ≡ there α
  `beta-lift-zero   : here {l = l} &ᴿ (ζ ↑ᴿ)      ≡ here
  `beta-lift-suc    : (there {l′ = l′} α) &ᴿ (ζ ↑ᴿ) ≡ there (α &ᴿ ζ)
  `beta-comp        : α &ᴿ (ζ₁ ⨟ᴿ ζ₂)             ≡ (α &ᴿ ζ₁) &ᴿ ζ₂

  `associativity    : (ζ₁ ⨟ᴿ ζ₂) ⨟ᴿ ζ₃            ≡ ζ₁ ⨟ᴿ (ζ₂ ⨟ᴿ ζ₃)
  `distributivity   : (α ∙ᴿ ζ₁) ⨟ᴿ ζ₂             ≡ (α &ᴿ ζ₂) ∙ᴿ (ζ₁ ⨟ᴿ ζ₂)
  `interact         : (wkᴿ {l = l}) ⨟ᴿ (α ∙ᴿ ζ)   ≡ ζ
  `interact-⨟       : (wkᴿ {l = l}) ⨟ᴿ ((α ∙ᴿ ζ) ⨟ᴿ ζ′) ≡ ζ ⨟ᴿ ζ′
  `comp-idᵣ         : ζ ⨟ᴿ idᴿ                    ≡ ζ
  `comp-idₗ         : idᴿ ⨟ᴿ ζ                    ≡ ζ
  `lift-id          : _↑ᴿ {l = l} (idᴿ {Δ})       ≡ idᴿ
  `lift-wk          : (wkᴿ {l = l}) ⨟ᴿ (ζ ↑ᴿ)     ≡ ζ ⨟ᴿ wkᴿ
  `lift-cons        : (ζ ↑ᴿ) ⨟ᴿ (α ∙ᴿ ζ′)         ≡ α ∙ᴿ (ζ ⨟ᴿ ζ′)
  `lift-cons-⨟      : (ζ ↑ᴿ) ⨟ᴿ ((α ∙ᴿ ζ′) ⨟ᴿ ζ₃) ≡ (α &ᴿ ζ₃) ∙ᴿ (ζ ⨟ᴿ (ζ′ ⨟ᴿ ζ₃))
  `lift-fusion      : (ζ₁ ↑ᴿ) ⨟ᴿ (_↑ᴿ {l = l} ζ₂) ≡ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ
  `lift-wk-⨟        : (wkᴿ {l = l}) ⨟ᴿ ((ζ ↑ᴿ) ⨟ᴿ ζ′) ≡ ζ ⨟ᴿ (wkᴿ ⨟ᴿ ζ′)
  `lift-fusion-⨟    : (ζ₁ ↑ᴿ) ⨟ᴿ ((_↑ᴿ {l = l} ζ₂) ⨟ᴿ ζ′) ≡ ((ζ₁ ⨟ᴿ ζ₂) ↑ᴿ) ⨟ᴿ ζ′

  beta-ext-zero     : here &ˢ (T ∙ˢ η)                ≡ T
  beta-ext-suc      : (there {l′ = l′} α) &ˢ (T ∙ˢ η) ≡ α &ˢ η
  beta-rename       : α &ˢ ⟨ ζ ⟩                      ≡ ` (α &ᴿ ζ)
  beta-lift-zero    : here {l = l} &ˢ (η ↑ˢ)          ≡ ` here
  beta-lift-suc     : (there {l′ = l′} α) &ˢ (η ↑ˢ)   ≡ α &ˢ (η ⨟ˢ ⟨ wkᴿ ⟩)
  beta-⟨⟩-⨟         : α &ˢ (⟨ ζ ⟩ ⨟ˢ η)               ≡ (α &ᴿ ζ) &ˢ η
  beta-lift-zero-⨟  : here {l = l} &ˢ ((η ↑ˢ) ⨟ˢ η′)  ≡ here &ˢ η′
  beta-lift-suc-⨟   : (there {l′ = l′} α) &ˢ ((η ↑ˢ) ⨟ˢ η′) ≡ α &ˢ (η ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ η′))
  beta-fold         : (α &ˢ η₁) [ η₂ ]ˢ               ≡ α &ˢ (η₁ ⨟ˢ η₂)
  beta-fold-ˢᴿ      : (α &ˢ η) [ ζ ]ᴿ                 ≡ α &ˢ (η ⨟ˢ ⟨ ζ ⟩)
  beta-lift-ren-∙   : (α &ᴿ (ζ ↑ᴿ)) &ˢ (T ∙ˢ η)       ≡ α &ˢ (T ∙ˢ (⟨ ζ ⟩ ⨟ˢ η))

  associativity     : (η₁ ⨟ˢ η₂) ⨟ˢ η₃                ≡ η₁ ⨟ˢ (η₂ ⨟ˢ η₃)
  distributivity    : (T ∙ˢ η₁) ⨟ˢ η₂                 ≡ (T [ η₂ ]ˢ) ∙ˢ (η₁ ⨟ˢ η₂)
  interact          : ⟨ wkᴿ {l = l} ⟩ ⨟ˢ (T ∙ˢ η)     ≡ η
  comp-idᵣ          : η ⨟ˢ ⟨ idᴿ ⟩                    ≡ η
  comp-idₗ          : ⟨ idᴿ ⟩ ⨟ˢ η                    ≡ η
  lift-id           : _↑ˢ {l = l} (⟨ idᴿ {Δ} ⟩)       ≡ ⟨ idᴿ ⟩
  lift-wk           : ⟨ wkᴿ {l = l} ⟩ ⨟ˢ (η ↑ˢ)       ≡ η ⨟ˢ ⟨ wkᴿ ⟩
  lift-cons         : (η ↑ˢ) ⨟ˢ (T ∙ˢ η′)             ≡ T ∙ˢ (η ⨟ˢ η′)
  lift-fusion       : (η₁ ↑ˢ) ⨟ˢ (_↑ˢ {l = l} η₂)     ≡ (η₁ ⨟ˢ η₂) ↑ˢ
  lift-wk-⨟         : ⟨ wkᴿ {l = l} ⟩ ⨟ˢ ((η ↑ˢ) ⨟ˢ η′) ≡ η ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ η′)
  lift-fusion-⨟     : (η₁ ↑ˢ) ⨟ˢ ((_↑ˢ {l = l} η₂) ⨟ˢ η′) ≡ ((η₁ ⨟ˢ η₂) ↑ˢ) ⨟ˢ η′

  ⟨⟩-comp           : ⟨ ζ₁ ⟩ ⨟ˢ ⟨ ζ₂ ⟩                ≡ ⟨ ζ₁ ⨟ᴿ ζ₂ ⟩
  ⟨⟩-split          : ⟨ ζ₁ ⨟ᴿ ζ₂ ⟩                    ≡ ⟨ ζ₁ ⟩ ⨟ˢ ⟨ ζ₂ ⟩
  ⟨⟩-split-⨟        : ⟨ ζ₁ ⨟ᴿ ζ₂ ⟩ ⨟ˢ η               ≡ ⟨ ζ₁ ⟩ ⨟ˢ (⟨ ζ₂ ⟩ ⨟ˢ η)
  ⟨⟩-↑-cons         : ⟨ ζ ↑ᴿ ⟩ ⨟ˢ (T ∙ˢ η)            ≡ T ∙ˢ (⟨ ζ ⟩ ⨟ˢ η)
  ⟨⟩-wk-cons        : ⟨ wkᴿ {l = l} ⟩ ⨟ˢ ⟨ α ∙ᴿ ζ ⟩   ≡ ⟨ ζ ⟩
  ⟨⟩-wk-cons-⨟      : ⟨ wkᴿ {l = l} ⟩ ⨟ˢ (⟨ α ∙ᴿ ζ ⟩ ⨟ˢ η) ≡ ⟨ ζ ⟩ ⨟ˢ η
  ⟨⟩-wk-lift        : ⟨ wkᴿ {l = l} ⟩ ⨟ˢ ⟨ ζ ↑ᴿ ⟩     ≡ ⟨ ζ ⟩ ⨟ˢ ⟨ wkᴿ ⟩
  ⟨⟩-wk-lift-⨟      : ⟨ wkᴿ {l = l} ⟩ ⨟ˢ (⟨ ζ ↑ᴿ ⟩ ⨟ˢ η) ≡ ⟨ ζ ⟩ ⨟ˢ (⟨ wkᴿ ⟩ ⨟ˢ η)
  ⟨⟩-lift-lift      : ⟨ ζ₁ ↑ᴿ ⟩ ⨟ˢ ⟨ _↑ᴿ {l = l} ζ₂ ⟩ ≡ ⟨ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ ⟩
  ⟨⟩-lift-lift-⨟    : ⟨ ζ₁ ↑ᴿ ⟩ ⨟ˢ (⟨ _↑ᴿ {l = l} ζ₂ ⟩ ⨟ˢ η) ≡ ⟨ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ ⟩ ⨟ˢ η
  `beta-lift-fusion : (α &ᴿ (ζ₁ ↑ᴿ)) &ᴿ (_↑ᴿ {l = l} ζ₂) ≡ α &ᴿ ((ζ₁ ⨟ᴿ ζ₂) ↑ᴿ)
  ⟨⟩-lift-RS        : ⟨ ζ ↑ᴿ ⟩ ⨟ˢ (_↑ˢ {l = l} η)    ≡ (⟨ ζ ⟩ ⨟ˢ η) ↑ˢ
  ⟨⟩-lift-RS-⨟      : ⟨ ζ ↑ᴿ ⟩ ⨟ˢ ((_↑ˢ {l = l} η) ⨟ˢ η′) ≡ ((⟨ ζ ⟩ ⨟ˢ η) ↑ˢ) ⨟ˢ η′
  beta-lift-ren-↑   : (α &ᴿ (ζ ↑ᴿ)) &ˢ (_↑ˢ {l = l} η) ≡ α &ˢ ((⟨ ζ ⟩ ⨟ˢ η) ↑ˢ)
  beta-lift-ren-↑-⨟ : (α &ᴿ (ζ ↑ᴿ)) &ˢ ((_↑ˢ {l = l} η) ⨟ˢ η′) ≡ α &ˢ (((⟨ ζ ⟩ ⨟ˢ η) ↑ˢ) ⨟ˢ η′)
  ⟨⟩-lift-SR-comp   : (η ↑ˢ) ⨟ˢ ⟨ (_↑ᴿ {l = l} ζ) ⨟ᴿ ζ′ ⟩ ≡ ((η ⨟ˢ ⟨ ζ ⟩) ↑ˢ) ⨟ˢ ⟨ ζ′ ⟩
  ⟨⟩-lift-SR        : (η ↑ˢ) ⨟ˢ ⟨ _↑ᴿ {l = l} ζ ⟩    ≡ (η ⨟ˢ ⟨ ζ ⟩) ↑ˢ
  ⟨⟩-lift-SR-⨟      : (η ↑ˢ) ⨟ˢ (⟨ _↑ᴿ {l = l} ζ ⟩ ⨟ˢ η′) ≡ ((η ⨟ˢ ⟨ ζ ⟩) ↑ˢ) ⨟ˢ η′

  identityᵣ         : T [ idᴿ ]ᴿ            ≡ T
  compositionalityᴿᴿ : (T [ ζ₁ ]ᴿ) [ ζ₂ ]ᴿ  ≡ T [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ
  compositionalityᴿˢ : (T [ ζ₁ ]ᴿ) [ η₂ ]ˢ  ≡ T [ ⟨ ζ₁ ⟩ ⨟ˢ η₂ ]ˢ
  compositionalityˢᴿ : (T [ η₁ ]ˢ) [ ζ₂ ]ᴿ  ≡ T [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ
  compositionalityˢˢ : (T [ η₁ ]ˢ) [ η₂ ]ˢ  ≡ T [ η₁ ⨟ˢ η₂ ]ˢ

  coincidence       : T [ ⟨ ζ ⟩ ]ˢ          ≡ T [ ζ ]ᴿ
  identityᵣˢ        : T [ ⟨ idᴿ ⟩ ]ˢ        ≡ T

  `beta-ext-zero  = refl
  `beta-ext-suc   = refl
  `beta-id        = refl
  `beta-wk        = refl
  `beta-lift-zero = refl
  `beta-lift-suc  = refl
  `beta-comp      = refl

  `associativity   = refl
  `distributivity  = ext² λ { _ here → refl; _ (there α) → refl }
  `interact        = refl
  `interact-⨟      = refl
  `comp-idᵣ        = refl
  `comp-idₗ        = refl
  `lift-id         = ext² λ { _ here → refl; _ (there α) → refl }
  `lift-wk         = refl
  `lift-cons       = ext² λ { _ here → refl; _ (there α) → refl }
  `lift-cons-⨟     = ext² λ { _ here → refl; _ (there α) → refl }
  `lift-fusion     = ext² λ { _ here → refl; _ (there α) → refl }
  `lift-wk-⨟       = ext² λ _ α → refl
  `lift-fusion-⨟   = ext² λ { _ here → refl; _ (there α) → refl }

  beta-ext-zero  = refl
  beta-ext-suc   = refl
  beta-rename    = refl
  beta-lift-zero = refl
  beta-lift-suc {α = α} {η = η} = sym (coincidence {T = η _ α})
  beta-⟨⟩-⨟      = refl
  beta-lift-zero-⨟ = refl
  beta-lift-suc-⨟ {α = α} {η = η} {η′ = η′} = compositionalityᴿˢ {T = η _ α}
  beta-fold      = refl
  beta-fold-ˢᴿ {α = α} {η = η} = sym (coincidence {T = η _ α})
  beta-lift-ren-∙ {α = here}    = refl
  beta-lift-ren-∙ {α = there α} = refl

  associativity {η₁ = η₁} = ext² (λ _ α → compositionalityˢˢ {T = η₁ _ α})
  distributivity  = ext² λ { _ here → refl; _ (there α) → refl }
  interact        = refl
  comp-idᵣ        = ext² (λ _ α → identityᵣˢ)
  comp-idₗ        = refl
  lift-id         = ext² λ { _ here → refl; _ (there α) → refl }
  lift-wk {η = η} = ext² λ _ α → sym (coincidence {T = η _ α})
  lift-cons {η = η} {T = T} {η′ = η′} = ext² λ
    { _ here → refl
    ; _ (there α) → trans (compositionalityᴿˢ {T = η _ α})
                          (cong ((η _ α) [_]ˢ) (interact {T = T} {η = η′})) }
  lift-wk-⨟ {η = η} {η′ = η′} = ext² λ _ α → compositionalityᴿˢ {T = η _ α}
  lift-fusion-⨟ {η₁ = η₁} {η₂ = η₂} {η′ = η′} =
    trans (sym (associativity {η₁ = η₁ ↑ˢ} {η₂ = η₂ ↑ˢ} {η₃ = η′}))
          (cong (_⨟ˢ η′) lift-fusion)
  ⟨⟩-comp         = ext² λ _ α → refl
  ⟨⟩-split        = ext² λ _ α → refl
  ⟨⟩-split-⨟      = ext² λ _ α → refl
  ⟨⟩-wk-cons      = ext² λ _ α → refl
  ⟨⟩-wk-cons-⨟    = ext² λ _ α → refl
  ⟨⟩-wk-lift      = ext² λ _ α → refl
  ⟨⟩-wk-lift-⨟    = ext² λ _ α → refl
  ⟨⟩-lift-lift    = ext² λ { _ here → refl; _ (there α) → refl }
  ⟨⟩-lift-lift-⨟  = ext² λ { _ here → refl; _ (there α) → refl }
  `beta-lift-fusion {α = here}    = refl
  `beta-lift-fusion {α = there α} = refl
  ⟨⟩-lift-RS      = ext² λ { _ here → refl; _ (there α) → refl }
  ⟨⟩-lift-RS-⨟    = ext² λ { _ here → refl; _ (there α) → refl }
  beta-lift-ren-↑ {α = here}    = refl
  beta-lift-ren-↑ {α = there α} = refl
  beta-lift-ren-↑-⨟ {α = here}    = refl
  beta-lift-ren-↑-⨟ {α = there α} = refl
  ⟨⟩-↑-cons       = ext² λ { _ here → refl; _ (there α) → refl }

  identityᵣ {T = (` α)}     = refl
  identityᵣ {T = base _}          = refl
  identityᵣ {T = (∀α T)}    = cong ∀α_ (trans (cong (T [_]ᴿ) `lift-id) (identityᵣ {T = T}))
  identityᵣ {T = (T₁ ⇒ T₂)} = cong₂ _⇒_ (identityᵣ {T = T₁}) (identityᵣ {T = T₂})

  lift-coincidence : ∀ {Δ₁ Δ₂} {l} {ζ : Ren Δ₁ Δ₂} → (_↑ˢ {l = l} ⟨ ζ ⟩) ≡ ⟨ ζ ↑ᴿ ⟩
  lift-coincidence = ext² λ { _ here → refl; _ (there α) → refl }

  coincidence {T = ` α}          = refl
  coincidence {T = base _}            = refl
  coincidence {T = ∀α T} {ζ = ζ} = cong ∀α_ (trans (cong (T [_]ˢ) lift-coincidence) coincidence)
  coincidence {T = T₁ ⇒ T₂}      = cong₂ _⇒_ coincidence coincidence

  lift-compositionalityᴿᴿ : ∀ {Δ₁ Δ₂ Δ₃} {l} {ζ₁ : Ren Δ₁ Δ₂} {ζ₂ : Ren Δ₂ Δ₃} →
                            (ζ₁ ↑ᴿ) ⨟ᴿ (_↑ᴿ {l = l} ζ₂) ≡ (ζ₁ ⨟ᴿ ζ₂) ↑ᴿ
  lift-compositionalityᴿᴿ = ext² λ { _ here → refl; _ (there α) → refl }

  compositionalityᴿᴿ {T = ` α}     = refl
  compositionalityᴿᴿ {T = base _}          = refl
  compositionalityᴿᴿ {T = ∀α T}    = cong ∀α_ (trans compositionalityᴿᴿ (cong (T [_]ᴿ) lift-compositionalityᴿᴿ))
  compositionalityᴿᴿ {T = T₁ ⇒ T₂} = cong₂ _⇒_ compositionalityᴿᴿ compositionalityᴿᴿ

  lift-compositionalityᴿˢ : ∀ {Δ₁ Δ₂ Δ₃} {l} {ζ₁ : Ren Δ₁ Δ₂} {η₂ : Sub Δ₂ Δ₃} →
                            (⟨ ζ₁ ↑ᴿ ⟩ ⨟ˢ (_↑ˢ {l = l} η₂)) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ↑ˢ)
  lift-compositionalityᴿˢ = ext² λ { _ here → refl; _ (there α) → refl }

  compositionalityᴿˢ {T = ` α}     = refl
  compositionalityᴿˢ {T = base _}          = refl
  compositionalityᴿˢ {T = ∀α T}    = cong ∀α_ (trans (compositionalityᴿˢ {T = T}) (cong (T [_]ˢ) lift-compositionalityᴿˢ))
  compositionalityᴿˢ {T = T₁ ⇒ T₂} = cong₂ _⇒_ (compositionalityᴿˢ {T = T₁}) (compositionalityᴿˢ {T = T₂})

  lift-compositionalityˢᴿ : ∀ {Δ₁ Δ₂ Δ₃} {l} {η₁ : Sub Δ₁ Δ₂} {ζ₂ : Ren Δ₂ Δ₃} →
                            ((_↑ˢ {l = l} η₁) ⨟ˢ ⟨ ζ₂ ↑ᴿ ⟩) ≡ ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ↑ˢ)
  lift-compositionalityˢᴿ {η₁ = η₁} {ζ₂ = ζ₂} = ext² λ { _ here → refl; _ (there α) →
    let T = η₁ _ α in
    begin
      (T [ wkᴿ ]ᴿ) [ ⟨ ζ₂ ↑ᴿ ⟩ ]ˢ  ≡⟨ coincidence ⟩
      (T [ wkᴿ ]ᴿ) [ ζ₂ ↑ᴿ ]ᴿ      ≡⟨ compositionalityᴿᴿ ⟩
      T [ wkᴿ ⨟ᴿ (ζ₂ ↑ᴿ) ]ᴿ        ≡⟨ sym compositionalityᴿᴿ ⟩
      (T [ ζ₂ ]ᴿ) [ wkᴿ ]ᴿ         ≡⟨ cong (_[ wkᴿ ]ᴿ) (sym coincidence) ⟩
      (T [ ⟨ ζ₂ ⟩ ]ˢ) [ wkᴿ ]ᴿ     ∎ }

  compositionalityˢᴿ {T = ` α}     = sym coincidence
  compositionalityˢᴿ {T = base _}          = refl
  compositionalityˢᴿ {T = ∀α T}    = cong ∀α_ (trans (compositionalityˢᴿ {T = T}) (cong (T [_]ˢ) lift-compositionalityˢᴿ))
  compositionalityˢᴿ {T = T₁ ⇒ T₂} = cong₂ _⇒_ (compositionalityˢᴿ {T = T₁}) (compositionalityˢᴿ {T = T₂})

  lift-compositionalityˢˢ : ∀ {Δ₁ Δ₂ Δ₃} {l} {η₁ : Sub Δ₁ Δ₂} {η₂ : Sub Δ₂ Δ₃} →
                            ((η₁ ↑ˢ) ⨟ˢ (_↑ˢ {l = l} η₂)) ≡ ((η₁ ⨟ˢ η₂) ↑ˢ)
  lift-compositionalityˢˢ {η₁ = η₁} {η₂ = η₂} = ext² λ { _ here → refl; _ (there α) →
    let T = η₁ _ α in
    begin
      (T [ wkᴿ ]ᴿ) [ η₂ ↑ˢ ]ˢ    ≡⟨ compositionalityᴿˢ {T = T} ⟩
      T [ ⟨ wkᴿ ⟩ ⨟ˢ (η₂ ↑ˢ) ]ˢ  ≡⟨ cong (T [_]ˢ) (ext² λ _ β → sym (coincidence {T = η₂ _ β})) ⟩
      T [ η₂ ⨟ˢ ⟨ wkᴿ ⟩ ]ˢ       ≡⟨ sym (compositionalityˢᴿ {T = T}) ⟩
      (T [ η₂ ]ˢ) [ wkᴿ ]ᴿ       ∎ }

  lift-fusion = lift-compositionalityˢˢ
  ⟨⟩-lift-SR  = lift-compositionalityˢᴿ

  ⟨⟩-lift-SR-comp {η = η} {ζ = ζ} {ζ′ = ζ′} = ext² λ { _ here → refl; _ (there α) →
    let T = η _ α in
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

  compositionalityˢˢ {T = ` α}     = refl
  compositionalityˢˢ {T = base _}          = refl
  compositionalityˢˢ {T = ∀α T}    = cong ∀α_ (trans (compositionalityˢˢ {T = T}) (cong (T [_]ˢ) lift-compositionalityˢˢ))
  compositionalityˢˢ {T = T₁ ⇒ T₂} = cong₂ _⇒_ (compositionalityˢˢ {T = T₁}) (compositionalityˢˢ {T = T₂})

  identityᵣˢ {T = ` α}     = refl
  identityᵣˢ {T = base _}          = refl
  identityᵣˢ {T = ∀α T}    = cong ∀α_ (trans (cong (T [_]ˢ) lift-id) identityᵣˢ)
  identityᵣˢ {T = T₁ ⇒ T₂} = cong₂ _⇒_ identityᵣˢ identityᵣˢ

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

idˢ : Sub Δ Δ
idˢ = ⟨ idᴿ ⟩

_[_]* : Type (l ∙ Δ) l′ → Type Δ l → Type Δ l′
T [ T′ ]* = T [ T′ ∙ˢ idˢ ]ˢ

𝔹 : Type Δ lzero
𝔹 = base lzero

-- ── sanity check: the Church booleans, and that ∀ really lands above ──
-- α at level lzero, body at lzero, so ∀α … : Type ∅ (lsuc lzero).
𝔹ᶜ : Type ∅ (lsuc lzero)
𝔹ᶜ = ∀α ((` here) ⇒ ((` here) ⇒ (` here)))

-- and a level-1 quantifier lands at level 2: no impredicativity anywhere
𝔹ᶜ₁ : Type ∅ (lsuc (lsuc lzero))
𝔹ᶜ₁ = ∀α_ {l = lsuc lzero} ((` here) ⇒ ((` here) ⇒ (` here)))

-- ══════════════ §5  Stratified expressions ═════════════════════════

weaken : Type Δ l′ → Type (l ∙ Δ) l′
weaken T = T [ wkᴿ ]ᴿ

infixl 5 _▷_
--! StratCtx {
data Ctx : LCtx → Set where
  ∅    : Ctx ∅
  _▷_  : Ctx Δ → Type Δ l → Ctx Δ
  _▷*_ : Ctx Δ → (l : Level) → Ctx (l ∙ Δ)
--! }

variable Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx Δ

data _∋_ : Ctx Δ → Type Δ l → Set where
  zero  : (Γ ▷ T) ∋ T
  suc   : Γ ∋ T → (Γ ▷ T′) ∋ T
  suc*  : Γ ∋ T → (Γ ▷* l) ∋ weaken T

variable x x′ x₁ x₂ : Γ ∋ T

--! StratExpr {
data Expr {Δ} (Γ : Ctx Δ) : ∀ {l} → Type Δ l → Set where
  `_    : Γ ∋ T → Expr Γ T
  true  : Expr Γ 𝔹
  false : Expr Γ 𝔹
  λx    : Expr (Γ ▷ T₁) T₂ → Expr Γ (T₁ ⇒ T₂)
  _·_   : Expr Γ (T₁ ⇒ T₂) → Expr Γ T₁ → Expr Γ T₂
  Λα    : Expr (Γ ▷* l) T → Expr Γ (∀α T)
  _·*_  : Expr Γ (∀α T) → (T′ : Type Δ l) → Expr Γ (T [ T′ ]*)
--! }

variable e e′ e₁ e₁′ e₂ e₂′ e₃ : Expr Γ T

-- ── expression renaming ──
-- Every clause below is TRANSPORT-FREE: the type-level rewrite set makes
-- each index equation definitional.  That is the "transfer heaven" half.

_∣_⇒ᴿ_ : Ren Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set
_∣_⇒ᴿ_ {Δ₁ = Δ₁} ζ Γ₁ Γ₂ = ∀ l (T : Type Δ₁ l) → Γ₁ ∋ T → Γ₂ ∋ (T [ ζ ]ᴿ)

--! STIdr {
Idᴿ : idᴿ ∣ Γ ⇒ᴿ Γ
Idᴿ _ _ x = x
--! }

--! STWeakening {
Wkᴿ : (T′ : Type Δ l) → idᴿ ∣ Γ ⇒ᴿ (Γ ▷ T′)
Wkᴿ _ _ _ x = suc x
--! }

--! STTWeakening {
wkᴿ* : ∀ {l} → (wkᴿ {l = l}) ∣ Γ ⇒ᴿ (Γ ▷* l)
wkᴿ* _ _ x = suc* x
--! }

--! STLifting {
_∣_⇑ᴿ_ : ∀ (ζ : Ren Δ₁ Δ₂) {Γ₁ Γ₂} → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → (T : Type Δ₁ l) →
        ζ ∣ (Γ₁ ▷ T) ⇒ᴿ (Γ₂ ▷ (T [ ζ ]ᴿ))
(ζ ∣ ρ ⇑ᴿ T) _ _ zero    = zero
(ζ ∣ ρ ⇑ᴿ T) _ _ (suc x) = suc (ρ _ _ x)
--! }

--! STTLifting {
_∣_↑ᴿ* : ∀ {l} (ζ : Ren Δ₁ Δ₂) {Γ₁ Γ₂} → ζ ∣ Γ₁ ⇒ᴿ Γ₂ →
         (ζ ↑ᴿ) ∣ (Γ₁ ▷* l) ⇒ᴿ (Γ₂ ▷* l)
(ζ ∣ ρ ↑ᴿ*) _ _ (suc* x) = suc* (ρ _ _ x)
--! }

_∣_[_]ᴿ : (ζ : Ren Δ₁ Δ₂) → Expr Γ₁ T → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → Expr Γ₂ (T [ ζ ]ᴿ)
ζ ∣ (` x)      [ ρ ]ᴿ = ` (ρ _ _ x)
_ ∣ true       [ ρ ]ᴿ = true
_ ∣ false      [ ρ ]ᴿ = false
ζ ∣ (λx e)     [ ρ ]ᴿ = λx (ζ ∣ e [ (ζ ∣ ρ ⇑ᴿ _) ]ᴿ)
ζ ∣ (Λα e)     [ ρ ]ᴿ = Λα (_ ∣ e [ (ζ ∣ ρ ↑ᴿ*) ]ᴿ)
_ ∣ (e₁ · e₂)  [ ρ ]ᴿ = (_ ∣ e₁ [ ρ ]ᴿ) · (_ ∣ e₂ [ ρ ]ᴿ)
ζ ∣ (e ·* T′)  [ ρ ]ᴿ = (ζ ∣ e [ ρ ]ᴿ) ·* (T′ [ ζ ]ᴿ)

Weaken : Expr Γ T → Expr (Γ ▷ T′) T
Weaken e = idᴿ ∣ e [ Wkᴿ _ ]ᴿ

weaken* : ∀ {l} → Expr Γ T → Expr (Γ ▷* l) (weaken T)
weaken* e = wkᴿ ∣ e [ wkᴿ* ]ᴿ

-- ── expression substitution ──

_∣_⇒ˢ_ : Sub Δ₁ Δ₂ → Ctx Δ₁ → Ctx Δ₂ → Set
_∣_⇒ˢ_ {Δ₁ = Δ₁} η Γ₁ Γ₂ = ∀ l (T : Type Δ₁ l) → Γ₁ ∋ T → Expr Γ₂ (T [ η ]ˢ)

--! STCoe {
_∣⟪_⟫ : ∀ (ζ : Ren Δ₁ Δ₂) {Γ₁ Γ₂} → ζ ∣ Γ₁ ⇒ᴿ Γ₂ → ⟨ ζ ⟩ ∣ Γ₁ ⇒ˢ Γ₂
(_ ∣⟪ ρ ⟫) _ _ x = ` (ρ _ _ x)
--! }

--! STIds {
Idˢ : idˢ ∣ Γ ⇒ˢ Γ
Idˢ _ _ x = ` x
--! }

--! STSExtension {
_∣_∙ˢ_ : ∀ (η : Sub Δ₁ Δ₂) {Γ₁ Γ₂} {T : Type Δ₁ l} →
        Expr Γ₂ (T [ η ]ˢ) → η ∣ Γ₁ ⇒ˢ Γ₂ → η ∣ (Γ₁ ▷ T) ⇒ˢ Γ₂
(η ∣ e ∙ˢ σ) _ _ zero    = e
(η ∣ e ∙ˢ σ) _ _ (suc x) = σ _ _ x
--! }

--! STSTExtension {
_∣_∙ˢ*_ : ∀ (η : Sub Δ₁ Δ₂) {Γ₁ Γ₂} {l} (T′ : Type Δ₂ l) →
         η ∣ Γ₁ ⇒ˢ Γ₂ → (T′ ∙ˢ η) ∣ (Γ₁ ▷* l) ⇒ˢ Γ₂
(η ∣ T′ ∙ˢ* σ) _ _ (suc* x) = σ _ _ x
--! }

--! STSLifting {
_∣_⇑ˢ_ : ∀ (η : Sub Δ₁ Δ₂) {Γ₁ Γ₂} → η ∣ Γ₁ ⇒ˢ Γ₂ → (T : Type Δ₁ l) →
        η ∣ (Γ₁ ▷ T) ⇒ˢ (Γ₂ ▷ (T [ η ]ˢ))
(η ∣ σ ⇑ˢ T) _ _ zero    = ` zero
(η ∣ σ ⇑ˢ T) _ _ (suc x) = idᴿ ∣ (σ _ _ x) [ Wkᴿ _ ]ᴿ
--! }

--! STSTLifting {
_∣_⇑ˢ* : ∀ {l} (η : Sub Δ₁ Δ₂) {Γ₁ Γ₂} → η ∣ Γ₁ ⇒ˢ Γ₂ →
         (η ↑ˢ) ∣ (Γ₁ ▷* l) ⇒ˢ (Γ₂ ▷* l)
(η ∣ σ ⇑ˢ*) _ _ (suc* x) = wkᴿ ∣ (σ _ _ x) [ wkᴿ* ]ᴿ
--! }

_∣_[_]ˢ : (η : Sub Δ₁ Δ₂) → Expr Γ₁ T → η ∣ Γ₁ ⇒ˢ Γ₂ → Expr Γ₂ (T [ η ]ˢ)
η ∣ (` x)     [ σ ]ˢ = σ _ _ x
_ ∣ true      [ σ ]ˢ = true
_ ∣ false     [ σ ]ˢ = false
η ∣ (λx e)    [ σ ]ˢ = λx (η ∣ e [ (η ∣ σ ⇑ˢ _) ]ˢ)
η ∣ (Λα e)    [ σ ]ˢ = Λα ((η ↑ˢ) ∣ e [ (η ∣ σ ⇑ˢ*) ]ˢ)
η ∣ (e₁ · e₂) [ σ ]ˢ = (η ∣ e₁ [ σ ]ˢ) · (η ∣ e₂ [ σ ]ˢ)
η ∣ (e ·* T′) [ σ ]ˢ = (η ∣ e [ σ ]ˢ) ·* (T′ [ η ]ˢ)

-- ══════════════ §6  Full β-reduction ═══════════════════════════════

_[_] : Expr (Γ ▷ T′) T → Expr Γ T′ → Expr Γ T
e [ e′ ] = idˢ ∣ e [ (idˢ ∣ e′ ∙ˢ Idˢ) ]ˢ

_[*_*] : ∀ {l} {T : Type (l ∙ Δ) l′} {Γ : Ctx Δ} →
         Expr (Γ ▷* l) T → (T′ : Type Δ l) → Expr Γ (T [ T′ ]*)
e [* T′ *] = (T′ ∙ˢ idˢ) ∣ e [ (idˢ ∣ T′ ∙ˢ* Idˢ) ]ˢ

-- FULL β: a congruence in EVERY position, including under λ and Λ.
--! FullBeta {
data _⟶_ : Expr Γ T → Expr Γ T → Set where
  β-λ   :                (λx e₁ · e₂)  ⟶ (e₁ [ e₂ ])
  β-Λ   : ∀ {l l′} {Δ} {T : Type (l ∙ Δ) l′} {Γ : Ctx Δ} {e : Expr (Γ ▷* l) T} {T′} →
                         ((Λα e) ·* T′) ⟶ (e [* T′ *])
  ξ-·₁  : e₁ ⟶ e₁′  →  (e₁ · e₂)     ⟶ (e₁′ · e₂)
  ξ-·₂  : e₂ ⟶ e₂′  →  (e₁ · e₂)     ⟶ (e₁ · e₂′)
  ξ-λ   : e ⟶ e′    →  (λx {T₁ = T₁} e) ⟶ (λx e′)
  ξ-·*  : ∀ {l l′} {Δ} {T : Type (l ∙ Δ) l′} {Γ : Ctx Δ} {e e′ : Expr Γ (∀α T)} {T′} →
          e ⟶ e′    →  (e ·* T′)     ⟶ (e′ ·* T′)
  ξ-Λ   : ∀ {l l′} {Δ} {T : Type (l ∙ Δ) l′} {Γ : Ctx Δ} {e e′ : Expr (Γ ▷* l) T} →
          e ⟶ e′    →  (Λα e)        ⟶ (Λα e′)
--! }

data _⟶*_ : Expr Γ T → Expr Γ T → Set where
  ⟶refl  : e ⟶* e
  ⟶step  : e₁ ⟶ e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃

mutual
  data Neutral : Expr Γ T → Set where
    `_   : (x : Γ ∋ T)                → Neutral (` x)
    _·_  : Neutral e₁ → Normal e₂     → Neutral (e₁ · e₂)
    _·*_ : ∀ {l l′} {Δ} {T : Type (l ∙ Δ) l′} {Γ : Ctx Δ} {e : Expr Γ (∀α T)} →
           Neutral e → (T′ : Type Δ l) → Neutral (e ·* T′)

  data Normal : Expr Γ T → Set where
    ne   : Neutral e                  → Normal e
    true : Normal (true {Γ = Γ})
    false : Normal (false {Γ = Γ})
    λx   : Normal e                   → Normal (λx {T₁ = T₁} e)
    Λα   : ∀ {l l′} {Δ} {T : Type (l ∙ Δ) l′} {Γ : Ctx Δ} {e : Expr (Γ ▷* l) T} →
           Normal e                   → Normal (Λα e)

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)

data Progress : Expr Γ T → Set where
  done  : Normal e     → Progress e
  step  : e ⟶ e′     → Progress e

-- under FULL reduction progress needs no hypothesis on the context:
-- every term either is normal or steps.
--! Progress {
progress : (e : Expr Γ T) → Progress e
--! }
progress (` x)    = done (ne (` x))
progress true     = done true
progress false    = done false
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

NoVar : Ctx Δ → Set
NoVar {Δ} Γ = ∀ {l} {T : Type Δ l} → ¬ (Γ ∋ T)

NoVar-∅ : NoVar ∅
NoVar-∅ ()

-- in a context with no term variables there are no neutral terms
NoVar⇒¬Neutral : NoVar Γ → {e : Expr Γ T} → ¬ Neutral e
NoVar⇒¬Neutral nv (` x)    = nv x
NoVar⇒¬Neutral nv (n · _)  = NoVar⇒¬Neutral nv n
NoVar⇒¬Neutral nv (n ·* _) = NoVar⇒¬Neutral nv n

-- ══════════════ §7  Canonical forms at the Church booleans ═════════
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

truᶜ flsᶜ : Expr ∅ 𝔹ᶜ
truᶜ = Λα (λx (λx (` (suc zero))))
flsᶜ = Λα (λx (λx (` zero)))

-- a context is ATOMIC when every term variable has a type-variable type
Atomic : Ctx Δ → Set
Atomic {Δ} Γ = ∀ {l} {T : Type Δ l} → Γ ∋ T → Σ[ α ∈ Δ ∋ˡ l ] (T ≡ ` α)

atomic-∅ : Atomic {∅} ∅
atomic-∅ ()

atomic-▷* : ∀ {Δ} {Γ : Ctx Δ} {l} → Atomic Γ → Atomic (Γ ▷* l)
atomic-▷* at (suc* x) with at x
... | (α , refl) = (there α , refl)

atomic-▷ : ∀ {Δ} {Γ : Ctx Δ} {l} {α : Δ ∋ˡ l} → Atomic Γ → Atomic (Γ ▷ (` α))
atomic-▷ at zero    = (_ , refl)
atomic-▷ at (suc x) = at x

-- KEY: in an atomic context a neutral term can only have an atomic type.
-- Its head is a variable, and an atomic type admits no elimination.
neutral-atomic : ∀ {Δ} {Γ : Ctx Δ} → Atomic Γ → ∀ {l} {T : Type Δ l} {e : Expr Γ T} →
                 Neutral e → Σ[ α ∈ Δ ∋ˡ l ] (T ≡ ` α)
neutral-atomic at (` x)    = at x
neutral-atomic at (n · _)  with neutral-atomic at n
... | (_ , ())
neutral-atomic at (n ·* _) with neutral-atomic at n
... | (_ , ())

-- the three contexts the ∀/λ/λ-peeling walks through
Ξ₀ : Ctx (lzero ∙ ∅)
Ξ₀ = ∅ ▷* lzero

Ξ₁ : Ctx (lzero ∙ ∅)
Ξ₁ = Ξ₀ ▷ (` here)

Ξ₂ : Ctx (lzero ∙ ∅)
Ξ₂ = Ξ₁ ▷ (` here)

atomic-Ξ₀ : Atomic Ξ₀
atomic-Ξ₀ = atomic-▷* atomic-∅

atomic-Ξ₁ : Atomic Ξ₁
atomic-Ξ₁ = atomic-▷ atomic-Ξ₀

atomic-Ξ₂ : Atomic Ξ₂
atomic-Ξ₂ = atomic-▷ atomic-Ξ₁

-- a neutral in an atomic context IS a variable (stated with T free, so
-- the ·*-index T [ T′ ]* unifies against a metavariable, not a redex)
neutral-var : ∀ {Δ} {Γ : Ctx Δ} → Atomic Γ → ∀ {l} {T : Type Δ l} {e : Expr Γ T} →
              Neutral e → Σ[ x ∈ Γ ∋ T ] (e ≡ ` x)
neutral-var at (` x)    = (x , refl)
neutral-var at (n · _)  with neutral-atomic at n
... | (_ , ())
neutral-var at (n ·* _) with neutral-atomic at n
... | (_ , ())

novar-Ξ₀ : NoVar Ξ₀
novar-Ξ₀ (suc* ())

-- CANONICAL FORMS: a closed NORMAL term of Church-boolean type is
-- literally one of the two Church booleans.
canonical-formsᶜ : (e : Expr ∅ 𝔹ᶜ) → Normal e → (e ≡ truᶜ) ⊎ (e ≡ flsᶜ)
canonical-formsᶜ _ (ne n)           = ⊥-elim (NoVar⇒¬Neutral NoVar-∅ n)
canonical-formsᶜ _ (Λα (ne n))      = ⊥-elim (NoVar⇒¬Neutral novar-Ξ₀ n)
canonical-formsᶜ _ (Λα (λx (ne n))) with neutral-atomic atomic-Ξ₁ n
... | (_ , ())
canonical-formsᶜ _ (Λα (λx (λx (ne n)))) with neutral-var atomic-Ξ₂ n
... | (zero            , refl) = inj₂ refl
... | (suc zero        , refl) = inj₁ refl
... | (suc (suc x)     , _)    = ⊥-elim (novar-Ξ₀ x)

-- ══════════════ §8  The logical relation, PREDICATIVELY ════════════
-- The point of stratification.  With Pred at object level l living in
-- Set (lsuc l), the ∀-case quantifies over Pred S and lands in
-- Set (lsuc l ⊔ l′) — exactly the level Agda assigns to ∀α_.  So the
-- relation is definable with NO --type-in-type.
--
-- Env is INDEXED BY its own type substitution.  That is what makes the
-- composition bookkeeping definitional: here &ˢ (η₁ ⨟ˢ η₂) folds by
-- beta-fold, ⟨wkᴿ⟩ ⨟ˢ (S ∙ˢ η) collapses by interact, and nesting
-- reassociates by associativity — so ⟦⟧-sub below needs no transport.

open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift; lower)

-- strong normalization for FULL β, as accessibility
data SN {Δ} {Γ : Ctx Δ} {l} {T : Type Δ l} (e : Expr Γ T) : Set where
  acc : (∀ {e′} → e ⟶ e′ → SN e′) → SN e

sn-fwd : ∀ {Δ} {Γ : Ctx Δ} {l} {T : Type Δ l} {e e′ : Expr Γ T} →
         SN e → e ⟶ e′ → SN e′
sn-fwd (acc f) s = f s

-- predicates on closed-TYPE terms (term contexts may still be non-empty:
-- the relation has to see under λ, since reduction is full).  Γ is
-- EXPLICIT so that plain fun-ext applies to equalities of predicates.
Pred : ∀ {l} → Type ∅ l → Set (lsuc l)
Pred {l} A = (Γ : Ctx ∅) → Expr Γ A → Set l

-- GIRARD-NEUTRAL: not an introduction form.  This, not the β-normal
-- `Neutral`, is the right hypothesis for CR3.
data Ne {Δ} {Γ : Ctx Δ} : ∀ {l} {T : Type Δ l} → Expr Γ T → Set where
  ne-var  : (x : Γ ∋ T) → Ne (` x)
  ne-app  : (e₁ : Expr Γ (T₁ ⇒ T₂)) (e₂ : Expr Γ T₁) → Ne (e₁ · e₂)
  ne-tapp : ∀ {l l′} {T : Type (l ∙ Δ) l′} (e : Expr Γ (∀α T)) (T′ : Type Δ l) →
            Ne (e ·* T′)


-- context extension (needed already for CR's weakening condition)
data _⊆_ : Ctx ∅ → Ctx ∅ → Set where
  ⊆-refl : ∀ {Γ} → Γ ⊆ Γ
  ⊆-▷    : ∀ {Γ Γ′ l}{A : Type ∅ l} → Γ ⊆ Γ′ → Γ ⊆ (Γ′ ▷ A)

⊆-var : ∀ {Γ Γ′ l}{A : Type ∅ l} → Γ ⊆ Γ′ → Γ ∋ A → Γ′ ∋ A
⊆-var ⊆-refl  x = x
⊆-var (⊆-▷ w) x = suc (⊆-var w x)

⊆-ren : ∀ {Γ Γ′} → Γ ⊆ Γ′ → idᴿ ∣ Γ ⇒ᴿ Γ′
⊆-ren w _ _ x = ⊆-var w x

ren⊆ : ∀ {Γ Γ′ l}{A : Type ∅ l} → Γ ⊆ Γ′ → Expr Γ A → Expr Γ′ A
ren⊆ w e = idᴿ ∣ e [ ⊆-ren w ]ᴿ

⊆-trans : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
⊆-trans w ⊆-refl   = w
⊆-trans w (⊆-▷ w′) = ⊆-▷ (⊆-trans w w′)

⊆-var-trans : ∀ {Γ Γ′ Γ″ l}{A : Type ∅ l}(w : Γ ⊆ Γ′)(w′ : Γ′ ⊆ Γ″)(x : Γ ∋ A) →
              ⊆-var w′ (⊆-var w x) ≡ ⊆-var (⊆-trans w w′) x
⊆-var-trans w ⊆-refl   x = refl
⊆-var-trans w (⊆-▷ w′) x = cong suc (⊆-var-trans w w′ x)

--! CandidateRec {
record CR {l} {A : Type ∅ l} (P : Pred A) : Set l where
  field
    cr-sn  : ∀ {Γ : Ctx ∅} {e : Expr Γ A} → P Γ e → SN e
    cr-fwd : ∀ {Γ : Ctx ∅} {e e′ : Expr Γ A} → P Γ e → e ⟶ e′ → P Γ e′
    cr-exp : ∀ {Γ : Ctx ∅} {e : Expr Γ A} → Ne e →
             (∀ {e′} → e ⟶ e′ → P Γ e′) → P Γ e
    cr-wk  : ∀ {Γ Γ′ : Ctx ∅} {e : Expr Γ A} (w : Γ ⊆ Γ′) → P Γ e → P Γ′ (ren⊆ w e)
--! }
open CR public

maxL : LCtx → Level
maxL ∅       = lzero
maxL (l ∙ Δ) = lsuc l ⊔ maxL Δ

-- semantic environments, INDEXED by the closed type substitution they
-- realise.  Recursion on Δ (a record would need ∀ {l : Level} : Setω).
Env : (Δ : LCtx) → Sub Δ ∅ → Set (maxL Δ)
Env ∅       η = ⊤
Env (l ∙ Δ) η = Pred (here &ˢ η) × Env Δ (⟨ wkᴿ ⟩ ⨟ˢ η)

-- η is EXPLICIT: Env is a recursive function, so its index cannot be
-- recovered by unification from an environment's type.
semE : ∀ {Δ l} (α : Δ ∋ˡ l) (η : Sub Δ ∅) → Env Δ η → Pred (α &ˢ η)
semE here      η (P , _) = P
semE (there α) η (_ , ρ) = semE α (⟨ wkᴿ ⟩ ⨟ˢ η) ρ

-- THE LOGICAL RELATION.  Transport-free: the ∀-case needs
-- (T [ η ↑ˢ ]ˢ) [ S ]* ≡ T [ S ∙ˢ η ]ˢ, definitional via
-- compositionalityˢˢ / lift-cons / comp-idᵣ; and (P , ρ) inhabits
-- Env (l ∙ Δ) (S ∙ˢ η) by beta-ext-zero and interact.
--! LogRel {
⟦_⟧ : ∀ {Δ l} (T : Type Δ l) {η : Sub Δ ∅} → Env Δ η → Pred (T [ η ]ˢ)
--! }
⟦ ` α ⟧      {η} ρ = semE α η ρ
⟦ base l ⟧   ρ Γ e = Lift l (SN e)
⟦ T₁ ⇒ T₂ ⟧  {η} ρ Γ e =
  SN e × (∀ {Γ′} (w : Γ ⊆ Γ′) (e′ : Expr Γ′ (T₁ [ η ]ˢ)) →
            ⟦ T₁ ⟧ ρ Γ′ e′ → ⟦ T₂ ⟧ ρ Γ′ (ren⊆ w e · e′))
⟦ ∀α_ {l = l} T ⟧ {η} ρ Γ e =
  SN e × (∀ {Γ′} (w : Γ ⊆ Γ′) (S : Type ∅ l) (P : Pred S) → CR P →
            ⟦ T ⟧ {S ∙ˢ η} (P , ρ) Γ′ (ren⊆ w e ·* S))

CREnv : ∀ {Δ} {η : Sub Δ ∅} → Env Δ η → Set (maxL Δ)
CREnv {∅}     _        = ⊤
CREnv {l ∙ Δ} (P , ρ)  = Lift (lsuc l) (CR P) × CREnv ρ

-- ══════════════ §9  Expression equational theory (LEMMAS ONLY) ═════
-- No REWRITE pragmas here: the expression-level mirror of the
-- σ-calculus cannot be installed as a rewrite system (SystemF.agda §7
-- says why).  These are ordinary Agda theorems, applied explicitly at
-- their use sites.

--! STComposition {
_,_∣_⨾ᴿ_ : ∀ (ζ₁ : Ren Δ₁ Δ₂) (ζ₂ : Ren Δ₂ Δ₃) {Γ₁ Γ₂ Γ₃} →
        ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂ → ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃ → (ζ₁ ⨟ᴿ ζ₂) ∣ Γ₁ ⇒ᴿ Γ₃
(ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) _ _ x = ρ₂ _ _ (ρ₁ _ _ x)
--! }

--! STSComposition {
_,_∣_⨾ˢ_ : ∀ (η₁ : Sub Δ₁ Δ₂) (η₂ : Sub Δ₂ Δ₃) {Γ₁ Γ₂ Γ₃} →
        η₁ ∣ Γ₁ ⇒ˢ Γ₂ → η₂ ∣ Γ₂ ⇒ˢ Γ₃ → (η₁ ⨟ˢ η₂) ∣ Γ₁ ⇒ˢ Γ₃
(η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) _ _ x = η₂ ∣ (σ₁ _ _ x) [ σ₂ ]ˢ
--! }

-- ── identity ──
Lift-Idᴿ : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} → (idᴿ ∣ (Idᴿ {Γ = Γ}) ⇑ᴿ T) ≡ Idᴿ
Lift-Idᴿ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { zero → refl ; (suc x) → refl }

η*-Idᴿ : ∀ {Δ}{Γ : Ctx Δ}{l} → (_∣_↑ᴿ* {l = l} idᴿ (Idᴿ {Γ = Γ})) ≡ Idᴿ
η*-Idᴿ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Identityᵣᴿ : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} (e : Expr Γ T) → idᴿ ∣ e [ Idᴿ ]ᴿ ≡ e
Identityᵣᴿ (` x)     = refl
Identityᵣᴿ true      = refl
Identityᵣᴿ false     = refl
Identityᵣᴿ (λx e)    = cong λx (trans (cong (idᴿ ∣ e [_]ᴿ) Lift-Idᴿ) (Identityᵣᴿ e))
Identityᵣᴿ (Λα e)    = cong Λα (trans (cong (idᴿ ∣ e [_]ᴿ) η*-Idᴿ) (Identityᵣᴿ e))
Identityᵣᴿ (e₁ · e₂) = cong₂ _·_ (Identityᵣᴿ e₁) (Identityᵣᴿ e₂)
Identityᵣᴿ (e ·* T′) = cong (_·* T′) (Identityᵣᴿ e)

η-Idˢ : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} →
        (idˢ ∣ (Idˢ {Γ = Γ}) ⇑ˢ T) ≡ Idˢ
η-Idˢ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { zero → refl ; (suc x) → refl }

η*-Idˢ : ∀ {Δ}{Γ : Ctx Δ}{l} → (_∣_⇑ˢ* {l = l} idˢ (Idˢ {Γ = Γ})) ≡ Idˢ
η*-Idˢ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Identityᵣ : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} (e : Expr Γ T) → idˢ ∣ e [ Idˢ ]ˢ ≡ e
Identityᵣ (` x)     = refl
Identityᵣ true      = refl
Identityᵣ false     = refl
Identityᵣ (λx e)    = cong λx (trans (cong (idˢ ∣ e [_]ˢ) η-Idˢ) (Identityᵣ e))
Identityᵣ (Λα e)    = cong Λα (trans (cong (idˢ ∣ e [_]ˢ) η*-Idˢ) (Identityᵣ e))
Identityᵣ (e₁ · e₂) = cong₂ _·_ (Identityᵣ e₁) (Identityᵣ e₂)
Identityᵣ (e ·* T′) = cong (_·* T′) (Identityᵣ e)

-- ── ᴿᴿ ──
Lift-Dist-Compᴿᴿ : ∀ {ζ₁ : Ren Δ₁ Δ₂}{ζ₂ : Ren Δ₂ Δ₃}{Γ₁ Γ₂ Γ₃}{T : Type Δ₁ l}
  (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  (ζ₁ , ζ₂ ∣ (ζ₁ ∣ ρ₁ ⇑ᴿ T) ⨾ᴿ (ζ₂ ∣ ρ₂ ⇑ᴿ (T [ ζ₁ ]ᴿ))) ≡ ((ζ₁ ⨟ᴿ ζ₂) ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ⇑ᴿ T)
Lift-Dist-Compᴿᴿ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { zero → refl ; (suc x) → refl }

Lift*-Dist-Compᴿᴿ : ∀ (ζ₁ : Ren Δ₁ Δ₂) (ζ₂ : Ren Δ₂ Δ₃) {Γ₁ Γ₂ Γ₃}{l}
  (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  ((ζ₁ ↑ᴿ) , (ζ₂ ↑ᴿ) ∣ (_∣_↑ᴿ* {l = l} ζ₁ ρ₁) ⨾ᴿ (ζ₂ ∣ ρ₂ ↑ᴿ*)) ≡ ((ζ₁ ⨟ᴿ ζ₂) ∣ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ↑ᴿ*)
Lift*-Dist-Compᴿᴿ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Compositionalityᴿᴿ : ∀ {Δ₁ Δ₂ Δ₃}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{Γ₃ : Ctx Δ₃}{l}{T : Type Δ₁ l}
  (e : Expr Γ₁ T) (ζ₁ : Ren Δ₁ Δ₂) (ζ₂ : Ren Δ₂ Δ₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  ζ₂ ∣ (ζ₁ ∣ e [ ρ₁ ]ᴿ) [ ρ₂ ]ᴿ ≡ (ζ₁ ⨟ᴿ ζ₂) ∣ e [ (ζ₁ , ζ₂ ∣ ρ₁ ⨾ᴿ ρ₂) ]ᴿ
Compositionalityᴿᴿ (` x)     _  _  _  _  = refl
Compositionalityᴿᴿ true      _  _  _  _  = refl
Compositionalityᴿᴿ false     _  _  _  _  = refl
Compositionalityᴿᴿ (λx e)    ζ₁ ζ₂ ρ₁ ρ₂ =
  cong λx (trans (Compositionalityᴿᴿ e _ _ _ _) (cong (_ ∣ e [_]ᴿ) (Lift-Dist-Compᴿᴿ ρ₁ ρ₂)))
Compositionalityᴿᴿ (Λα e)    ζ₁ ζ₂ ρ₁ ρ₂ =
  cong Λα (trans (Compositionalityᴿᴿ e _ _ _ _) (cong (_ ∣ e [_]ᴿ) (Lift*-Dist-Compᴿᴿ ζ₁ ζ₂ ρ₁ ρ₂)))
Compositionalityᴿᴿ (e₁ · e₂) _  _  _  _  = cong₂ _·_ (Compositionalityᴿᴿ e₁ _ _ _ _) (Compositionalityᴿᴿ e₂ _ _ _ _)
Compositionalityᴿᴿ (e ·* T′) ζ₁ ζ₂ ρ₁ ρ₂ = cong (_·* (T′ [ ζ₁ ⨟ᴿ ζ₂ ]ᴿ)) (Compositionalityᴿᴿ e ζ₁ ζ₂ ρ₁ ρ₂)

-- ── ᴿˢ ──
Lift-Dist-Compᴿˢ : ∀ {ζ₁ : Ren Δ₁ Δ₂}{η₂ : Sub Δ₂ Δ₃}{Γ₁ Γ₂ Γ₃}{T : Type Δ₁ l}
  (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  (⟨ ζ₁ ⟩ , η₂ ∣ (_ ∣⟪ (ζ₁ ∣ ρ₁ ⇑ᴿ T) ⟫) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ (T [ ζ₁ ]ᴿ))) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ (⟨ ζ₁ ⟩ , η₂ ∣ (_ ∣⟪ ρ₁ ⟫) ⨾ˢ σ₂) ⇑ˢ T)
Lift-Dist-Compᴿˢ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { zero → refl ; (suc x) → refl }

Lift*-Dist-Compᴿˢ : ∀ (ζ₁ : Ren Δ₁ Δ₂) (η₂ : Sub Δ₂ Δ₃) {Γ₁ Γ₂ Γ₃}{l}
  (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  (⟨ ζ₁ ↑ᴿ ⟩ , (η₂ ↑ˢ) ∣ (_ ∣⟪ (_∣_↑ᴿ* {l = l} ζ₁ ρ₁) ⟫) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ*)) ≡ ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ (⟨ ζ₁ ⟩ , η₂ ∣ (_ ∣⟪ ρ₁ ⟫) ⨾ˢ σ₂) ⇑ˢ*)
Lift*-Dist-Compᴿˢ _ _ _ _ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (suc* x) → refl }

Compositionalityᴿˢ : ∀ {Δ₁ Δ₂ Δ₃}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{Γ₃ : Ctx Δ₃}{l}{T : Type Δ₁ l}
  (e : Expr Γ₁ T) (ζ₁ : Ren Δ₁ Δ₂) (η₂ : Sub Δ₂ Δ₃) (ρ₁ : ζ₁ ∣ Γ₁ ⇒ᴿ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  η₂ ∣ (ζ₁ ∣ e [ ρ₁ ]ᴿ) [ σ₂ ]ˢ ≡ (⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ e [ (⟨ ζ₁ ⟩ , η₂ ∣ (_ ∣⟪ ρ₁ ⟫) ⨾ˢ σ₂) ]ˢ
Compositionalityᴿˢ (` x)     _  _  _  _  = refl
Compositionalityᴿˢ true      _  _  _  _  = refl
Compositionalityᴿˢ false     _  _  _  _  = refl
Compositionalityᴿˢ (λx e)    ζ₁ η₂ ρ₁ σ₂ =
  cong λx (trans (Compositionalityᴿˢ e _ _ _ _)
                 (cong ((⟨ ζ₁ ⟩ ⨟ˢ η₂) ∣ e [_]ˢ) (Lift-Dist-Compᴿˢ ρ₁ σ₂)))
Compositionalityᴿˢ (Λα e)    ζ₁ η₂ ρ₁ σ₂ =
  cong Λα (trans (Compositionalityᴿˢ e _ _ _ _)
                 (cong (((⟨ ζ₁ ⟩ ⨟ˢ η₂) ↑ˢ) ∣ e [_]ˢ) (Lift*-Dist-Compᴿˢ ζ₁ η₂ ρ₁ σ₂)))
Compositionalityᴿˢ (e₁ · e₂) _  _  _  _  = cong₂ _·_ (Compositionalityᴿˢ e₁ _ _ _ _) (Compositionalityᴿˢ e₂ _ _ _ _)
Compositionalityᴿˢ (e ·* T′) ζ₁ η₂ ρ₁ σ₂ = cong (_·* (T′ [ ⟨ ζ₁ ⟩ ⨟ˢ η₂ ]ˢ)) (Compositionalityᴿˢ e ζ₁ η₂ ρ₁ σ₂)

Coincidence : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l}{T : Type Δ₁ l}{ζ : Ren Δ₁ Δ₂}
  (e : Expr Γ₁ T) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) → ⟨ ζ ⟩ ∣ e [ (_ ∣⟪ ρ ⟫) ]ˢ ≡ (ζ ∣ e [ ρ ]ᴿ)
Coincidence {ζ = ζ} e ρ =
  trans (sym (Compositionalityᴿˢ e ζ idˢ ρ Idˢ)) (Identityᵣ (ζ ∣ e [ ρ ]ᴿ))

-- ── ˢᴿ ──
Lift-Dist-Compˢᴿ : ∀ {η₁ : Sub Δ₁ Δ₂}{ζ₂ : Ren Δ₂ Δ₃}{Γ₁ Γ₂ Γ₃}{T : Type Δ₁ l}
  (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  (η₁ , ⟨ ζ₂ ⟩ ∣ (η₁ ∣ σ₁ ⇑ˢ T) ⨾ˢ (_ ∣⟪ (ζ₂ ∣ ρ₂ ⇑ᴿ (T [ η₁ ]ˢ)) ⟫))
  ≡ ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ˢ (_ ∣⟪ ρ₂ ⟫)) ⇑ˢ T)
Lift-Dist-Compˢᴿ {ζ₂ = ζ₂} σ₁ ρ₂ = fun-ext λ _ → fun-ext λ _ → fun-ext λ
  { zero → refl
  ; (suc x) →
      let e = σ₁ _ _ x in
      begin
        _ ≡⟨ Coincidence (idᴿ ∣ e [ Wkᴿ _ ]ᴿ) (ζ₂ ∣ ρ₂ ⇑ᴿ _) ⟩
        _ ≡⟨ Compositionalityᴿᴿ e idᴿ ζ₂ (Wkᴿ _) (ζ₂ ∣ ρ₂ ⇑ᴿ _) ⟩
        _ ≡⟨ sym (Compositionalityᴿᴿ e ζ₂ idᴿ ρ₂ (Wkᴿ _)) ⟩
        _ ≡⟨ cong (idᴿ ∣_[ Wkᴿ _ ]ᴿ) (sym (Coincidence e ρ₂)) ⟩
        _ ∎ }

Lift*-Dist-Compˢᴿ : ∀ (η₁ : Sub Δ₁ Δ₂) (ζ₂ : Ren Δ₂ Δ₃) {Γ₁ Γ₂ Γ₃}{l}
  (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  ((η₁ ↑ˢ) , ⟨ ζ₂ ↑ᴿ ⟩ ∣ (_∣_⇑ˢ* {l = l} η₁ σ₁) ⨾ˢ (_ ∣⟪ (ζ₂ ∣ ρ₂ ↑ᴿ*) ⟫))
  ≡ ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ˢ (_ ∣⟪ ρ₂ ⟫)) ⇑ˢ*)
Lift*-Dist-Compˢᴿ η₁ ζ₂ σ₁ ρ₂ = fun-ext λ _ → fun-ext λ _ → fun-ext λ
  { (suc* x) →
      let e = σ₁ _ _ x in
      begin
        _ ≡⟨ Coincidence (wkᴿ ∣ e [ wkᴿ* ]ᴿ) (ζ₂ ∣ ρ₂ ↑ᴿ*) ⟩
        _ ≡⟨ Compositionalityᴿᴿ e wkᴿ (ζ₂ ↑ᴿ) wkᴿ* (ζ₂ ∣ ρ₂ ↑ᴿ*) ⟩
        _ ≡⟨ sym (Compositionalityᴿᴿ e ζ₂ wkᴿ ρ₂ wkᴿ*) ⟩
        _ ≡⟨ cong (wkᴿ ∣_[ wkᴿ* ]ᴿ) (sym (Coincidence e ρ₂)) ⟩
        _ ∎ }

Compositionalityˢᴿ : ∀ {Δ₁ Δ₂ Δ₃}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{Γ₃ : Ctx Δ₃}{l}{T : Type Δ₁ l}
  (e : Expr Γ₁ T) (η₁ : Sub Δ₁ Δ₂) (ζ₂ : Ren Δ₂ Δ₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (ρ₂ : ζ₂ ∣ Γ₂ ⇒ᴿ Γ₃) →
  ζ₂ ∣ (η₁ ∣ e [ σ₁ ]ˢ) [ ρ₂ ]ᴿ ≡ (η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ e [ (η₁ , ⟨ ζ₂ ⟩ ∣ σ₁ ⨾ˢ (_ ∣⟪ ρ₂ ⟫)) ]ˢ
Compositionalityˢᴿ (` x)     _  _  σ₁ ρ₂ = sym (Coincidence (σ₁ _ _ x) ρ₂)
Compositionalityˢᴿ true      _  _  _  _  = refl
Compositionalityˢᴿ false     _  _  _  _  = refl
Compositionalityˢᴿ (λx e)    η₁ ζ₂ σ₁ ρ₂ =
  cong λx (trans (Compositionalityˢᴿ e η₁ ζ₂ (η₁ ∣ σ₁ ⇑ˢ _) (ζ₂ ∣ ρ₂ ⇑ᴿ _))
                 (cong ((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ∣ e [_]ˢ) (Lift-Dist-Compˢᴿ σ₁ ρ₂)))
Compositionalityˢᴿ (Λα e)    η₁ ζ₂ σ₁ ρ₂ =
  cong Λα (trans (Compositionalityˢᴿ e (η₁ ↑ˢ) (ζ₂ ↑ᴿ) (η₁ ∣ σ₁ ⇑ˢ*) (ζ₂ ∣ ρ₂ ↑ᴿ*))
                 (cong (((η₁ ⨟ˢ ⟨ ζ₂ ⟩) ↑ˢ) ∣ e [_]ˢ) (Lift*-Dist-Compˢᴿ η₁ ζ₂ σ₁ ρ₂)))
Compositionalityˢᴿ (e₁ · e₂) η₁ ζ₂ σ₁ ρ₂ =
  cong₂ _·_ (Compositionalityˢᴿ e₁ η₁ ζ₂ σ₁ ρ₂) (Compositionalityˢᴿ e₂ η₁ ζ₂ σ₁ ρ₂)
Compositionalityˢᴿ (e ·* T′) η₁ ζ₂ σ₁ ρ₂ =
  cong (_·* (T′ [ η₁ ⨟ˢ ⟨ ζ₂ ⟩ ]ˢ)) (Compositionalityˢᴿ e η₁ ζ₂ σ₁ ρ₂)

-- ── ˢˢ ──
Lift-Dist-Compˢˢ : ∀ {η₁ : Sub Δ₁ Δ₂}{η₂ : Sub Δ₂ Δ₃}{Γ₁ Γ₂ Γ₃}{T : Type Δ₁ l}
  (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  (η₁ , η₂ ∣ (η₁ ∣ σ₁ ⇑ˢ T) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ (T [ η₁ ]ˢ)))
  ≡ ((η₁ ⨟ˢ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ⇑ˢ T)
Lift-Dist-Compˢˢ {η₂ = η₂} σ₁ σ₂ = fun-ext λ _ → fun-ext λ _ → fun-ext λ
  { zero → refl
  ; (suc x) →
      let e = σ₁ _ _ x in
      begin
        _ ≡⟨ Compositionalityᴿˢ e idᴿ η₂ (Wkᴿ _) (η₂ ∣ σ₂ ⇑ˢ _) ⟩
        _ ≡⟨ cong ((⟨ idᴿ ⟩ ⨟ˢ η₂) ∣ e [_]ˢ)
               (fun-ext λ _ → fun-ext λ _ → fun-ext λ y → sym (Coincidence (σ₂ _ _ y) (Wkᴿ _))) ⟩
        _ ≡⟨ sym (Compositionalityˢᴿ e η₂ idᴿ σ₂ (Wkᴿ _)) ⟩
        _ ∎ }

Lift*-Dist-Compˢˢ : ∀ (η₁ : Sub Δ₁ Δ₂) (η₂ : Sub Δ₂ Δ₃) {Γ₁ Γ₂ Γ₃}{l}
  (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  ((η₁ ↑ˢ) , (η₂ ↑ˢ) ∣ (_∣_⇑ˢ* {l = l} η₁ σ₁) ⨾ˢ (η₂ ∣ σ₂ ⇑ˢ*))
  ≡ ((η₁ ⨟ˢ η₂) ∣ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ⇑ˢ*)
Lift*-Dist-Compˢˢ η₁ η₂ σ₁ σ₂ = fun-ext λ _ → fun-ext λ _ → fun-ext λ
  { (suc* x) →
      let e = σ₁ _ _ x in
      begin
        _ ≡⟨ Compositionalityᴿˢ e wkᴿ (η₂ ↑ˢ) wkᴿ* (η₂ ∣ σ₂ ⇑ˢ*) ⟩
        _ ≡⟨ cong ((⟨ wkᴿ ⟩ ⨟ˢ (η₂ ↑ˢ)) ∣ e [_]ˢ)
               (fun-ext λ _ → fun-ext λ _ → fun-ext λ y → sym (Coincidence (σ₂ _ _ y) wkᴿ*)) ⟩
        _ ≡⟨ sym (Compositionalityˢᴿ e η₂ wkᴿ σ₂ wkᴿ*) ⟩
        _ ∎ }

Compositionalityˢˢ : ∀ {Δ₁ Δ₂ Δ₃}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{Γ₃ : Ctx Δ₃}{l}{T : Type Δ₁ l}
  (e : Expr Γ₁ T) (η₁ : Sub Δ₁ Δ₂) (η₂ : Sub Δ₂ Δ₃) (σ₁ : η₁ ∣ Γ₁ ⇒ˢ Γ₂) (σ₂ : η₂ ∣ Γ₂ ⇒ˢ Γ₃) →
  η₂ ∣ (η₁ ∣ e [ σ₁ ]ˢ) [ σ₂ ]ˢ ≡ (η₁ ⨟ˢ η₂) ∣ e [ (η₁ , η₂ ∣ σ₁ ⨾ˢ σ₂) ]ˢ
Compositionalityˢˢ (` x)     _  _  _  _  = refl
Compositionalityˢˢ true      _  _  _  _  = refl
Compositionalityˢˢ false     _  _  _  _  = refl
Compositionalityˢˢ (λx e)    η₁ η₂ σ₁ σ₂ =
  cong λx (trans (Compositionalityˢˢ e η₁ η₂ (η₁ ∣ σ₁ ⇑ˢ _) (η₂ ∣ σ₂ ⇑ˢ _))
                 (cong ((η₁ ⨟ˢ η₂) ∣ e [_]ˢ) (Lift-Dist-Compˢˢ σ₁ σ₂)))
Compositionalityˢˢ (Λα e)    η₁ η₂ σ₁ σ₂ =
  cong Λα (trans (Compositionalityˢˢ e (η₁ ↑ˢ) (η₂ ↑ˢ) (η₁ ∣ σ₁ ⇑ˢ*) (η₂ ∣ σ₂ ⇑ˢ*))
                 (cong (((η₁ ⨟ˢ η₂) ↑ˢ) ∣ e [_]ˢ) (Lift*-Dist-Compˢˢ η₁ η₂ σ₁ σ₂)))
Compositionalityˢˢ (e₁ · e₂) η₁ η₂ σ₁ σ₂ =
  cong₂ _·_ (Compositionalityˢˢ e₁ η₁ η₂ σ₁ σ₂) (Compositionalityˢˢ e₂ η₁ η₂ σ₁ σ₂)
Compositionalityˢˢ (e ·* T′) η₁ η₂ σ₁ σ₂ =
  cong (_·* (T′ [ η₁ ⨟ˢ η₂ ]ˢ)) (Compositionalityˢˢ e η₁ η₂ σ₁ σ₂)

-- ══════════════ §10  Substitution commutes with reduction ══════════

β-λ-sub : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l₁ l₂}{T₁ : Type Δ₁ l₁}{T₂ : Type Δ₁ l₂}
  (η : Sub Δ₁ Δ₂) (e₁ : Expr (Γ₁ ▷ T₁) T₂) (e₂ : Expr Γ₁ T₁) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
  η ∣ (e₁ [ e₂ ]) [ σ ]ˢ ≡ (η ∣ e₁ [ (η ∣ σ ⇑ˢ T₁) ]ˢ) [ η ∣ e₂ [ σ ]ˢ ]
β-λ-sub η e₁ e₂ σ =
  begin
    η ∣ (idˢ ∣ e₁ [ (idˢ ∣ e₂ ∙ˢ Idˢ) ]ˢ) [ σ ]ˢ
  ≡⟨ Compositionalityˢˢ e₁ idˢ η (idˢ ∣ e₂ ∙ˢ Idˢ) σ ⟩
    η ∣ e₁ [ (idˢ , η ∣ (idˢ ∣ e₂ ∙ˢ Idˢ) ⨾ˢ σ) ]ˢ
  ≡⟨ cong (η ∣ e₁ [_]ˢ) (fun-ext λ _ → fun-ext λ _ → fun-ext λ
       { zero    → refl
       ; (suc x) → sym (trans (Compositionalityᴿˢ (σ _ _ x) idᴿ idˢ (Wkᴿ _)
                                 (idˢ ∣ (η ∣ e₂ [ σ ]ˢ) ∙ˢ Idˢ))
                              (Identityᵣ (σ _ _ x))) }) ⟩
    η ∣ e₁ [ (η , idˢ ∣ (η ∣ σ ⇑ˢ _) ⨾ˢ (idˢ ∣ (η ∣ e₂ [ σ ]ˢ) ∙ˢ Idˢ)) ]ˢ
  ≡⟨ sym (Compositionalityˢˢ e₁ η idˢ (η ∣ σ ⇑ˢ _) (idˢ ∣ (η ∣ e₂ [ σ ]ˢ) ∙ˢ Idˢ)) ⟩
    (η ∣ e₁ [ (η ∣ σ ⇑ˢ _) ]ˢ) [ η ∣ e₂ [ σ ]ˢ ]
  ∎

β-Λ-sub : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l l′}{T : Type (l ∙ Δ₁) l′}
  (η : Sub Δ₁ Δ₂) (e : Expr (Γ₁ ▷* l) T) (T′ : Type Δ₁ l) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
  η ∣ (e [* T′ *]) [ σ ]ˢ ≡ ((η ↑ˢ) ∣ e [ (η ∣ σ ⇑ˢ*) ]ˢ) [* T′ [ η ]ˢ *]
β-Λ-sub η e T′ σ =
  begin
    η ∣ ((T′ ∙ˢ idˢ) ∣ e [ (idˢ ∣ T′ ∙ˢ* Idˢ) ]ˢ) [ σ ]ˢ
  ≡⟨ Compositionalityˢˢ e (T′ ∙ˢ idˢ) η (idˢ ∣ T′ ∙ˢ* Idˢ) σ ⟩
    ((T′ [ η ]ˢ) ∙ˢ η) ∣ e [ ((T′ ∙ˢ idˢ) , η ∣ (idˢ ∣ T′ ∙ˢ* Idˢ) ⨾ˢ σ) ]ˢ
  ≡⟨ cong (((T′ [ η ]ˢ) ∙ˢ η) ∣ e [_]ˢ) (fun-ext λ _ → fun-ext λ _ → fun-ext λ
       { (suc* x) → sym (trans (Compositionalityᴿˢ (σ _ _ x) wkᴿ ((T′ [ η ]ˢ) ∙ˢ idˢ) wkᴿ*
                                  (idˢ ∣ (T′ [ η ]ˢ) ∙ˢ* Idˢ))
                               (Identityᵣ (σ _ _ x))) }) ⟩
    ((T′ [ η ]ˢ) ∙ˢ η) ∣ e [ ((η ↑ˢ) , ((T′ [ η ]ˢ) ∙ˢ idˢ) ∣ (η ∣ σ ⇑ˢ*) ⨾ˢ (idˢ ∣ (T′ [ η ]ˢ) ∙ˢ* Idˢ)) ]ˢ
  ≡⟨ sym (Compositionalityˢˢ e (η ↑ˢ) ((T′ [ η ]ˢ) ∙ˢ idˢ) (η ∣ σ ⇑ˢ*) (idˢ ∣ (T′ [ η ]ˢ) ∙ˢ* Idˢ)) ⟩
    ((η ↑ˢ) ∣ e [ (η ∣ σ ⇑ˢ*) ]ˢ) [* T′ [ η ]ˢ *]
  ∎

-- reduction is preserved by substitution
⟶-sub : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l}{T : Type Δ₁ l}{e e′ : Expr Γ₁ T}
        (η : Sub Δ₁ Δ₂) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) →
        e ⟶ e′ → (η ∣ e [ σ ]ˢ) ⟶ (η ∣ e′ [ σ ]ˢ)
⟶-sub η σ (β-λ {e₁ = a} {e₂ = b}) =
  subst (λ z → (η ∣ ((λx a) · b) [ σ ]ˢ) ⟶ z) (sym (β-λ-sub η a b σ)) β-λ
⟶-sub η σ (β-Λ {e = a} {T′ = A}) =
  subst (λ z → (η ∣ ((Λα a) ·* A) [ σ ]ˢ) ⟶ z) (sym (β-Λ-sub η a A σ)) β-Λ
⟶-sub η σ (ξ-·₁ s) = ξ-·₁ (⟶-sub η σ s)
⟶-sub η σ (ξ-·₂ s) = ξ-·₂ (⟶-sub η σ s)
⟶-sub η σ (ξ-λ s)  = ξ-λ (⟶-sub η (η ∣ σ ⇑ˢ _) s)
⟶-sub η σ (ξ-·* s) = ξ-·* (⟶-sub η σ s)
⟶-sub η σ (ξ-Λ s)  = ξ-Λ (⟶-sub (η ↑ˢ) (η ∣ σ ⇑ˢ*) s)

-- SN reflects along substitution: if the substituted term is SN, so is
-- the original.  This is what turns the fundamental theorem into SN.
sn-sub : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l}{T : Type Δ₁ l}
         (η : Sub Δ₁ Δ₂) (σ : η ∣ Γ₁ ⇒ˢ Γ₂) {e : Expr Γ₁ T} →
         SN (η ∣ e [ σ ]ˢ) → SN e
sn-sub η σ (acc f) = acc λ s → sn-sub η σ (f (⟶-sub η σ s))

-- ══════════════ §11  Semantic type substitution ════════════════════
-- RENAMINGS FIRST.  The renaming action is defined by lookup, never by
-- ⟦_⟧, so its lift/weaken laws need no reference to ⟦⟧-ren and the
-- mutual dependency that would otherwise arise is broken.
--
-- NOTE: the realised substitution is an EXPLICIT argument everywhere.
-- Env is a function defined by recursion on Δ, not a datatype, so
-- Env Δ ?η ≟ Env Δ η is not an injective unification problem and the
-- index can never be recovered from an environment's type.

⊛ : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (η : Sub Δ₂ ∅) → Env Δ₂ η → Env Δ₁ (⟨ ζ ⟩ ⨟ˢ η)
⊛ {∅}      ζ η ρ = tt
⊛ {l ∙ Δ₁} ζ η ρ = semE (here &ᴿ ζ) η ρ , ⊛ (wkᴿ ⨟ᴿ ζ) η ρ

semE-⊛ : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (ζ : Ren Δ₁ Δ₂) (η : Sub Δ₂ ∅) (ρ : Env Δ₂ η) →
         semE α (⟨ ζ ⟩ ⨟ˢ η) (⊛ ζ η ρ) ≡ semE (α &ᴿ ζ) η ρ
semE-⊛ here      ζ η ρ = refl
semE-⊛ (there α) ζ η ρ = semE-⊛ α (wkᴿ ⨟ᴿ ζ) η ρ

-- stated with projections, not pattern-matched pairs: destructuring an
-- Env at (l ∙ Δ) would need the η-law (here &ˢ η) ∙ˢ (⟨wkᴿ⟩ ⨟ˢ η) ≡ η,
-- which is deliberately NOT a rewrite (η is incompatible with confluence)
⊛-wk : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (η : Sub (l ∙ Δ₂) ∅) (ρ : Env (l ∙ Δ₂) η) →
       ⊛ (ζ ⨟ᴿ wkᴿ) η ρ ≡ ⊛ ζ (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ)
⊛-wk {Δ₁ = ∅}      ζ η ρ = refl
⊛-wk {Δ₁ = l ∙ Δ₁} ζ η ρ =
  cong (semE (here &ᴿ ζ) (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ) ,_) (⊛-wk (wkᴿ ⨟ᴿ ζ) η ρ)

⊛-wk₀ : ∀ {Δ l} (η : Sub (l ∙ Δ) ∅) (ρ : Env (l ∙ Δ) η) →
        ⊛ wkᴿ η ρ ≡ proj₂ ρ
⊛-wk₀ {Δ = ∅}     η ρ = refl
⊛-wk₀ {Δ = l ∙ Δ} η ρ =
  cong (semE here (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ) ,_)
       (trans (⊛-wk wkᴿ η ρ) (⊛-wk₀ (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ)))

⊛-lift : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (η : Sub (l ∙ Δ₂) ∅) (ρ : Env (l ∙ Δ₂) η) →
         ⊛ (ζ ↑ᴿ) η ρ ≡ (proj₁ ρ , ⊛ ζ (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ))
⊛-lift ζ η ρ = cong (proj₁ ρ ,_) (⊛-wk ζ η ρ)

-- the interpretation commutes with type RENAMING
⟦⟧-ren : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Sub Δ₂ ∅) (ρ : Env Δ₂ η) →
         ⟦ T [ ζ ]ᴿ ⟧ ρ ≡ ⟦ T ⟧ (⊛ ζ η ρ)
⟦⟧-ren (` α)     ζ η ρ = sym (semE-⊛ α ζ η ρ)
⟦⟧-ren (base l)  ζ η ρ = refl
⟦⟧-ren (T₁ ⇒ T₂) ζ η ρ =
  fun-ext λ Γ → fun-ext λ e →
    cong₂ (λ P Q → SN e × (∀ {Γ′} (w : Γ ⊆ Γ′) e′ → P Γ′ e′ → Q Γ′ (ren⊆ w e · e′)))
          (⟦⟧-ren T₁ ζ η ρ) (⟦⟧-ren T₂ ζ η ρ)
⟦⟧-ren (∀α_ {l = l} T) ζ η ρ =
  fun-ext λ Γ → fun-ext λ e →
    cong (λ f → SN e × (∀ {Γ′} (w : Γ ⊆ Γ′) (S : Type ∅ l) (P : Pred S) → CR P →
                          f S P Γ′ (ren⊆ w e ·* S)))
         (fun-ext λ S → fun-ext λ P → ∀step S P)
  where
  ∀step : ∀ (S : Type ∅ l) (P : Pred S) →
          ⟦ T [ ζ ↑ᴿ ]ᴿ ⟧ {S ∙ˢ η} (P , ρ)
        ≡ ⟦ T ⟧ {S ∙ˢ (⟨ ζ ⟩ ⨟ˢ η)} (P , ⊛ ζ η ρ)
  ∀step S P = trans (⟦⟧-ren T (ζ ↑ᴿ) (S ∙ˢ η) (P , ρ))
                    (cong (⟦ T ⟧ {S ∙ˢ (⟨ ζ ⟩ ⨟ˢ η)}) (⊛-lift ζ (S ∙ˢ η) (P , ρ)))

-- ── now SUBSTITUTIONS, mirroring the renaming development ──

⊙ : ∀ {Δ₁ Δ₂} (η₁ : Sub Δ₁ Δ₂) (η₂ : Sub Δ₂ ∅) → Env Δ₂ η₂ → Env Δ₁ (η₁ ⨟ˢ η₂)
⊙ {∅}      η₁ η₂ ρ = tt
⊙ {l ∙ Δ₁} η₁ η₂ ρ = ⟦ here &ˢ η₁ ⟧ {η₂} ρ , ⊙ (⟨ wkᴿ ⟩ ⨟ˢ η₁) η₂ ρ

semE-⊙ : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (η₁ : Sub Δ₁ Δ₂) (η₂ : Sub Δ₂ ∅) (ρ : Env Δ₂ η₂) →
         semE α (η₁ ⨟ˢ η₂) (⊙ η₁ η₂ ρ) ≡ ⟦ α &ˢ η₁ ⟧ {η₂} ρ
semE-⊙ here      η₁ η₂ ρ = refl
semE-⊙ (there α) η₁ η₂ ρ = semE-⊙ α (⟨ wkᴿ ⟩ ⨟ˢ η₁) η₂ ρ

-- an embedded renaming acts as the renaming action
⊙-⟨⟩ : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (η : Sub Δ₂ ∅) (ρ : Env Δ₂ η) →
       ⊙ ⟨ ζ ⟩ η ρ ≡ ⊛ ζ η ρ
⊙-⟨⟩ {Δ₁ = ∅}      ζ η ρ = refl
⊙-⟨⟩ {Δ₁ = l ∙ Δ₁} ζ η ρ =
  cong (semE (here &ᴿ ζ) η ρ ,_) (⊙-⟨⟩ (wkᴿ ⨟ᴿ ζ) η ρ)

⊙-wk : ∀ {Δ₁ Δ₂ l} (η₁ : Sub Δ₁ Δ₂) (η₂ : Sub (l ∙ Δ₂) ∅) (ρ : Env (l ∙ Δ₂) η₂) →
       ⊙ (η₁ ⨟ˢ ⟨ wkᴿ ⟩) η₂ ρ ≡ ⊙ η₁ (⟨ wkᴿ ⟩ ⨟ˢ η₂) (proj₂ ρ)
⊙-wk {Δ₁ = ∅}      η₁ η₂ ρ = refl
⊙-wk {Δ₁ = l ∙ Δ₁} η₁ η₂ ρ =
  cong₂ _,_
    (trans (⟦⟧-ren (here &ˢ η₁) wkᴿ η₂ ρ)
           (cong (⟦ here &ˢ η₁ ⟧ {⟨ wkᴿ ⟩ ⨟ˢ η₂}) (⊛-wk₀ η₂ ρ)))
    (⊙-wk (⟨ wkᴿ ⟩ ⨟ˢ η₁) η₂ ρ)

⊙-lift : ∀ {Δ₁ Δ₂ l} (η₁ : Sub Δ₁ Δ₂) (η₂ : Sub (l ∙ Δ₂) ∅) (ρ : Env (l ∙ Δ₂) η₂) →
         ⊙ (η₁ ↑ˢ) η₂ ρ ≡ (proj₁ ρ , ⊙ η₁ (⟨ wkᴿ ⟩ ⨟ˢ η₂) (proj₂ ρ))
⊙-lift η₁ η₂ ρ = cong (proj₁ ρ ,_) (⊙-wk η₁ η₂ ρ)

⊙-id : ∀ {Δ} (η : Sub Δ ∅) (ρ : Env Δ η) → ⊙ idˢ η ρ ≡ ρ
⊙-id {∅}     η ρ = refl
⊙-id {l ∙ Δ} η ρ =
  cong (semE here η ρ ,_)
       (trans (⊙-⟨⟩ wkᴿ η ρ) (⊛-wk₀ η ρ))

-- THE INTERPRETATION COMMUTES WITH TYPE SUBSTITUTION
⟦⟧-sub : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (η₁ : Sub Δ₁ Δ₂) (η₂ : Sub Δ₂ ∅) (ρ : Env Δ₂ η₂) →
         ⟦ T [ η₁ ]ˢ ⟧ {η₂} ρ ≡ ⟦ T ⟧ (⊙ η₁ η₂ ρ)
⟦⟧-sub (` α)     η₁ η₂ ρ = sym (semE-⊙ α η₁ η₂ ρ)
⟦⟧-sub (base l)  η₁ η₂ ρ = refl
⟦⟧-sub (T₁ ⇒ T₂) η₁ η₂ ρ =
  fun-ext λ Γ → fun-ext λ e →
    cong₂ (λ P Q → SN e × (∀ {Γ′} (w : Γ ⊆ Γ′) e′ → P Γ′ e′ → Q Γ′ (ren⊆ w e · e′)))
          (⟦⟧-sub T₁ η₁ η₂ ρ) (⟦⟧-sub T₂ η₁ η₂ ρ)
⟦⟧-sub (∀α_ {l = l} T) η₁ η₂ ρ =
  fun-ext λ Γ → fun-ext λ e →
    cong (λ f → SN e × (∀ {Γ′} (w : Γ ⊆ Γ′) (S : Type ∅ l) (P : Pred S) → CR P →
                          f S P Γ′ (ren⊆ w e ·* S)))
         (fun-ext λ S → fun-ext λ P → ∀stepˢ S P)
  where
  ∀stepˢ : ∀ (S : Type ∅ l) (P : Pred S) →
           ⟦ T [ η₁ ↑ˢ ]ˢ ⟧ {S ∙ˢ η₂} (P , ρ)
         ≡ ⟦ T ⟧ {S ∙ˢ (η₁ ⨟ˢ η₂)} (P , ⊙ η₁ η₂ ρ)
  ∀stepˢ S P = trans (⟦⟧-sub T (η₁ ↑ˢ) (S ∙ˢ η₂) (P , ρ))
                     (cong (⟦ T ⟧ {S ∙ˢ (η₁ ⨟ˢ η₂)}) (⊙-lift η₁ (S ∙ˢ η₂) (P , ρ)))

-- the single-variable instance the ·*-case of the fundamental theorem needs
⟦⟧-[]* : ∀ {Δ l l′} (T : Type (l ∙ Δ) l′) (T′ : Type Δ l) (η : Sub Δ ∅) (ρ : Env Δ η) →
         ⟦ T [ T′ ]* ⟧ {η} ρ ≡ ⟦ T ⟧ {(T′ [ η ]ˢ) ∙ˢ η} (⟦ T′ ⟧ {η} ρ , ρ)
⟦⟧-[]* T T′ η ρ =
  trans (⟦⟧-sub T (T′ ∙ˢ idˢ) η ρ)
        (cong (⟦ T ⟧ {(T′ [ η ]ˢ) ∙ˢ η}) (cong (⟦ T′ ⟧ {η} ρ ,_) (⊙-id η ρ)))

-- ══════════════ §12  SN and reduction infrastructure ═══════════════

-- reduction is preserved by RENAMING (derived from ⟶-sub via Coincidence;
-- the two index types are definitionally equal because coincidence is a
-- registered type-level rewrite)
⟶-ren : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l}{T : Type Δ₁ l}
        (ζ : Ren Δ₁ Δ₂) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) {e e′ : Expr Γ₁ T} →
        e ⟶ e′ → (ζ ∣ e [ ρ ]ᴿ) ⟶ (ζ ∣ e′ [ ρ ]ᴿ)
⟶-ren ζ ρ {e} {e′} s =
  subst₂ _⟶_ (Coincidence e ρ) (Coincidence e′ ρ) (⟶-sub ⟨ ζ ⟩ (_ ∣⟪ ρ ⟫) s)

-- SN reflects along renaming (the EASY direction: needs only ⟶-ren)
sn-ren-inv : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l}{T : Type Δ₁ l}
             (ζ : Ren Δ₁ Δ₂) (ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) {e : Expr Γ₁ T} →
             SN (ζ ∣ e [ ρ ]ᴿ) → SN e
sn-ren-inv ζ ρ (acc f) = acc λ s → sn-ren-inv ζ ρ (f (⟶-ren ζ ρ s))

-- SN closure properties
sn-λ : ∀ {Δ}{Γ : Ctx Δ}{l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}{e : Expr (Γ ▷ T₁) T₂} →
       SN e → SN (λx e)
sn-λ (acc f) = acc λ { (ξ-λ s) → sn-λ (f s) }

sn-Λ : ∀ {Δ}{Γ : Ctx Δ}{l l′}{T : Type (l ∙ Δ) l′}{e : Expr (Γ ▷* l) T} →
       SN e → SN (Λα e)
sn-Λ (acc f) = acc λ { (ξ-Λ s) → sn-Λ (f s) }

sn-·₁ : ∀ {Δ}{Γ : Ctx Δ}{l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}
        {e₁ : Expr Γ (T₁ ⇒ T₂)}{e₂ : Expr Γ T₁} → SN (e₁ · e₂) → SN e₁
sn-·₁ (acc f) = acc λ s → sn-·₁ (f (ξ-·₁ s))

sn-·*₁ : ∀ {Δ}{Γ : Ctx Δ}{l l′}{T : Type (l ∙ Δ) l′}{e : Expr Γ (∀α T)}{T′ : Type Δ l} →
         SN (e ·* T′) → SN e
sn-·*₁ (acc f) = acc λ s → sn-·*₁ (f (ξ-·* s))

-- multi-step congruences
⟶*-trans : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l}{e₁ e₂ e₃ : Expr Γ T} →
           e₁ ⟶* e₂ → e₂ ⟶* e₃ → e₁ ⟶* e₃
⟶*-trans ⟶refl        q = q
⟶*-trans (⟶step s p)  q = ⟶step s (⟶*-trans p q)

⟶*-· : ∀ {Δ}{Γ : Ctx Δ}{l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}
       {e₁ e₁′ : Expr Γ (T₁ ⇒ T₂)}{e₂ : Expr Γ T₁} →
       e₁ ⟶* e₁′ → (e₁ · e₂) ⟶* (e₁′ · e₂)
⟶*-· ⟶refl       = ⟶refl
⟶*-· (⟶step s p) = ⟶step (ξ-·₁ s) (⟶*-· p)

⟶*-·₂ : ∀ {Δ}{Γ : Ctx Δ}{l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}
        {e₁ : Expr Γ (T₁ ⇒ T₂)}{e₂ e₂′ : Expr Γ T₁} →
        e₂ ⟶* e₂′ → (e₁ · e₂) ⟶* (e₁ · e₂′)
⟶*-·₂ ⟶refl       = ⟶refl
⟶*-·₂ (⟶step s p) = ⟶step (ξ-·₂ s) (⟶*-·₂ p)

-- forward closure of a candidate along ⟶*
cr-fwd* : ∀ {l}{A : Type ∅ l}{P : Pred A} → CR P →
          ∀ {Γ : Ctx ∅}{e e′ : Expr Γ A} → P Γ e → e ⟶* e′ → P Γ e′
cr-fwd* cr p ⟶refl       = p
cr-fwd* cr p (⟶step s q) = cr-fwd* cr (cr-fwd cr p s) q

-- ══════════════ §13  Canonicity, modulo the fundamental theorem ════

-- level 0 is now INHABITED, so ∀ at level 0 can actually be instantiated
_ : Type ∅ lzero
_ = 𝔹

_ : Expr ∅ (((` here) ⇒ ((` here) ⇒ (` here))) [ 𝔹 ]*)
_ = truᶜ ·* 𝔹

-- canonical forms at the BASE type: trivial, because a closed normal
-- term cannot be neutral
canonical-forms : (e : Expr ∅ 𝔹) → Normal e → (e ≡ true) ⊎ (e ≡ false)
canonical-forms _ (ne n) = ⊥-elim (NoVar⇒¬Neutral NoVar-∅ n)
canonical-forms _ true   = inj₁ refl
canonical-forms _ false  = inj₂ refl

-- SN gives a reduction sequence to a normal form (progress supplies the step)
sn→nf : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} (e : Expr Γ T) → SN e →
        Σ[ e′ ∈ Expr Γ T ] ((e ⟶* e′) × Normal e′)
sn→nf e (acc f) with progress e
... | done nf         = (e , ⟶refl , nf)
... | step {e′ = e′} s with sn→nf e′ (f s)
...   | (e″ , p , nf) = (e″ , ⟶step s p , nf)

-- everything except SN is now in place:
canonicity-from-SN : (e : Expr ∅ 𝔹) → SN e → (e ⟶* true) ⊎ (e ⟶* false)
canonicity-from-SN e sn with sn→nf e sn
... | (e′ , p , nf) with canonical-forms e′ nf
...   | inj₁ refl = inj₁ p
...   | inj₂ refl = inj₂ p

-- ══════════════ §14  Context extension and renaming inversion ══════

ren⊆-refl : ∀ {Γ l}{A : Type ∅ l}(e : Expr Γ A) → ren⊆ ⊆-refl e ≡ e
ren⊆-refl e = Identityᵣᴿ e

ren⊆-trans : ∀ {Γ Γ′ Γ″ l}{A : Type ∅ l}(w : Γ ⊆ Γ′)(w′ : Γ′ ⊆ Γ″)(e : Expr Γ A) →
             ren⊆ w′ (ren⊆ w e) ≡ ren⊆ (⊆-trans w w′) e
ren⊆-trans w w′ e =
  trans (Compositionalityᴿᴿ e idᴿ idᴿ (⊆-ren w) (⊆-ren w′))
        (cong (idᴿ ∣ e [_]ᴿ)
              (fun-ext λ _ → fun-ext λ _ → fun-ext λ x → ⊆-var-trans w w′ x))

Ne-ren : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l}{T : Type Δ₁ l}{e : Expr Γ₁ T}
         (ζ : Ren Δ₁ Δ₂)(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) → Ne e → Ne (ζ ∣ e [ ρ ]ᴿ)
Ne-ren ζ ρ (ne-var x)     = ne-var _
Ne-ren ζ ρ (ne-app _ _)   = ne-app _ _
Ne-ren ζ ρ (ne-tapp _ _)  = ne-tapp _ _

-- inverting a reduction of a NEUTRAL application: no head redex, so the
-- step is in a subterm.  X is abstract, so matching β-λ refines it to a
-- λ and the Ne hypothesis discharges the case.
ne-app-inv : ∀ {Δ}{Γ : Ctx Δ}{l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}
             {X : Expr Γ (T₁ ⇒ T₂)}{a : Expr Γ T₁}{r : Expr Γ T₂} → Ne X → (X · a) ⟶ r →
             (Σ[ X′ ∈ Expr Γ (T₁ ⇒ T₂) ] ((X ⟶ X′) × (r ≡ X′ · a)))
             ⊎ (Σ[ a′ ∈ Expr Γ T₁ ] ((a ⟶ a′) × (r ≡ X · a′)))
ne-app-inv nu (ξ-·₁ s) = inj₁ (_ , s , refl)
ne-app-inv nu (ξ-·₂ s) = inj₂ (_ , s , refl)

ne-tapp-inv : ∀ {Δ}{Γ : Ctx Δ}{l l′}{T : Type (l ∙ Δ) l′}{X : Expr Γ (∀α T)}
              {S : Type Δ l}{r : Expr Γ (T [ S ]*)} → Ne X → (X ·* S) ⟶ r →
              Σ[ X′ ∈ Expr Γ (∀α T) ] ((X ⟶ X′) × (r ≡ X′ ·* S))
ne-tapp-inv nu (ξ-·* s) = (_ , s , refl)

-- β-lemmas for RENAMING, obtained from the substitution versions via Coincidence
⟪⟫-⇑ : ∀ {Δ₁ Δ₂}(ζ : Ren Δ₁ Δ₂){Γ₁ Γ₂}(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂){l}(T : Type Δ₁ l) →
           (⟨ ζ ⟩ ∣ (_ ∣⟪ ρ ⟫) ⇑ˢ T) ≡ (_ ∣⟪ (ζ ∣ ρ ⇑ᴿ T) ⟫)
⟪⟫-⇑ ζ ρ T = fun-ext λ _ → fun-ext λ _ → fun-ext λ { zero → refl ; (suc x) → refl }

⟪⟫-⇑* : ∀ {Δ₁ Δ₂}(ζ : Ren Δ₁ Δ₂){Γ₁ Γ₂}(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂){l} →
            (_∣_⇑ˢ* {l = l} ⟨ ζ ⟩ (_ ∣⟪ ρ ⟫)) ≡ (_ ∣⟪ (ζ ∣ ρ ↑ᴿ*) ⟫)
⟪⟫-⇑* ζ ρ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (suc* x) → refl }

β-λ-ren : ∀ {Δ₁ Δ₂}(ζ : Ren Δ₁ Δ₂){Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l₁ l₂}
          {T₁ : Type Δ₁ l₁}{T₂ : Type Δ₁ l₂}
          (e₁ : Expr (Γ₁ ▷ T₁) T₂)(e₂ : Expr Γ₁ T₁)(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
          ζ ∣ (e₁ [ e₂ ]) [ ρ ]ᴿ ≡ (ζ ∣ e₁ [ (ζ ∣ ρ ⇑ᴿ T₁) ]ᴿ) [ ζ ∣ e₂ [ ρ ]ᴿ ]
β-λ-ren ζ e₁ e₂ ρ =
  trans (sym (Coincidence (e₁ [ e₂ ]) ρ))
  (trans (β-λ-sub ⟨ ζ ⟩ e₁ e₂ (_ ∣⟪ ρ ⟫))
         (cong₂ (λ u v → u [ v ])
                (trans (cong (⟨ ζ ⟩ ∣ e₁ [_]ˢ) (⟪⟫-⇑ ζ ρ _))
                       (Coincidence e₁ (ζ ∣ ρ ⇑ᴿ _)))
                (Coincidence e₂ ρ)))

β-Λ-ren : ∀ {Δ₁ Δ₂}(ζ : Ren Δ₁ Δ₂){Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l l′}{T : Type (l ∙ Δ₁) l′}
          (e : Expr (Γ₁ ▷* l) T)(S : Type Δ₁ l)(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂) →
          ζ ∣ (e [* S *]) [ ρ ]ᴿ ≡ ((ζ ↑ᴿ) ∣ e [ (ζ ∣ ρ ↑ᴿ*) ]ᴿ) [* S [ ζ ]ᴿ *]
β-Λ-ren ζ e S ρ =
  trans (sym (Coincidence (e [* S *]) ρ))
  (trans (β-Λ-sub ⟨ ζ ⟩ e S (_ ∣⟪ ρ ⟫))
         (cong (_[* S [ ζ ]ᴿ *])
               (trans (cong ((⟨ ζ ⟩ ↑ˢ) ∣ e [_]ˢ) (⟪⟫-⇑* ζ ρ))
                      (Coincidence e (ζ ∣ ρ ↑ᴿ*)))))

-- A VIEW on expressions, split at a type VARIABLE.  Splitting the head of
-- an application directly is impossible: matching `_·*_` at type T₁ ⇒ T₂
-- needs T [ S ]* ≟ T₁ ⇒ T₂, which is stuck — the same computed-index
-- obstruction as everywhere else.  Here A is a metavariable, so it goes.
data LamView {Δ}{Γ : Ctx Δ} : ∀ {l}{A : Type Δ l} → Expr Γ A → Set where
  vlam : ∀ {l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}(b : Expr (Γ ▷ T₁) T₂) → LamView (λx b)
  vΛ   : ∀ {l l′}{T : Type (l ∙ Δ) l′}(b : Expr (Γ ▷* l) T) → LamView (Λα b)
  vne  : ∀ {l}{A : Type Δ l}{e : Expr Γ A} → Ne e → LamView e
  vtt  : LamView (true {Γ = Γ})
  vff  : LamView (false {Γ = Γ})

lamView : ∀ {Δ}{Γ : Ctx Δ}{l}{A : Type Δ l}(e : Expr Γ A) → LamView e
lamView (` x)    = vne (ne-var x)
lamView true     = vtt
lamView false    = vff
lamView (λx b)   = vlam b
lamView (Λα b)   = vΛ b
lamView (e · a)  = vne (ne-app e a)
lamView (e ·* S) = vne (ne-tapp e S)

-- REDUCTION INVERSION FOR RENAMING.  The two elimination cases go through
-- helpers taking the IHs explicitly: a `with` here would force Agda to
-- re-cover every clause inside the with-function.
ren-inv-· : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l₁ l₂}{T₁ : Type Δ₁ l₁}{T₂ : Type Δ₁ l₂}
            (ζ : Ren Δ₁ Δ₂)(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂)
            (e₁ : Expr Γ₁ (T₁ ⇒ T₂))(e₂ : Expr Γ₁ T₁) → LamView e₁ →
            (∀ {r} → (ζ ∣ e₁ [ ρ ]ᴿ) ⟶ r →
                     Σ[ u ∈ Expr Γ₁ (T₁ ⇒ T₂) ] ((e₁ ⟶ u) × (r ≡ ζ ∣ u [ ρ ]ᴿ))) →
            (∀ {r} → (ζ ∣ e₂ [ ρ ]ᴿ) ⟶ r →
                     Σ[ u ∈ Expr Γ₁ T₁ ] ((e₂ ⟶ u) × (r ≡ ζ ∣ u [ ρ ]ᴿ))) →
            ∀ {r} → (ζ ∣ (e₁ · e₂) [ ρ ]ᴿ) ⟶ r →
            Σ[ u ∈ Expr Γ₁ T₂ ] (((e₁ · e₂) ⟶ u) × (r ≡ ζ ∣ u [ ρ ]ᴿ))
ren-inv-· ζ ρ e₁ e₂ (vne nu) ih₁ ih₂ s with ne-app-inv (Ne-ren ζ ρ nu) s
... | inj₁ (X′ , sX , refl) with ih₁ sX
...   | (u , su , refl) = (u · e₂ , ξ-·₁ su , refl)
ren-inv-· ζ ρ e₁ e₂ (vne nu) ih₁ ih₂ s | inj₂ (a′ , sa , refl) with ih₂ sa
... | (u , su , refl) = (e₁ · u , ξ-·₂ su , refl)
ren-inv-· ζ ρ _ e₂ (vlam b) ih₁ ih₂ β-λ      = (b [ e₂ ] , β-λ , sym (β-λ-ren ζ b e₂ ρ))
ren-inv-· ζ ρ _ e₂ (vlam b) ih₁ ih₂ (ξ-·₁ s) with ih₁ s
... | (u , su , refl) = (u · e₂ , ξ-·₁ su , refl)
ren-inv-· ζ ρ _ e₂ (vlam b) ih₁ ih₂ (ξ-·₂ s) with ih₂ s
... | (u , su , refl) = ((λx b) · u , ξ-·₂ su , refl)

ren-inv-·* : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l l′}{T : Type (l ∙ Δ₁) l′}
             (ζ : Ren Δ₁ Δ₂)(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂)
             (e : Expr Γ₁ (∀α T))(S : Type Δ₁ l) → LamView e →
             (∀ {r} → (ζ ∣ e [ ρ ]ᴿ) ⟶ r →
                      Σ[ u ∈ Expr Γ₁ (∀α T) ] ((e ⟶ u) × (r ≡ ζ ∣ u [ ρ ]ᴿ))) →
             ∀ {r} → (ζ ∣ (e ·* S) [ ρ ]ᴿ) ⟶ r →
             Σ[ u ∈ Expr Γ₁ (T [ S ]*) ] (((e ·* S) ⟶ u) × (r ≡ ζ ∣ u [ ρ ]ᴿ))
ren-inv-·* ζ ρ e S (vne nu) ih s with ne-tapp-inv (Ne-ren ζ ρ nu) s
... | (X′ , sX , refl) with ih sX
...   | (u , su , refl) = (u ·* S , ξ-·* su , refl)
ren-inv-·* ζ ρ _ S (vΛ b) ih β-Λ       = (b [* S *] , β-Λ , sym (β-Λ-ren ζ b S ρ))
ren-inv-·* ζ ρ _ S (vΛ b) ih (ξ-·* s)  with ih s
... | (u , su , refl) = (u ·* S , ξ-·* su , refl)

⟶-ren-inv : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l}{T : Type Δ₁ l}
            (ζ : Ren Δ₁ Δ₂)(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂)(e : Expr Γ₁ T){r : Expr Γ₂ (T [ ζ ]ᴿ)} →
            (ζ ∣ e [ ρ ]ᴿ) ⟶ r →
            Σ[ u ∈ Expr Γ₁ T ] ((e ⟶ u) × (r ≡ ζ ∣ u [ ρ ]ᴿ))
⟶-ren-inv ζ ρ (` x)  ()
⟶-ren-inv ζ ρ true   ()
⟶-ren-inv ζ ρ false  ()
⟶-ren-inv ζ ρ (λx b) (ξ-λ s) with ⟶-ren-inv ζ (ζ ∣ ρ ⇑ᴿ _) b s
... | (u , su , refl) = (λx u , ξ-λ su , refl)
⟶-ren-inv ζ ρ (Λα b) (ξ-Λ s) with ⟶-ren-inv (ζ ↑ᴿ) (ζ ∣ ρ ↑ᴿ*) b s
... | (u , su , refl) = (Λα u , ξ-Λ su , refl)
⟶-ren-inv ζ ρ (e₁ · e₂) s =
  ren-inv-· ζ ρ e₁ e₂ (lamView e₁) (⟶-ren-inv ζ ρ e₁) (⟶-ren-inv ζ ρ e₂) s
⟶-ren-inv ζ ρ (e ·* S)  s =
  ren-inv-·* ζ ρ e S (lamView e) (⟶-ren-inv ζ ρ e) s

sn-ren : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l}{T : Type Δ₁ l}
         (ζ : Ren Δ₁ Δ₂)(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂){e : Expr Γ₁ T} → SN e → SN (ζ ∣ e [ ρ ]ᴿ)
sn-ren {Γ₁ = Γ₁} {T = T} ζ ρ {e} sn = acc (go e sn)
  where
  go : (e : Expr Γ₁ T) → SN e → ∀ {r} → (ζ ∣ e [ ρ ]ᴿ) ⟶ r → SN r
  go e (acc f) s with ⟶-ren-inv ζ ρ e s
  ... | (u , su , refl) = acc (go u (f su))

sn-ren⊆ : ∀ {Γ Γ′ l}{A : Type ∅ l}(w : Γ ⊆ Γ′){e : Expr Γ A} → SN e → SN (ren⊆ w e)
sn-ren⊆ w = sn-ren idᴿ (⊆-ren w)

-- ══════════════ §15  The logical relation is a candidate ═══════════
-- cr-exp stays NON-Kripke: sn-ren makes cr-wk provable, and then the
-- inj₁ branch below is discharged by h's own function component rather
-- than by a weakened induction hypothesis, so the inner recursion on
-- SN e′ stays structural.
⟦⟧-CR : ∀ {Δ l} (T : Type Δ l) {η : Sub Δ ∅} (ρ : Env Δ η) → CREnv ρ → CR (⟦ T ⟧ ρ)
⟦⟧-CR (base l) ρ c = record
  { cr-sn  = lower
  ; cr-fwd = λ p s → lift (sn-fwd (lower p) s)
  ; cr-exp = λ nu h → lift (acc (λ s → lower (h s)))
  ; cr-wk  = λ w p → lift (sn-ren⊆ w (lower p)) }
⟦⟧-CR (` here)      (P , ρ) (c , _)  = lower c
⟦⟧-CR (` (there α)) (_ , ρ) (_ , cs) = ⟦⟧-CR (` α) ρ cs
⟦⟧-CR (T₁ ⇒ T₂) {η} ρ c = record
  { cr-sn  = proj₁
  ; cr-fwd = λ { (sn , f) s →
      ( sn-fwd sn s
      , λ w e′ r → cr-fwd (⟦⟧-CR T₂ ρ c) (f w e′ r) (ξ-·₁ (⟶-ren idᴿ (⊆-ren w) s)) ) }
  ; cr-exp = λ { {e = e} nu h →
      ( acc (λ s → proj₁ (h s))
      , λ w e′ r → aux nu h w e′ r (cr-sn (⟦⟧-CR T₁ ρ c) r) ) }
  ; cr-wk  = λ { {e = e} w (sn , f) →
      ( sn-ren⊆ w sn
      , λ w′ e′ r → subst (λ z → ⟦ T₂ ⟧ ρ _ (z · e′))
                          (sym (ren⊆-trans w w′ e)) (f (⊆-trans w w′) e′ r) ) }
  }
  where
  aux : ∀ {Γ : Ctx ∅} {e : Expr Γ ((T₁ ⇒ T₂) [ η ]ˢ)} → Ne e →
        (∀ {e″} → e ⟶ e″ → ⟦ T₁ ⇒ T₂ ⟧ ρ Γ e″) →
        ∀ {Γ′} (w : Γ ⊆ Γ′) (e′ : Expr Γ′ (T₁ [ η ]ˢ)) →
        ⟦ T₁ ⟧ ρ Γ′ e′ → SN e′ → ⟦ T₂ ⟧ ρ Γ′ (ren⊆ w e · e′)
  aux {e = e} nu h w e′ r (acc g) = cr-exp (⟦⟧-CR T₂ ρ c) (ne-app _ _) hyp
    where
    hyp : ∀ {r′} → (ren⊆ w e · e′) ⟶ r′ → ⟦ T₂ ⟧ ρ _ r′
    hyp s with ne-app-inv (Ne-ren idᴿ (⊆-ren w) nu) s
    ... | inj₁ (X′ , sX , refl) with ⟶-ren-inv idᴿ (⊆-ren w) e sX
    ...   | (u , su , refl) = proj₂ (h su) w e′ r
    hyp s | inj₂ (a′ , sa , refl) =
      aux nu h w a′ (cr-fwd (⟦⟧-CR T₁ ρ c) r sa) (g sa)
⟦⟧-CR (∀α_ {l = l} T) {η} ρ c = record
  { cr-sn  = proj₁
  ; cr-fwd = λ { (sn , f) s →
      ( sn-fwd sn s
      , λ w S P cp → cr-fwd (⟦⟧-CR T (P , ρ) (lift cp , c))
                            (f w S P cp) (ξ-·* (⟶-ren idᴿ (⊆-ren w) s)) ) }
  ; cr-exp = λ { {e = e} nu h →
      ( acc (λ s → proj₁ (h s))
      , λ w S P cp → cr-exp (⟦⟧-CR T (P , ρ) (lift cp , c)) (ne-tapp _ _) (hyp nu h w S P cp) ) }
  ; cr-wk  = λ { {e = e} w (sn , f) →
      ( sn-ren⊆ w sn
      , λ w′ S P cp → subst (λ z → ⟦ T ⟧ {S ∙ˢ η} (P , ρ) _ (z ·* S))
                            (sym (ren⊆-trans w w′ e)) (f (⊆-trans w w′) S P cp) ) }
  }
  where
  hyp : ∀ {Γ : Ctx ∅} {e : Expr Γ ((∀α T) [ η ]ˢ)} → Ne e →
        (∀ {e″} → e ⟶ e″ → ⟦ ∀α T ⟧ ρ Γ e″) →
        ∀ {Γ′} (w : Γ ⊆ Γ′) (S : Type ∅ l) (P : Pred S) (cp : CR P) →
        ∀ {r′} → (ren⊆ w e ·* S) ⟶ r′ → ⟦ T ⟧ {S ∙ˢ η} (P , ρ) Γ′ r′
  hyp {e = e} nu h w S P cp s with ne-tapp-inv (Ne-ren idᴿ (⊆-ren w) nu) s
  ... | (X′ , sX , refl) with ⟶-ren-inv idᴿ (⊆-ren w) e sX
  ...   | (u , su , refl) = proj₂ (h su) w S P cp

-- ══════════════ §16  β-expansion ═══════════════════════════════════

⟶*-ren : ∀ {Δ₁ Δ₂}{Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l}{T : Type Δ₁ l}
         (ζ : Ren Δ₁ Δ₂)(ρ : ζ ∣ Γ₁ ⇒ᴿ Γ₂){e e′ : Expr Γ₁ T} →
         e ⟶* e′ → (ζ ∣ e [ ρ ]ᴿ) ⟶* (ζ ∣ e′ [ ρ ]ᴿ)
⟶*-ren ζ ρ ⟶refl       = ⟶refl
⟶*-ren ζ ρ (⟶step s p) = ⟶step (⟶-ren ζ ρ s) (⟶*-ren ζ ρ p)

-- pointwise ⟶* between substitutions (η explicit: not inferable from
-- σ's type, which unfolds to a Π)
Redsˢ : ∀ {Δ₁ Δ₂}(η : Sub Δ₁ Δ₂){Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}(σ σ′ : η ∣ Γ₁ ⇒ˢ Γ₂) → Set
Redsˢ {Δ₁ = Δ₁} η σ σ′ = ∀ l (T : Type Δ₁ l) x → σ l T x ⟶* σ′ l T x

⇑ˢ-cong : ∀ {Δ₁ Δ₂}(η : Sub Δ₁ Δ₂){Γ₁ Γ₂}(σ σ′ : η ∣ Γ₁ ⇒ˢ Γ₂) → Redsˢ η σ σ′ →
             ∀ {l}(A : Type Δ₁ l) → Redsˢ η (η ∣ σ ⇑ˢ A) (η ∣ σ′ ⇑ˢ A)
⇑ˢ-cong η σ σ′ p A _ _ zero    = ⟶refl
⇑ˢ-cong η σ σ′ p A _ _ (suc x) = ⟶*-ren idᴿ (Wkᴿ _) (p _ _ x)

⇑ˢ*-cong : ∀ {Δ₁ Δ₂}(η : Sub Δ₁ Δ₂){Γ₁ Γ₂}(σ σ′ : η ∣ Γ₁ ⇒ˢ Γ₂) → Redsˢ η σ σ′ →
              ∀ {l} → Redsˢ (η ↑ˢ) (_∣_⇑ˢ* {l = l} η σ) (η ∣ σ′ ⇑ˢ*)
⇑ˢ*-cong η σ σ′ p _ _ (suc* x) = ⟶*-ren wkᴿ wkᴿ* (p _ _ x)

⟶*-λ : ∀ {Δ}{Γ : Ctx Δ}{l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}{e e′ : Expr (Γ ▷ T₁) T₂} →
       e ⟶* e′ → (λx e) ⟶* (λx e′)
⟶*-λ ⟶refl       = ⟶refl
⟶*-λ (⟶step s p) = ⟶step (ξ-λ s) (⟶*-λ p)

⟶*-Λ : ∀ {Δ}{Γ : Ctx Δ}{l l′}{T : Type (l ∙ Δ) l′}{e e′ : Expr (Γ ▷* l) T} →
       e ⟶* e′ → (Λα e) ⟶* (Λα e′)
⟶*-Λ ⟶refl       = ⟶refl
⟶*-Λ (⟶step s p) = ⟶step (ξ-Λ s) (⟶*-Λ p)

⟶*-·* : ∀ {Δ}{Γ : Ctx Δ}{l l′}{T : Type (l ∙ Δ) l′}{e e′ : Expr Γ (∀α T)}{S : Type Δ l} →
        e ⟶* e′ → (e ·* S) ⟶* (e′ ·* S)
⟶*-·* ⟶refl       = ⟶refl
⟶*-·* (⟶step s p) = ⟶step (ξ-·* s) (⟶*-·* p)

sub-cong : ∀ {Δ₁ Δ₂}(η : Sub Δ₁ Δ₂){Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}
           (σ σ′ : η ∣ Γ₁ ⇒ˢ Γ₂) → Redsˢ η σ σ′ →
           ∀ {l}{T : Type Δ₁ l}(e : Expr Γ₁ T) → (η ∣ e [ σ ]ˢ) ⟶* (η ∣ e [ σ′ ]ˢ)
sub-cong η σ σ′ p (` x)     = p _ _ x
sub-cong η σ σ′ p true      = ⟶refl
sub-cong η σ σ′ p false     = ⟶refl
sub-cong η σ σ′ p (λx b)    =
  ⟶*-λ (sub-cong η (η ∣ σ ⇑ˢ _) (η ∣ σ′ ⇑ˢ _) (⇑ˢ-cong η σ σ′ p _) b)
sub-cong η σ σ′ p (Λα b)    =
  ⟶*-Λ (sub-cong (η ↑ˢ) (η ∣ σ ⇑ˢ*) (η ∣ σ′ ⇑ˢ*) (⇑ˢ*-cong η σ σ′ p) b)
sub-cong η σ σ′ p (e₁ · e₂) =
  ⟶*-trans (⟶*-· (sub-cong η σ σ′ p e₁)) (⟶*-·₂ (sub-cong η σ σ′ p e₂))
sub-cong η σ σ′ p (e ·* S)  = ⟶*-·* (sub-cong η σ σ′ p e)

-- reducing the argument of a single substitution
sub-⟶* : ∀ {Δ}{Γ : Ctx Δ}{l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}
         (b : Expr (Γ ▷ T₁) T₂){a a′ : Expr Γ T₁} → a ⟶ a′ → (b [ a ]) ⟶* (b [ a′ ])
sub-⟶* b {a} {a′} s =
  sub-cong idˢ (idˢ ∣ a ∙ˢ Idˢ) (idˢ ∣ a′ ∙ˢ Idˢ)
           (λ { _ _ zero → ⟶step s ⟶refl ; _ _ (suc x) → ⟶refl }) b

-- substituting into a lifted substitution = extending it
lift-cons-sub : ∀ {Δ₁ Δ₂}(η : Sub Δ₁ Δ₂){Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l₁ l₂}
                {T₁ : Type Δ₁ l₁}{T₂ : Type Δ₁ l₂}
                (e : Expr (Γ₁ ▷ T₁) T₂)(σ : η ∣ Γ₁ ⇒ˢ Γ₂)(a : Expr Γ₂ (T₁ [ η ]ˢ)) →
                (η ∣ e [ (η ∣ σ ⇑ˢ T₁) ]ˢ) [ a ] ≡ η ∣ e [ (η ∣ a ∙ˢ σ) ]ˢ
lift-cons-sub η e σ a =
  trans (Compositionalityˢˢ e η idˢ (η ∣ σ ⇑ˢ _) (idˢ ∣ a ∙ˢ Idˢ))
        (cong (η ∣ e [_]ˢ) (fun-ext λ _ → fun-ext λ _ → fun-ext λ
          { zero    → refl
          ; (suc x) → trans (Compositionalityᴿˢ (σ _ _ x) idᴿ idˢ (Wkᴿ _) (idˢ ∣ a ∙ˢ Idˢ))
                            (Identityᵣ (σ _ _ x)) }))

lift*-cons-sub : ∀ {Δ₁ Δ₂}(η : Sub Δ₁ Δ₂){Γ₁ : Ctx Δ₁}{Γ₂ : Ctx Δ₂}{l l′}
                 {T : Type (l ∙ Δ₁) l′}
                 (e : Expr (Γ₁ ▷* l) T)(σ : η ∣ Γ₁ ⇒ˢ Γ₂)(S : Type Δ₂ l) →
                 ((η ↑ˢ) ∣ e [ (η ∣ σ ⇑ˢ*) ]ˢ) [* S *] ≡ (S ∙ˢ η) ∣ e [ (η ∣ S ∙ˢ* σ) ]ˢ
lift*-cons-sub η e σ S =
  trans (Compositionalityˢˢ e (η ↑ˢ) (S ∙ˢ idˢ) (η ∣ σ ⇑ˢ*) (idˢ ∣ S ∙ˢ* Idˢ))
        (cong ((S ∙ˢ η) ∣ e [_]ˢ) (fun-ext λ _ → fun-ext λ _ → fun-ext λ
          { (suc* x) → trans (Compositionalityᴿˢ (σ _ _ x) wkᴿ (S ∙ˢ idˢ) wkᴿ*
                                (idˢ ∣ S ∙ˢ* Idˢ))
                             (Identityᵣ (σ _ _ x)) }))

-- β-EXPANSION
⟦⟧-β-λ : ∀ {Δ l₁ l₂}(T₁ : Type Δ l₁)(T₂ : Type Δ l₂){η : Sub Δ ∅}
         (ρ : Env Δ η)(c : CREnv ρ){Γ : Ctx ∅}
         (b : Expr (Γ ▷ (T₁ [ η ]ˢ)) (T₂ [ η ]ˢ))(a : Expr Γ (T₁ [ η ]ˢ)) →
         SN b → SN a → ⟦ T₂ ⟧ ρ Γ (b [ a ]) → ⟦ T₂ ⟧ ρ Γ ((λx b) · a)
⟦⟧-β-λ T₁ T₂ ρ c b a (acc fb) (acc fa) h =
  cr-exp (⟦⟧-CR T₂ ρ c) (ne-app _ _) hyp
  where
  hyp : ∀ {r} → ((λx b) · a) ⟶ r → ⟦ T₂ ⟧ ρ _ r
  hyp β-λ            = h
  hyp (ξ-·₁ (ξ-λ s)) =
    ⟦⟧-β-λ T₁ T₂ ρ c _ a (fb s) (acc fa)
           (cr-fwd (⟦⟧-CR T₂ ρ c) h (⟶-sub idˢ (idˢ ∣ a ∙ˢ Idˢ) s))
  hyp (ξ-·₂ s)       =
    ⟦⟧-β-λ T₁ T₂ ρ c b _ (acc fb) (fa s)
           (cr-fwd* (⟦⟧-CR T₂ ρ c) h (sub-⟶* b s))

⟦⟧-β-Λ : ∀ {Δ l l′}(T : Type (l ∙ Δ) l′){η : Sub Δ ∅}
         (ρ : Env Δ η)(c : CREnv ρ)(S : Type ∅ l)(P : Pred S)(cp : CR P){Γ : Ctx ∅}
         (b : Expr (Γ ▷* l) (T [ η ↑ˢ ]ˢ)) →
         SN b → ⟦ T ⟧ {S ∙ˢ η} (P , ρ) Γ (b [* S *]) →
         ⟦ T ⟧ {S ∙ˢ η} (P , ρ) Γ ((Λα b) ·* S)
⟦⟧-β-Λ T {η} ρ c S P cp b (acc fb) h =
  cr-exp (⟦⟧-CR T (P , ρ) (lift cp , c)) (ne-tapp _ _) hyp
  where
  hyp : ∀ {r} → ((Λα b) ·* S) ⟶ r → ⟦ T ⟧ {S ∙ˢ η} (P , ρ) _ r
  hyp β-Λ             = h
  hyp (ξ-·* (ξ-Λ s))  =
    ⟦⟧-β-Λ T ρ c S P cp _ (fb s)
           (cr-fwd (⟦⟧-CR T (P , ρ) (lift cp , c)) h
                   (⟶-sub (S ∙ˢ idˢ) (idˢ ∣ S ∙ˢ* Idˢ) s))

-- ══════════════ §17  Reducible substitutions ═══════════════════════
-- Defined by recursion on Γ: a ∀-quantification over the level of each
-- variable's type would live in Setω.
maxC : ∀ {Δ} → Ctx Δ → Level
maxC ∅                  = lzero
maxC (_▷_ {l = l} Γ T)  = l ⊔ maxC Γ
maxC (Γ ▷* l)           = maxC Γ

Reds : ∀ {Δ}(Γ : Ctx Δ){η : Sub Δ ∅}(ρ : Env Δ η){Γ′ : Ctx ∅}(σ : η ∣ Γ ⇒ˢ Γ′) →
       Set (maxC Γ)
Reds ∅         ρ σ = ⊤
Reds (Γ ▷ T)   ρ {Γ′} σ = ⟦ T ⟧ ρ Γ′ (σ _ _ zero) × Reds Γ ρ (λ l A x → σ l A (suc x))
Reds (Γ ▷* l)  ρ σ = Reds Γ (proj₂ ρ) (λ l₀ A x → σ l₀ (weaken A) (suc* x))

-- weakening a type variable out of the interpretation
⟦⟧-weaken : ∀ {Δ l l′}(T : Type Δ l′)(η : Sub (l ∙ Δ) ∅)(ρ : Env (l ∙ Δ) η) →
            ⟦ weaken T ⟧ ρ ≡ ⟦ T ⟧ (proj₂ ρ)
⟦⟧-weaken T η ρ =
  trans (⟦⟧-ren T wkᴿ η ρ) (cong (⟦ T ⟧ {⟨ wkᴿ ⟩ ⨟ˢ η}) (⊛-wk₀ η ρ))

Reds-var : ∀ {Δ}{Γ : Ctx Δ}{η : Sub Δ ∅}(ρ : Env Δ η){Γ′ : Ctx ∅}
           (σ : η ∣ Γ ⇒ˢ Γ′) → Reds Γ ρ σ →
           ∀ {l}{T : Type Δ l}(x : Γ ∋ T) → ⟦ T ⟧ ρ Γ′ (σ _ _ x)
Reds-var ρ σ rs zero      = proj₁ rs
Reds-var ρ σ rs (suc x)   = Reds-var ρ (λ l A y → σ l A (suc y)) (proj₂ rs) x
Reds-var {η = η} ρ σ rs (suc* {T = T} x) =
  subst (λ Q → Q _ (σ _ _ (suc* x))) (sym (⟦⟧-weaken T η ρ))
        (Reds-var (proj₂ ρ) (λ l₀ A y → σ l₀ (weaken A) (suc* y)) rs x)

Reds-wk : ∀ {Δ}(Γ : Ctx Δ){η : Sub Δ ∅}(ρ : Env Δ η)(c : CREnv ρ){Γ′ Γ″ : Ctx ∅}
          (σ : η ∣ Γ ⇒ˢ Γ′)(w : Γ′ ⊆ Γ″) → Reds Γ ρ σ →
          Reds Γ ρ (λ l A x → ren⊆ w (σ l A x))
Reds-wk ∅        ρ c σ w rs = tt
Reds-wk (Γ ▷ T)  ρ c σ w rs =
  (cr-wk (⟦⟧-CR T ρ c) w (proj₁ rs) , Reds-wk Γ ρ c (λ l A x → σ l A (suc x)) w (proj₂ rs))
Reds-wk (Γ ▷* l) ρ c σ w rs =
  Reds-wk Γ (proj₂ ρ) (proj₂ c) (λ l₀ A x → σ l₀ (weaken A) (suc* x)) w rs

-- ══════════════ §18  The fundamental theorem ═══════════════════════

-- renaming a lifted substitution and then extending it
ren-lift-cons : ∀ {Δ}(η : Sub Δ ∅){Γ : Ctx Δ}{Γ′ Γ″ : Ctx ∅}{l₁ l₂}
                {T₁ : Type Δ l₁}{T₂ : Type Δ l₂}
                (b : Expr (Γ ▷ T₁) T₂)(σ : η ∣ Γ ⇒ˢ Γ′)(w : Γ′ ⊆ Γ″)
                (a : Expr Γ″ (T₁ [ η ]ˢ)) →
                (idᴿ ∣ (η ∣ b [ (η ∣ σ ⇑ˢ T₁) ]ˢ) [ (idᴿ ∣ (⊆-ren w) ⇑ᴿ (T₁ [ η ]ˢ)) ]ᴿ) [ a ]
                ≡ η ∣ b [ (η ∣ a ∙ˢ (λ l A x → ren⊆ w (σ l A x))) ]ˢ
ren-lift-cons η b σ w a =
  trans (cong (_[ a ]) (Compositionalityˢᴿ b η idᴿ (η ∣ σ ⇑ˢ _) (idᴿ ∣ (⊆-ren w) ⇑ᴿ _)))
  (trans (Compositionalityˢˢ b η idˢ _ (idˢ ∣ a ∙ˢ Idˢ))
         (cong (η ∣ b [_]ˢ) (fun-ext λ _ → fun-ext λ _ → fun-ext λ
           { zero    → refl
           ; (suc x) →
               trans (cong (λ z → idˢ ∣ z [ (idˢ ∣ a ∙ˢ Idˢ) ]ˢ)
                           (trans (Coincidence (idᴿ ∣ (σ _ _ x) [ Wkᴿ _ ]ᴿ) (idᴿ ∣ (⊆-ren w) ⇑ᴿ _))
                                  (Compositionalityᴿᴿ (σ _ _ x) idᴿ idᴿ (Wkᴿ _) (idᴿ ∣ (⊆-ren w) ⇑ᴿ _))))
               (trans (Compositionalityᴿˢ (σ _ _ x) idᴿ idˢ _ (idˢ ∣ a ∙ˢ Idˢ))
               (trans (cong (⟨ idᴿ ⟩ ∣ (σ _ _ x) [_]ˢ)
                            (fun-ext λ _ → fun-ext λ _ → fun-ext λ y → refl))
                      (Coincidence (σ _ _ x) (⊆-ren w)))) })))

ren-lift*-cons : ∀ {Δ}(η : Sub Δ ∅){Γ : Ctx Δ}{Γ′ Γ″ : Ctx ∅}{l l′}
                 {T : Type (l ∙ Δ) l′}
                 (b : Expr (Γ ▷* l) T)(σ : η ∣ Γ ⇒ˢ Γ′)(w : Γ′ ⊆ Γ″)(S : Type ∅ l) →
                 (idᴿ ∣ ((η ↑ˢ) ∣ b [ (η ∣ σ ⇑ˢ*) ]ˢ) [ (idᴿ ∣ (⊆-ren w) ↑ᴿ*) ]ᴿ) [* S *]
                 ≡ (S ∙ˢ η) ∣ b [ (η ∣ S ∙ˢ* (λ l₀ A x → ren⊆ w (σ l₀ A x))) ]ˢ
ren-lift*-cons η b σ w S =
  trans (cong (_[* S *]) (Compositionalityˢᴿ b (η ↑ˢ) idᴿ (η ∣ σ ⇑ˢ*) (idᴿ ∣ (⊆-ren w) ↑ᴿ*)))
  (trans (Compositionalityˢˢ b (η ↑ˢ) (S ∙ˢ idˢ) _ (idˢ ∣ S ∙ˢ* Idˢ))
         (cong ((S ∙ˢ η) ∣ b [_]ˢ) (fun-ext λ _ → fun-ext λ _ → fun-ext λ
           { (suc* x) →
               trans (cong (λ z → (S ∙ˢ idˢ) ∣ z [ (idˢ ∣ S ∙ˢ* Idˢ) ]ˢ)
                           (trans (Coincidence (wkᴿ ∣ (σ _ _ x) [ wkᴿ* ]ᴿ) (idᴿ ∣ (⊆-ren w) ↑ᴿ*))
                                  (Compositionalityᴿᴿ (σ _ _ x) wkᴿ (idᴿ ↑ᴿ) wkᴿ* (idᴿ ∣ (⊆-ren w) ↑ᴿ*))))
               (trans (Compositionalityᴿˢ (σ _ _ x) _ (S ∙ˢ idˢ) _ (idˢ ∣ S ∙ˢ* Idˢ))
               (trans (cong (⟨ idᴿ ⟩ ∣ (σ _ _ x) [_]ˢ)
                            (fun-ext λ _ → fun-ext λ _ → fun-ext λ y → refl))
                      (Coincidence (σ _ _ x) (⊆-ren w)))) })))

--! Fundamental {
fundamental : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l}(e : Expr Γ T)
              {η : Sub Δ ∅}(ρ : Env Δ η)(c : CREnv ρ)
              {Γ′ : Ctx ∅}(σ : η ∣ Γ ⇒ˢ Γ′) → Reds Γ ρ σ → ⟦ T ⟧ ρ Γ′ (η ∣ e [ σ ]ˢ)
--! }
fundamental (` x)  ρ c σ rs = Reds-var ρ σ rs x
fundamental true   ρ c σ rs = lift (acc λ ())
fundamental false  ρ c σ rs = lift (acc λ ())
fundamental (_·_ {T₂ = T₂} e₁ e₂) {η} ρ c σ rs =
  subst (λ z → ⟦ T₂ ⟧ ρ _ (z · (η ∣ e₂ [ σ ]ˢ))) (ren⊆-refl (η ∣ e₁ [ σ ]ˢ))
        (proj₂ (fundamental e₁ ρ c σ rs) ⊆-refl _ (fundamental e₂ ρ c σ rs))
fundamental (_·*_ {T = T} e S) {η} ρ c σ rs =
  subst (λ Q → Q _ ((η ∣ e [ σ ]ˢ) ·* (S [ η ]ˢ))) (sym (⟦⟧-[]* T S η ρ))
        (subst (λ z → ⟦ T ⟧ {(S [ η ]ˢ) ∙ˢ η} (⟦ S ⟧ ρ , ρ) _ (z ·* (S [ η ]ˢ)))
               (ren⊆-refl (η ∣ e [ σ ]ˢ))
               (proj₂ (fundamental e ρ c σ rs) ⊆-refl (S [ η ]ˢ) (⟦ S ⟧ ρ) (⟦⟧-CR S ρ c)))
fundamental (λx {T₁ = T₁} {T₂ = T₂} b) {η} ρ c {Γ′} σ rs =
  ( sn-λ (cr-sn (⟦⟧-CR T₂ ρ c) (fundamental b ρ c (η ∣ σ ⇑ˢ T₁) rsLift))
  , λ w e′ r →
      ⟦⟧-β-λ T₁ T₂ ρ c _ e′
             (sn-ren idᴿ (idᴿ ∣ (⊆-ren w) ⇑ᴿ _)
                     (cr-sn (⟦⟧-CR T₂ ρ c) (fundamental b ρ c (η ∣ σ ⇑ˢ T₁) rsLift)))
             (cr-sn (⟦⟧-CR T₁ ρ c) r)
             (subst (λ z → ⟦ T₂ ⟧ ρ _ z) (sym (ren-lift-cons η b σ w e′))
                    (fundamental b ρ c (η ∣ e′ ∙ˢ (λ l A x → ren⊆ w (σ l A x)))
                                 (r , Reds-wk _ ρ c σ w rs))) )
  where
  rsLift : Reds (_ ▷ T₁) ρ (η ∣ σ ⇑ˢ T₁)
  rsLift = ( cr-exp (⟦⟧-CR T₁ ρ c) (ne-var zero) (λ ())
           , Reds-wk _ ρ c σ (⊆-▷ ⊆-refl) rs )
fundamental (Λα {l = l} {T = T} b) {η} ρ c {Γ′} σ rs =
  ( sn-Λ snBody
  , λ w S P cp →
      ⟦⟧-β-Λ T ρ c S P cp _
             (sn-ren idᴿ (idᴿ ∣ (⊆-ren w) ↑ᴿ*) snBody)
             (subst (λ z → ⟦ T ⟧ {S ∙ˢ η} (P , ρ) _ z)
                    (sym (ren-lift*-cons η b σ w S))
                    (fundamental b (P , ρ) (lift cp , c)
                                 (η ∣ S ∙ˢ* (λ l₀ A x → ren⊆ w (σ l₀ A x)))
                                 (Reds-wk _ ρ c σ w rs))) )
  where
  P₀ : Pred (base l)
  P₀ = λ _ e → Lift l (SN e)
  cp₀ : CR P₀
  cp₀ = record { cr-sn = lower ; cr-fwd = λ p s → lift (sn-fwd (lower p) s)
               ; cr-exp = λ nu h → lift (acc (λ s → lower (h s)))
               ; cr-wk  = λ w p → lift (sn-ren⊆ w (lower p)) }
  ih₀ = fundamental b (P₀ , ρ) (lift cp₀ , c) (η ∣ (base l) ∙ˢ* σ) rs
  snBody : SN ((η ↑ˢ) ∣ b [ (η ∣ σ ⇑ˢ*) ]ˢ)
  snBody = sn-sub ((base l) ∙ˢ idˢ) (idˢ ∣ (base l) ∙ˢ* Idˢ)
             (subst SN (sym (lift*-cons-sub η b σ (base l)))
                    (cr-sn (⟦⟧-CR T (P₀ , ρ) (lift cp₀ , c)) ih₀))

-- ══════════════ §19  CANONICITY ════════════════════════════════════

ρ∅ : Env ∅ idˢ
ρ∅ = tt

-- STRONG NORMALIZATION for every closed term, at every type
--! SNall {
SN-all : ∀ {l}{T : Type ∅ l}(e : Expr ∅ T) → SN e
--! }
SN-all {T = T} e =
  sn-sub idˢ Idˢ (cr-sn (⟦⟧-CR T ρ∅ tt) (fundamental e ρ∅ tt Idˢ tt))

-- CANONICITY: every closed term of base type reduces to true or false
--! Canonicity {
canonicity : (e : Expr ∅ 𝔹) → (e ⟶* true) ⊎ (e ⟶* false)
--! }
canonicity e = canonicity-from-SN e (SN-all e)
