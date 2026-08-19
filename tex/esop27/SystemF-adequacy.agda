{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════
-- SAFFRICH / THIEMANN / WEIDNER's ADEQUACY PROOF, REBUILT ON THE
-- REWRITE-BASED σ-CALCULUS OF SystemF-strat.agda.
--
-- Reference: Hannes Saffrich, Peter Thiemann, Marius Weidner,
--   "Intrinsically Typed Syntax, a Logical Relation, and the Scourge of
--   the Transfer Lemma", TyDe'24, doi:10.1145/3678000.3678201.
--   Artifact: https://github.com/proglang/SystemF, src/StratF/.
--
-- This file reproduces THEIR construction, not a parametricity variant:
--   * big-step CBV `_⇓_` landing in `CValue`      (their StratF.BigStep)
--   * denotational semantics `⟦_⟧ᵀ`, `E⟦_⟧`       (their StratF.Types,
--                                                  StratF.Expressions)
--   * `REL {l} T = CValue T → ⟦ T ⟧ [] → Set l`   (their LogicalPrelim)
--   * `𝓥⟦_⟧`, `𝓔⟦_⟧`, `𝓖⟦_⟧`                     (their StratF.Logical)
--   * `semantic-soundness` / `fundamental`         (their Fundamental)
--   * `adequacy`                                   (their Fundamental)
--
-- Each section banner below names the module of their artifact that it
-- corresponds to, and every transport of theirs that disappears here is
-- flagged at the point where it would have occurred.
--
-- DECLARED DEVIATIONS (each is flagged again at the point of use):
--   (D1) Their `𝓥⟦ T ⟧ ρ` relates `CValue (Tsub (π₁ ρ) T)` to
--        `⟦ T ⟧ (⟦ π₁ ρ ⟧* [])` — substitution pushed into the SEMANTIC
--        ENVIRONMENT.  We relate `CValue (T [ η ]ˢ)` to `⟦ T [ η ]ˢ ⟧ᵀ []`
--        — substitution pushed into the TYPE.  The two are connected by
--        their own `Tsub-preserves-semantics`, proved here as `⟦⟧ᵀ-sub`.
--        We choose the substituted-type form because it is the form the
--        σ-rewrites normalise, which is what makes `𝓥⟦⟧-ren`/`𝓥⟦⟧-sub`
--        (their LRVren/LRVsub) transport-free IN THE STATEMENT.
--        The price is exactly one `subst id` in the statement of
--        `semantic-soundness`; see §A8.
--   (D2) Their base type is `ℕ` with `# n`/`suc`; strat's is `base l`
--        at every level, inhabited at level 0 by `true`/`false`.  So
--        `⟦ base l ⟧ᵀ η = Lift l Bool` and adequacy is stated for
--        booleans rather than numerals.  This is a difference in the
--        object language, not in the proof technique.
--   (D3) Their relation environment `𝓓⟦ Δ ⟧ = ∀ l → l ∈ Δ → Σ (Type [] l) REL`
--        lives in `Setω`.  Ours is a level-computing recursive function
--        into `Set (maxL Δ)` with the `Σ`'s first component pulled out
--        into an index — exactly `SystemF-strat`'s `Env` with `Pred`
--        replaced by `REL`.  This is a `Setω`-avoidance choice inherited
--        from strat, independent of the substitution infrastructure.
--   (D4) Their base case of the value relation reads "u is the literal
--        denoting z"; `base l` is inhabited only at level 0, so that
--        cannot be written uniformly in l.  We use the extensionally
--        equivalent "u's denotation is z"; see §A5, and §A9 for how the
--        literal is recovered.
--   (D5) Their value environment `Env Δ Γ η` lives in `Setω`.  Ours is
--        defined by recursion on Γ into `Set (maxC Γ)`, so it is an
--        ordinary `Set`; see §A4.
--
-- The only postulate is `fun-ext`, inherited from SystemF-strat.
-- ════════════════════════════════════════════════════════════════════
module SystemF-adequacy where

open import Agda.Builtin.Equality.Rewrite public
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
-- `[_]` (Reveal) hidden: it clashes with strat's `_[_]`
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
-- Bool's `true`/`false` are renamed: strat's `Expr` constructors of the
-- same name are the SYNTACTIC booleans, these are the semantic ones.
open import Data.Bool using (Bool) renaming (true to tt𝔹; false to ff𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Level using (Lift; lift; lower)
open import Function using (id; _∘_)

-- `fundamental` is hidden: strat's unary-logical-relation fundamental
-- theorem is unrelated to STW's, and this file re-uses THEIR name.
open import SystemF-strat hiding (fundamental)

-- NOTE: SystemF-strat's `variable` block (l, Δ, T, Γ, e, ζ, η, …) is
-- in scope through the import; only the new ones are declared here.

-- ══════════════ §A1  Values and big-step CBV  (their BigStep.agda) ═══
-- Their `Evaluation.agda` and `BigStep.agda`.
-- Strat has FULL β-reduction, so this semantics is added here, exactly
-- mirroring their `isValue`/`CValue`/`_⇓_`/`Value-⇓`.  Their `Eval`
-- record (an interface shared with the small-step development) is
-- omitted: we only instantiate it once.

--! CExpr
CExpr : ∀ {l} → Type ∅ l → Set
CExpr T = Expr ∅ T

--! isValue
data isValue {Δ}{Γ : Ctx Δ} : ∀ {l}{T : Type Δ l} → Expr Γ T → Set where
  V-true  : isValue (true {Γ = Γ})
  V-false : isValue (false {Γ = Γ})
  V-ƛ     : ∀ {l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}{e : Expr (Γ ▷ T₁) T₂} →
            isValue (λx e)
  V-Λ     : ∀ {l l′}{T : Type (l ∙ Δ) l′}{e : Expr (Γ ▷* l) T} → isValue (Λα e)

--! Value
record CValue {l} (T : Type ∅ l) : Set where
  constructor _,_
  field  exp : CExpr T
         prf : isValue exp
open CValue public

variable v v₂ : CValue T

infix 15 _⇓_
--! Semantics
data _⇓_ : ∀ {l}{T : Type ∅ l} → CExpr T → CValue T → Set where
  ⇓-true  : true ⇓ (true , V-true)
  ⇓-false : false ⇓ (false , V-false)
  ⇓-ƛ     : ∀ {l₁ l₂}{T₁ : Type ∅ l₁}{T₂ : Type ∅ l₂}{e : Expr (∅ ▷ T₁) T₂} →
            (λx e) ⇓ (λx e , V-ƛ)
  ⇓-·     : ∀ {l₁ l₂}{T₁ : Type ∅ l₁}{T₂ : Type ∅ l₂}
            {e₁ : CExpr (T₁ ⇒ T₂)}{e₂ : CExpr T₁}{e : Expr (∅ ▷ T₁) T₂}
            {v₂ : CValue T₁}{v : CValue T₂} →
            e₁ ⇓ (λx e , V-ƛ) → e₂ ⇓ v₂ → (e [ exp v₂ ]) ⇓ v → (e₁ · e₂) ⇓ v
  ⇓-Λ     : ∀ {l l′}{T : Type (l ∙ ∅) l′}{e : Expr (∅ ▷* l) T} →
            (Λα e) ⇓ (Λα e , V-Λ)
  ⇓-∙     : ∀ {l l′}{T : Type (l ∙ ∅) l′}{e₁ : CExpr (∀α T)}{e : Expr (∅ ▷* l) T}
            {T′ : Type ∅ l}{v : CValue (T [ T′ ]*)} →
            e₁ ⇓ (Λα e , V-Λ) → (e [* T′ *]) ⇓ v → (e₁ ·* T′) ⇓ v

--! ValueReduceSelf
Value-⇓ : ∀ {l}{T : Type ∅ l} → (v : CValue T) → exp v ⇓ v
Value-⇓ (.true ,   V-true)   = ⇓-true
Value-⇓ (.false ,  V-false)  = ⇓-false
Value-⇓ (.(λx _) , V-ƛ)      = ⇓-ƛ
Value-⇓ (.(Λα _) , V-Λ)      = ⇓-Λ

-- ══════════════ §A2  Denotational semantics of types ═══════════════
-- Their StratF/Types.agda, `Env*` and `⟦_⟧`.  Copied verbatim modulo
-- the base type (D2).  `Env*` is a `Setω` datatype exactly as theirs:
-- this is the one place where `Setω` is unavoidable and we do not try
-- to avoid it.

--! TEnv
data Env* : LCtx → Setω where
  []   : Env* ∅
  _∷_  : ∀ {l Δ} → Set l → Env* Δ → Env* (l ∙ Δ)

lookupᵀ : ∀ {Δ l} → Δ ∋ˡ l → Env* Δ → Set l
lookupᵀ here      (A ∷ _) = A
lookupᵀ (there α) (_ ∷ η) = lookupᵀ α η

--! TSem
⟦_⟧ᵀ : ∀ {Δ l} → Type Δ l → Env* Δ → Set l
⟦ base l ⟧ᵀ    η = Lift l Bool
⟦ T₁ ⇒ T₂ ⟧ᵀ   η = ⟦ T₁ ⟧ᵀ η → ⟦ T₂ ⟧ᵀ η
⟦ ` α ⟧ᵀ       η = lookupᵀ α η
⟦ ∀α_ {l = l} T ⟧ᵀ η = (A : Set l) → ⟦ T ⟧ᵀ (A ∷ η)

-- ══════════════ §A3  Semantic type substitution ════════════════════
-- Their StratF/TypeSubstPropertiesSem.agda: `Ren*`,
-- `Tren*-preserves-semantics`, `Tsub*-preserves-semantics`,
-- `Tsingle-subst-preserves`.  Mirrored with the same pointwise-relation
-- technique, which is what keeps `Setω` equality out of the picture.
--
-- NOTE: this section is NOT helped by the rewrite system.  `⟦_⟧ᵀ` is a
-- semantic function; the σ-calculus says nothing about it.  These are
-- genuine inductions and they are the irreducible core of the
-- denotational side.

-- NOTE ON EXPLICIT ARGUMENTS.  `Ren*ᵀ ζ η₁ η₂` unfolds to a Π-type, so
-- ζ, η₁, η₂ are NOT recoverable by unification from a term of that type.
-- Every lemma below therefore takes them explicitly.  STW hit exactly
-- the same obstruction and write `{ρ* = τ*} {η₁} {η₂}` by hand at every
-- call site (e.g. inside the statement of `LRVren-eq′` itself).
Ren*ᵀ : ∀ {Δ₁ Δ₂} → Ren Δ₁ Δ₂ → Env* Δ₁ → Env* Δ₂ → Setω
Ren*ᵀ {Δ₁} ζ η₁ η₂ = ∀ {l} (α : Δ₁ ∋ˡ l) → lookupᵀ (α &ᴿ ζ) η₂ ≡ lookupᵀ α η₁

Sub*ᵀ : ∀ {Δ₁ Δ₂} → Sub Δ₁ Δ₂ → Env* Δ₁ → Env* Δ₂ → Setω
Sub*ᵀ {Δ₁} σ η₁ η₂ = ∀ {l} (α : Δ₁ ∋ˡ l) → ⟦ α &ˢ σ ⟧ᵀ η₂ ≡ lookupᵀ α η₁

-- lifting a renaming preserves the relation
Ren*ᵀ-lift : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂)
             {l} (A : Set l) → Ren*ᵀ ζ η₁ η₂ → Ren*ᵀ (ζ ↑ᴿ) (A ∷ η₁) (A ∷ η₂)
Ren*ᵀ-lift ζ η₁ η₂ A r here      = refl
Ren*ᵀ-lift ζ η₁ η₂ A r (there α) = r α

Ren*ᵀ-wk : ∀ {Δ} (η : Env* Δ) {l} (A : Set l) → Ren*ᵀ (wkᴿ {l = l}) η (A ∷ η)
Ren*ᵀ-wk η A α = refl

--! TrenPreservesSemantics
⟦⟧ᵀ-ren : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) →
          Ren*ᵀ ζ η₁ η₂ → ∀ {l} (T : Type Δ₁ l) → ⟦ T [ ζ ]ᴿ ⟧ᵀ η₂ ≡ ⟦ T ⟧ᵀ η₁
⟦⟧ᵀ-ren ζ η₁ η₂ r (base l)  = refl
⟦⟧ᵀ-ren ζ η₁ η₂ r (` α)     = r α
⟦⟧ᵀ-ren ζ η₁ η₂ r (T₁ ⇒ T₂) =
  cong₂ (λ A B → A → B) (⟦⟧ᵀ-ren ζ η₁ η₂ r T₁) (⟦⟧ᵀ-ren ζ η₁ η₂ r T₂)
⟦⟧ᵀ-ren ζ η₁ η₂ r (∀α_ {l = l} T) =
  cong (λ f → (A : Set l) → f A)
       (fun-ext λ A → ⟦⟧ᵀ-ren (ζ ↑ᴿ) (A ∷ η₁) (A ∷ η₂) (Ren*ᵀ-lift ζ η₁ η₂ A r) T)

-- lifting a substitution preserves the relation
Sub*ᵀ-lift : ∀ {Δ₁ Δ₂} (σ : Sub Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂)
             {l} (A : Set l) → Sub*ᵀ σ η₁ η₂ → Sub*ᵀ (σ ↑ˢ) (A ∷ η₁) (A ∷ η₂)
Sub*ᵀ-lift σ η₁ η₂ A s here      = refl
Sub*ᵀ-lift σ η₁ η₂ A s (there α) =
  trans (⟦⟧ᵀ-ren wkᴿ η₂ (A ∷ η₂) (Ren*ᵀ-wk η₂ A) (α &ˢ σ)) (s α)

--! TsubPreservesSemantics
⟦⟧ᵀ-sub : ∀ {Δ₁ Δ₂} (σ : Sub Δ₁ Δ₂) (η₁ : Env* Δ₁) (η₂ : Env* Δ₂) →
          Sub*ᵀ σ η₁ η₂ → ∀ {l} (T : Type Δ₁ l) → ⟦ T [ σ ]ˢ ⟧ᵀ η₂ ≡ ⟦ T ⟧ᵀ η₁
⟦⟧ᵀ-sub σ η₁ η₂ s (base l)  = refl
⟦⟧ᵀ-sub σ η₁ η₂ s (` α)     = s α
⟦⟧ᵀ-sub σ η₁ η₂ s (T₁ ⇒ T₂) =
  cong₂ (λ A B → A → B) (⟦⟧ᵀ-sub σ η₁ η₂ s T₁) (⟦⟧ᵀ-sub σ η₁ η₂ s T₂)
⟦⟧ᵀ-sub σ η₁ η₂ s (∀α_ {l = l} T) =
  cong (λ f → (A : Set l) → f A)
       (fun-ext λ A → ⟦⟧ᵀ-sub (σ ↑ˢ) (A ∷ η₁) (A ∷ η₂) (Sub*ᵀ-lift σ η₁ η₂ A s) T)

-- the semantic environment realised by a CLOSING type substitution:
-- their `⟦ σ* ⟧* []` / `subst-to-env*`
envOf : ∀ {Δ} → Sub Δ ∅ → Env* Δ
envOf {∅}     σ = []
envOf {l ∙ Δ} σ = ⟦ here &ˢ σ ⟧ᵀ [] ∷ envOf (⟨ wkᴿ ⟩ ⨟ˢ σ)

-- their `subst-var-preserves`.  Definitional at every step: the index
-- `α &ˢ (⟨ wkᴿ ⟩ ⨟ˢ σ) ≡ (there α) &ˢ σ` is a registered σ-rewrite.
envOf-lookup : ∀ {Δ l} (α : Δ ∋ˡ l) (σ : Sub Δ ∅) →
               ⟦ α &ˢ σ ⟧ᵀ [] ≡ lookupᵀ α (envOf σ)
envOf-lookup here      σ = refl
envOf-lookup (there α) σ = envOf-lookup α (⟨ wkᴿ ⟩ ⨟ˢ σ)

Sub*ᵀ-envOf : ∀ {Δ} (σ : Sub Δ ∅) → Sub*ᵀ σ (envOf σ) []
Sub*ᵀ-envOf σ α = envOf-lookup α σ

--! TsubPreservesSemanticsClosed
⟦⟧ᵀ-closing : ∀ {Δ l} (σ : Sub Δ ∅) (T : Type Δ l) →
              ⟦ T [ σ ]ˢ ⟧ᵀ [] ≡ ⟦ T ⟧ᵀ (envOf σ)
⟦⟧ᵀ-closing σ T = ⟦⟧ᵀ-sub σ (envOf σ) [] (Sub*ᵀ-envOf σ) T

-- their `Tsingle-subst-preserves`: the instance the ∀-clause of the
-- logical relation and the `·*`-clause of `E⟦_⟧` both need.
⟦⟧ᵀ-single : ∀ {Δ l l′} (η : Env* Δ) (T′ : Type Δ l) (T : Type (l ∙ Δ) l′) →
             ⟦ T [ T′ ]* ⟧ᵀ η ≡ ⟦ T ⟧ᵀ (⟦ T′ ⟧ᵀ η ∷ η)
⟦⟧ᵀ-single η T′ T = ⟦⟧ᵀ-sub (T′ ∙ˢ idˢ) (⟦ T′ ⟧ᵀ η ∷ η) η aux T
  where
  aux : Sub*ᵀ (T′ ∙ˢ idˢ) (⟦ T′ ⟧ᵀ η ∷ η) η
  aux here      = refl
  aux (there α) = refl

-- ══════════════ §A4  Value environments and `E⟦_⟧` ═════════════════
-- Their StratF/Expressions.agda, `Env`, `extend`, `extend-tskip`, `E⟦_⟧`.

--! VEnv
-- DEVIATION (D5).  Theirs is `Env Δ Γ η = ∀ l (T : Type Δ l) → inn T Γ → ⟦ T ⟧ η`,
-- which lives in `Setω` because it quantifies over `l : Level`.  That is
-- what forces their `Setω` equality library (`≡ω`, `fun-extω`, `congωl`,
-- `transω`, …) and their postulate `relenv-ext`.  We define it instead by
-- RECURSION ON Γ into `Set (maxC Γ)` — SystemF-strat's `Reds` trick — so
-- it is an ordinary `Set` and plain `subst`/`cong` apply to it.
--
-- Three of their lemmas evaporate as a direct consequence:
--   * `extend-tskip`   becomes the IDENTITY (see `E⟦ Λα e ⟧` below);
--   * `Gdrop-t`        becomes the IDENTITY (`envOf` at `l ∙ Δ` already
--                      exposes the tail definitionally);
--   * `Gdrop-t-ext≡id` (stated with `≡ω` in their LRVren.agda) is `refl`.
-- This is a `Setω`-handling difference, NOT a substitution-infrastructure
-- difference.
Envᵥ : ∀ {Δ} (Γ : Ctx Δ) → Env* Δ → Set (maxC Γ)
Envᵥ ∅        η        = ⊤
Envᵥ (Γ ▷ T)  η        = ⟦ T ⟧ᵀ η × Envᵥ Γ η
Envᵥ (Γ ▷* l) (A ∷ η)  = Envᵥ Γ η

--! ExtendTskip
-- their `extend-tskip` / `Gdrop-t`, now only needed at a VARIABLE.  The
-- `subst id` is forced by `weaken T = T [ wkᴿ ]ᴿ` and is a SEMANTIC
-- transport (`⟦⟧ᵀ-ren`); the σ-calculus cannot remove it.
lookupᵥ : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} (x : Γ ∋ T) (η : Env* Δ) →
          Envᵥ Γ η → ⟦ T ⟧ᵀ η
lookupᵥ zero              η       γ = proj₁ γ
lookupᵥ (suc x)           η       γ = lookupᵥ x η (proj₂ γ)
lookupᵥ (suc* {T = T} x)  (A ∷ η) γ =
  subst id (sym (⟦⟧ᵀ-ren wkᴿ η (A ∷ η) (Ren*ᵀ-wk η A) T)) (lookupᵥ x η γ)

--! ExprSem
E⟦_⟧ : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} →
       Expr Γ T → (η : Env* Δ) → Envᵥ Γ η → ⟦ T ⟧ᵀ η
E⟦ ` x ⟧      η γ = lookupᵥ x η γ
E⟦ true ⟧     η γ = lift tt𝔹
E⟦ false ⟧    η γ = lift ff𝔹
E⟦ λx e ⟧     η γ = λ z → E⟦ e ⟧ η (z , γ)
E⟦ e₁ · e₂ ⟧  η γ = E⟦ e₁ ⟧ η γ (E⟦ e₂ ⟧ η γ)
E⟦ Λα e ⟧     η γ = λ A → E⟦ e ⟧ (A ∷ η) γ
E⟦ _·*_ {T = T} e T′ ⟧ η γ =
  subst id (sym (⟦⟧ᵀ-single η T′ T)) (E⟦ e ⟧ η γ (⟦ T′ ⟧ᵀ η))

-- ══════════════ §A5  THE LOGICAL RELATION  (their Logical.agda) ════
-- their `REL`, verbatim
--! REL
REL : ∀ {l} → Type ∅ l → Set (lsuc l)
REL {l} T = CValue T → ⟦ T ⟧ᵀ [] → Set l

-- their `𝓓⟦ Δ ⟧ = ∀ l → l ∈ Δ → Σ (Type [] l) REL`, with the Σ's first
-- component pulled out into an INDEX (deviation D3).  This is literally
-- SystemF-strat's `Env` with `Pred` replaced by `REL`; the index is what
-- makes all the composition bookkeeping below definitional.
--! RelEnv
𝓓⟦_⟧ : (Δ : LCtx) → Sub Δ ∅ → Set (maxL Δ)
𝓓⟦ ∅ ⟧     η = ⊤
𝓓⟦ l ∙ Δ ⟧ η = REL (here &ˢ η) × 𝓓⟦ Δ ⟧ (⟨ wkᴿ ⟩ ⨟ˢ η)

-- their `π₂`.  Their `π₁` is our index η, so it has no counterpart here:
-- that is the point of the indexing discipline.
--! piTwo
π₂ : ∀ {Δ l} (α : Δ ∋ˡ l) (η : Sub Δ ∅) → 𝓓⟦ Δ ⟧ η → REL (α &ˢ η)
π₂ here      η (R , _) = R
π₂ (there α) η (_ , ρ) = π₂ α (⟨ wkᴿ ⟩ ⨟ˢ η) ρ

-- the empty value environment, used by the base clause
γ∅ : Envᵥ ∅ []
γ∅ = tt

--! MCVType
𝓥⟦_⟧ : ∀ {Δ l} (T : Type Δ l) {η : Sub Δ ∅} → 𝓓⟦ Δ ⟧ η → REL (T [ η ]ˢ)
𝓔⟦_⟧ : ∀ {Δ l} (T : Type Δ l) {η : Sub Δ ∅} → 𝓓⟦ Δ ⟧ η →
       CExpr (T [ η ]ˢ) → ⟦ T [ η ]ˢ ⟧ᵀ [] → Set l

--! MCVBody
-- BASE.  Theirs is `∃[ n ] (exp u ≡ # n) ∧ (n ≡ z)`.  Strat's `base l`
-- exists at every level but is inhabited only at level 0 (by `true` and
-- `false`), so "u is a literal denoting z" cannot be written uniformly
-- in l.  We use the extensionally equivalent "u's denotation is z"
-- (deviation D4); at `𝔹` the two agree, and §A9 recovers the literal.
𝓥⟦ base l ⟧ ρ u z = Lift l (E⟦ exp u ⟧ [] γ∅ ≡ z)
-- ARROW.  Mirrors theirs exactly.
𝓥⟦ _⇒_ {l₁ = l₁} {l₂ = l₂} T₁ T₂ ⟧ {η} ρ u f =
  Σ[ e ∈ Expr (∅ ▷ (T₁ [ η ]ˢ)) (T₂ [ η ]ˢ) ] ((exp u ≡ λx e) ×
    (∀ (w : CValue (T₁ [ η ]ˢ)) (z : ⟦ T₁ [ η ]ˢ ⟧ᵀ []) →
       𝓥⟦ T₁ ⟧ ρ w z → 𝓔⟦ T₂ ⟧ ρ (e [ exp w ]) (f z)))
-- TYPE VARIABLE.  Theirs is
--   `π₂ ρ _ α v (subst id (subst-var-preserves α (π₁ ρ) []) z)`.
-- The `subst` is GONE: `(` α) [ η ]ˢ` is `α &ˢ η` by a registered
-- σ-rewrite, so the two sides are definitionally equal.
𝓥⟦ ` α ⟧ {η} ρ v z = π₂ α η ρ v z
-- ∀.  Theirs is
--   `… 𝓥⟦ T ⟧ (REext ρ (T′ , R)) (subst CValue (RE-ext∘lift ρ T T′ R) v) (F (⟦ T′ ⟧ []))`.
-- The `subst CValue (RE-ext∘lift …)` — their `lemma1`, the transfer
-- lemma of the title — is GONE: `(T [ η ↑ˢ ]ˢ) [ T′ ]* ≡ T [ T′ ∙ˢ η ]ˢ`
-- is definitional, and `(R , ρ) : 𝓓⟦ l ∙ Δ ⟧ (T′ ∙ˢ η)` needs no coercion.
-- What REMAINS is a transport on the DENOTATION (`⟦⟧ᵀ-single`, their
-- `Tsingle-subst-preserves`), which is a fact about `⟦_⟧ᵀ` and which the
-- σ-calculus cannot touch.
𝓥⟦ ∀α_ {l = l} T ⟧ {η} ρ u F =
  Σ[ e ∈ Expr (∅ ▷* l) (T [ η ↑ˢ ]ˢ) ] ((exp u ≡ Λα e) ×
    (∀ (T′ : Type ∅ l) (R : REL T′) →
       Σ[ v ∈ CValue (T [ T′ ∙ˢ η ]ˢ) ] (((e [* T′ *]) ⇓ v) ×
         𝓥⟦ T ⟧ {T′ ∙ˢ η} (R , ρ) v
           (subst id (sym (⟦⟧ᵀ-single [] T′ (T [ η ↑ˢ ]ˢ))) (F (⟦ T′ ⟧ᵀ []))))))

--! MCE
𝓔⟦ T ⟧ {η} ρ e z = Σ[ v ∈ CValue (T [ η ]ˢ) ] ((e ⇓ v) × 𝓥⟦ T ⟧ ρ v z)

-- ══════════════ §A6  THE RELATION AND TYPE SUBSTITUTION ════════════
-- This is where the comparison with their development is sharpest.
-- Their StratF/LRVren.agda and StratF/LRVsub.agda state:
--
--   LRVren-eq′ …  𝓥⟦ T ⟧ (Tren-act τ* ρ) v z ≡ S (𝓥⟦ Tren τ* T ⟧ ρ) v z
--     where S = subst₂ (λ vv zz → Value vv → zz → Set l)
--                      (fusion-Tsub-Tren T τ* ρ*)                  -- SYNTACTIC
--                      (Tren*-preserves-semantics … T)             -- SEMANTIC
--
--   LRVsub …      𝓥⟦ T ⟧ (Tsub-act τ* ρ) v z
--                 ≡ 𝓥⟦ Tsub τ* T ⟧ ρ (subst Value (sym (fusion-Tsub-Tsub …)) v)
--                                    (subst id (sym (… congωl …)) z)
--
-- Below, BOTH statements are plain `_≡_` between two applications of
-- `𝓥⟦_⟧`, with NO transport of any kind, because the index equations
--   (T [ ζ ]ᴿ) [ η ]ˢ ≡ T [ ⟨ ζ ⟩ ⨟ˢ η ]ˢ      (their fusion-Tsub-Tren)
--   (T [ σ ]ˢ) [ κ ]ˢ ≡ T [ σ  ⨟ˢ κ ]ˢ         (their fusion-Tsub-Tsub)
-- are registered σ-rewrites, hence definitional, and because the
-- denotation side is `⟦ T [ … ]ˢ ⟧ᵀ []` rather than `⟦ T ⟧ᵀ (envOf …)`
-- (deviation D1), so the semantic half of their `subst₂` is definitional
-- too.  These are exact mirrors of SystemF-strat's `⟦⟧-ren`/`⟦⟧-sub`.

⊛𝓓 : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (η : Sub Δ₂ ∅) → 𝓓⟦ Δ₂ ⟧ η → 𝓓⟦ Δ₁ ⟧ (⟨ ζ ⟩ ⨟ˢ η)
⊛𝓓 {∅}      ζ η ρ = tt
⊛𝓓 {l ∙ Δ₁} ζ η ρ = π₂ (here &ᴿ ζ) η ρ , ⊛𝓓 (wkᴿ ⨟ᴿ ζ) η ρ

π₂-⊛𝓓 : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (ζ : Ren Δ₁ Δ₂) (η : Sub Δ₂ ∅) (ρ : 𝓓⟦ Δ₂ ⟧ η) →
         π₂ α (⟨ ζ ⟩ ⨟ˢ η) (⊛𝓓 ζ η ρ) ≡ π₂ (α &ᴿ ζ) η ρ
π₂-⊛𝓓 here      ζ η ρ = refl
π₂-⊛𝓓 (there α) ζ η ρ = π₂-⊛𝓓 α (wkᴿ ⨟ᴿ ζ) η ρ

⊛𝓓-wk : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (η : Sub (l ∙ Δ₂) ∅) (ρ : 𝓓⟦ l ∙ Δ₂ ⟧ η) →
        ⊛𝓓 (ζ ⨟ᴿ wkᴿ) η ρ ≡ ⊛𝓓 ζ (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ)
⊛𝓓-wk {Δ₁ = ∅}      ζ η ρ = refl
⊛𝓓-wk {Δ₁ = l ∙ Δ₁} ζ η ρ =
  cong (π₂ (here &ᴿ ζ) (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ) ,_) (⊛𝓓-wk (wkᴿ ⨟ᴿ ζ) η ρ)

⊛𝓓-wk₀ : ∀ {Δ l} (η : Sub (l ∙ Δ) ∅) (ρ : 𝓓⟦ l ∙ Δ ⟧ η) → ⊛𝓓 wkᴿ η ρ ≡ proj₂ ρ
⊛𝓓-wk₀ {Δ = ∅}     η ρ = refl
⊛𝓓-wk₀ {Δ = l ∙ Δ} η ρ =
  cong (π₂ here (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ) ,_)
       (trans (⊛𝓓-wk wkᴿ η ρ) (⊛𝓓-wk₀ (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ)))

⊛𝓓-lift : ∀ {Δ₁ Δ₂ l} (ζ : Ren Δ₁ Δ₂) (η : Sub (l ∙ Δ₂) ∅) (ρ : 𝓓⟦ l ∙ Δ₂ ⟧ η) →
          ⊛𝓓 (ζ ↑ᴿ) η ρ ≡ (proj₁ ρ , ⊛𝓓 ζ (⟨ wkᴿ ⟩ ⨟ˢ η) (proj₂ ρ))
⊛𝓓-lift ζ η ρ = cong (proj₁ ρ ,_) (⊛𝓓-wk ζ η ρ)

-- their LRVren-eq / LRVren-eq′ — note: NO subst₂, no transport
--! LRVren
𝓥⟦⟧-ren : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (ζ : Ren Δ₁ Δ₂) (η : Sub Δ₂ ∅) (ρ : 𝓓⟦ Δ₂ ⟧ η) →
          𝓥⟦ T [ ζ ]ᴿ ⟧ ρ ≡ 𝓥⟦ T ⟧ (⊛𝓓 ζ η ρ)
𝓥⟦⟧-ren (base l)  ζ η ρ = refl
𝓥⟦⟧-ren (` α)     ζ η ρ = sym (π₂-⊛𝓓 α ζ η ρ)
𝓥⟦⟧-ren (_⇒_ {l₁ = l₁} {l₂ = l₂} T₁ T₂) ζ η ρ =
  fun-ext λ u → fun-ext λ f →
    cong₂ (λ P Q → Σ[ e ∈ Expr (∅ ▷ (T₁ [ ⟨ ζ ⟩ ⨟ˢ η ]ˢ)) (T₂ [ ⟨ ζ ⟩ ⨟ˢ η ]ˢ) ]
                     ((exp u ≡ λx e) ×
                      (∀ w z → P w z →
                         Σ[ v ∈ CValue (T₂ [ ⟨ ζ ⟩ ⨟ˢ η ]ˢ) ]
                           (((e [ exp w ]) ⇓ v) × Q v (f z)))))
          (𝓥⟦⟧-ren T₁ ζ η ρ) (𝓥⟦⟧-ren T₂ ζ η ρ)
𝓥⟦⟧-ren (∀α_ {l = l} T) ζ η ρ =
  fun-ext λ u → fun-ext λ F →
    cong (λ g → Σ[ e ∈ Expr (∅ ▷* l) (T [ (⟨ ζ ⟩ ⨟ˢ η) ↑ˢ ]ˢ) ]
                  ((exp u ≡ Λα e) ×
                   (∀ (T′ : Type ∅ l) (R : REL T′) →
                      Σ[ v ∈ CValue (T [ T′ ∙ˢ (⟨ ζ ⟩ ⨟ˢ η) ]ˢ) ]
                        (((e [* T′ *]) ⇓ v) ×
                         g T′ R v (subst id (sym (⟦⟧ᵀ-single [] T′ (T [ (⟨ ζ ⟩ ⨟ˢ η) ↑ˢ ]ˢ)))
                                             (F (⟦ T′ ⟧ᵀ [])))))))
         (fun-ext λ T′ → fun-ext λ R → ∀step T′ R)
  where
  ∀step : ∀ (T′ : Type ∅ l) (R : REL T′) →
          𝓥⟦ T [ ζ ↑ᴿ ]ᴿ ⟧ {T′ ∙ˢ η} (R , ρ)
        ≡ 𝓥⟦ T ⟧ {T′ ∙ˢ (⟨ ζ ⟩ ⨟ˢ η)} (R , ⊛𝓓 ζ η ρ)
  ∀step T′ R = trans (𝓥⟦⟧-ren T (ζ ↑ᴿ) (T′ ∙ˢ η) (R , ρ))
                     (cong (𝓥⟦ T ⟧ {T′ ∙ˢ (⟨ ζ ⟩ ⨟ˢ η)}) (⊛𝓓-lift ζ (T′ ∙ˢ η) (R , ρ)))

-- ── substitutions ──

⊙𝓓 : ∀ {Δ₁ Δ₂} (σ : Sub Δ₁ Δ₂) (κ : Sub Δ₂ ∅) → 𝓓⟦ Δ₂ ⟧ κ → 𝓓⟦ Δ₁ ⟧ (σ ⨟ˢ κ)
⊙𝓓 {∅}      σ κ ρ = tt
⊙𝓓 {l ∙ Δ₁} σ κ ρ = 𝓥⟦ here &ˢ σ ⟧ {κ} ρ , ⊙𝓓 (⟨ wkᴿ ⟩ ⨟ˢ σ) κ ρ

π₂-⊙𝓓 : ∀ {Δ₁ Δ₂ l} (α : Δ₁ ∋ˡ l) (σ : Sub Δ₁ Δ₂) (κ : Sub Δ₂ ∅) (ρ : 𝓓⟦ Δ₂ ⟧ κ) →
         π₂ α (σ ⨟ˢ κ) (⊙𝓓 σ κ ρ) ≡ 𝓥⟦ α &ˢ σ ⟧ {κ} ρ
π₂-⊙𝓓 here      σ κ ρ = refl
π₂-⊙𝓓 (there α) σ κ ρ = π₂-⊙𝓓 α (⟨ wkᴿ ⟩ ⨟ˢ σ) κ ρ

⊙𝓓-⟨⟩ : ∀ {Δ₁ Δ₂} (ζ : Ren Δ₁ Δ₂) (κ : Sub Δ₂ ∅) (ρ : 𝓓⟦ Δ₂ ⟧ κ) →
        ⊙𝓓 ⟨ ζ ⟩ κ ρ ≡ ⊛𝓓 ζ κ ρ
⊙𝓓-⟨⟩ {Δ₁ = ∅}      ζ κ ρ = refl
⊙𝓓-⟨⟩ {Δ₁ = l ∙ Δ₁} ζ κ ρ =
  cong (π₂ (here &ᴿ ζ) κ ρ ,_) (⊙𝓓-⟨⟩ (wkᴿ ⨟ᴿ ζ) κ ρ)

⊙𝓓-wk : ∀ {Δ₁ Δ₂ l} (σ : Sub Δ₁ Δ₂) (κ : Sub (l ∙ Δ₂) ∅) (ρ : 𝓓⟦ l ∙ Δ₂ ⟧ κ) →
        ⊙𝓓 (σ ⨟ˢ ⟨ wkᴿ ⟩) κ ρ ≡ ⊙𝓓 σ (⟨ wkᴿ ⟩ ⨟ˢ κ) (proj₂ ρ)
⊙𝓓-wk {Δ₁ = ∅}      σ κ ρ = refl
⊙𝓓-wk {Δ₁ = l ∙ Δ₁} σ κ ρ =
  cong₂ _,_
    (trans (𝓥⟦⟧-ren (here &ˢ σ) wkᴿ κ ρ)
           (cong (𝓥⟦ here &ˢ σ ⟧ {⟨ wkᴿ ⟩ ⨟ˢ κ}) (⊛𝓓-wk₀ κ ρ)))
    (⊙𝓓-wk (⟨ wkᴿ ⟩ ⨟ˢ σ) κ ρ)

⊙𝓓-lift : ∀ {Δ₁ Δ₂ l} (σ : Sub Δ₁ Δ₂) (κ : Sub (l ∙ Δ₂) ∅) (ρ : 𝓓⟦ l ∙ Δ₂ ⟧ κ) →
          ⊙𝓓 (σ ↑ˢ) κ ρ ≡ (proj₁ ρ , ⊙𝓓 σ (⟨ wkᴿ ⟩ ⨟ˢ κ) (proj₂ ρ))
⊙𝓓-lift σ κ ρ = cong (proj₁ ρ ,_) (⊙𝓓-wk σ κ ρ)

⊙𝓓-id : ∀ {Δ} (κ : Sub Δ ∅) (ρ : 𝓓⟦ Δ ⟧ κ) → ⊙𝓓 idˢ κ ρ ≡ ρ
⊙𝓓-id {∅}     κ ρ = refl
⊙𝓓-id {l ∙ Δ} κ ρ =
  cong (π₂ here κ ρ ,_) (trans (⊙𝓓-⟨⟩ wkᴿ κ ρ) (⊛𝓓-wk₀ κ ρ))

-- their LRVsub — note: NO subst, no `congωl`, no inlined
--! LRVsub
--            equational-reasoning chain in the statement)
𝓥⟦⟧-sub : ∀ {Δ₁ Δ₂ l} (T : Type Δ₁ l) (σ : Sub Δ₁ Δ₂) (κ : Sub Δ₂ ∅) (ρ : 𝓓⟦ Δ₂ ⟧ κ) →
          𝓥⟦ T [ σ ]ˢ ⟧ {κ} ρ ≡ 𝓥⟦ T ⟧ (⊙𝓓 σ κ ρ)
𝓥⟦⟧-sub (base l)  σ κ ρ = refl
𝓥⟦⟧-sub (` α)     σ κ ρ = sym (π₂-⊙𝓓 α σ κ ρ)
𝓥⟦⟧-sub (_⇒_ {l₁ = l₁} {l₂ = l₂} T₁ T₂) σ κ ρ =
  fun-ext λ u → fun-ext λ f →
    cong₂ (λ P Q → Σ[ e ∈ Expr (∅ ▷ (T₁ [ σ ⨟ˢ κ ]ˢ)) (T₂ [ σ ⨟ˢ κ ]ˢ) ]
                     ((exp u ≡ λx e) ×
                      (∀ w z → P w z →
                         Σ[ v ∈ CValue (T₂ [ σ ⨟ˢ κ ]ˢ) ]
                           (((e [ exp w ]) ⇓ v) × Q v (f z)))))
          (𝓥⟦⟧-sub T₁ σ κ ρ) (𝓥⟦⟧-sub T₂ σ κ ρ)
𝓥⟦⟧-sub (∀α_ {l = l} T) σ κ ρ =
  fun-ext λ u → fun-ext λ F →
    cong (λ g → Σ[ e ∈ Expr (∅ ▷* l) (T [ (σ ⨟ˢ κ) ↑ˢ ]ˢ) ]
                  ((exp u ≡ Λα e) ×
                   (∀ (T′ : Type ∅ l) (R : REL T′) →
                      Σ[ v ∈ CValue (T [ T′ ∙ˢ (σ ⨟ˢ κ) ]ˢ) ]
                        (((e [* T′ *]) ⇓ v) ×
                         g T′ R v (subst id (sym (⟦⟧ᵀ-single [] T′ (T [ (σ ⨟ˢ κ) ↑ˢ ]ˢ)))
                                             (F (⟦ T′ ⟧ᵀ [])))))))
         (fun-ext λ T′ → fun-ext λ R → ∀stepˢ T′ R)
  where
  ∀stepˢ : ∀ (T′ : Type ∅ l) (R : REL T′) →
           𝓥⟦ T [ σ ↑ˢ ]ˢ ⟧ {T′ ∙ˢ κ} (R , ρ)
         ≡ 𝓥⟦ T ⟧ {T′ ∙ˢ (σ ⨟ˢ κ)} (R , ⊙𝓓 σ κ ρ)
  ∀stepˢ T′ R = trans (𝓥⟦⟧-sub T (σ ↑ˢ) (T′ ∙ˢ κ) (R , ρ))
                      (cong (𝓥⟦ T ⟧ {T′ ∙ˢ (σ ⨟ˢ κ)}) (⊙𝓓-lift σ (T′ ∙ˢ κ) (R , ρ)))

-- the single-variable instance (their `LRVsub` at `Textₛ Tidₛ T′`)
𝓥⟦⟧-[]* : ∀ {Δ l l′} (T : Type (l ∙ Δ) l′) (T′ : Type Δ l) (κ : Sub Δ ∅) (ρ : 𝓓⟦ Δ ⟧ κ) →
          𝓥⟦ T [ T′ ]* ⟧ {κ} ρ ≡ 𝓥⟦ T ⟧ {(T′ [ κ ]ˢ) ∙ˢ κ} (𝓥⟦ T′ ⟧ {κ} ρ , ρ)
𝓥⟦⟧-[]* T T′ κ ρ =
  trans (𝓥⟦⟧-sub T (T′ ∙ˢ idˢ) κ ρ)
        (cong (𝓥⟦ T ⟧ {(T′ [ κ ]ˢ) ∙ˢ κ}) (cong (𝓥⟦ T′ ⟧ {κ} ρ ,_) (⊙𝓓-id κ ρ)))

-- their `LRVwk-eq` (whose statement carries TWO substs, `S₁` and `S₂`).
-- Ours carries none, for the same reason.
𝓥⟦⟧-weaken : ∀ {Δ l l′} (T : Type Δ l′) (κ : Sub (l ∙ Δ) ∅) (ρ : 𝓓⟦ l ∙ Δ ⟧ κ) →
             𝓥⟦ weaken T ⟧ ρ ≡ 𝓥⟦ T ⟧ (proj₂ ρ)
𝓥⟦⟧-weaken T κ ρ =
  trans (𝓥⟦⟧-ren T wkᴿ κ ρ) (cong (𝓥⟦ T ⟧ {⟨ wkᴿ ⟩ ⨟ˢ κ}) (⊛𝓓-wk₀ κ ρ))

-- ══════════════ §A7  Coercion bookkeeping, then `𝓖⟦_⟧` ═════════════
-- The ONE mismatch deviation D1 buys us is between
--   `⟦ T ⟧ᵀ (envOf η)`  (what `E⟦_⟧` produces)  and
--   `⟦ T [ η ]ˢ ⟧ᵀ []`  (what `𝓥⟦ T ⟧ ρ` consumes),
-- bridged by `⟦⟧ᵀ-closing` = their `Tsub-preserves-semantics`.  All the
-- coherence obligations it generates are equalities BETWEEN PROOFS of
-- Set-equalities, so UIP (Agda's default K) discharges them wholesale.
-- STW cannot use this shortcut in the same places because their
-- corresponding obligations are `≡ω` equations between `Setω` objects.

uip : ∀ {a}{A : Set a}{x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

-- a chain of one, two or three `subst id`s equals any single one
coe¹ : ∀ {a}{A B : Set a} (p q : A ≡ B) (x : A) → subst id p x ≡ subst id q x
coe¹ p q x = cong (λ t → subst id t x) (uip p q)

coe² : ∀ {a}{A B C : Set a} (p : A ≡ B) (q : B ≡ C) (s : A ≡ C) (x : A) →
       subst id q (subst id p x) ≡ subst id s x
coe² refl refl s x = sym (cong (λ t → subst id t x) (uip s refl))

coe³ : ∀ {a}{A B C D : Set a} (p : A ≡ B) (q : B ≡ C) (r : C ≡ D) (s : A ≡ D) (x : A) →
       subst id r (subst id q (subst id p x)) ≡ subst id s x
coe³ refl refl refl s x = sym (cong (λ t → subst id t x) (uip s refl))

-- pushing a coercion through `→` and through `(A : Set l) → _`
coe-⇒ : ∀ {l₁ l₂}{A A′ : Set l₁}{B B′ : Set l₂}
        (p : A ≡ A′) (q : B ≡ B′) (f : A′ → B′) (x : A) →
        subst id (sym (cong₂ (λ X Y → X → Y) p q)) f x
        ≡ subst id (sym q) (f (subst id p x))
coe-⇒ refl refl f x = refl

coe-Π : ∀ {l l′}{f g : Set l → Set l′} (p : f ≡ g)
        (F : (A : Set l) → g A) (A₀ : Set l) →
        subst id (sym (cong (λ k → (A : Set l) → k A) p)) F A₀
        ≡ subst id (sym (cong (λ k → k A₀) p)) (F A₀)
coe-Π refl F A₀ = refl

-- `subst` along a family, re-expressed as `subst id`
substᴮ : ∀ {a b}{A : Set a} (B : A → Set b) {x y : A} (p : x ≡ y) (z : B x) →
         subst B p z ≡ subst id (cong B p) z
substᴮ B refl z = refl

-- dependent application respects equality of the argument
dapp : ∀ {a b}{A : Set a}{B : A → Set b} (f : (x : A) → B x) {x y : A} (p : x ≡ y) →
       subst B p (f x) ≡ f y
dapp f refl = refl

--! coeT
coeᵀ : ∀ {Δ l} (η : Sub Δ ∅) (T : Type Δ l) → ⟦ T ⟧ᵀ (envOf η) → ⟦ T [ η ]ˢ ⟧ᵀ []
coeᵀ η T = subst id (sym (⟦⟧ᵀ-closing η T))

coeᵀ⁻ : ∀ {Δ l} (η : Sub Δ ∅) (T : Type Δ l) → ⟦ T [ η ]ˢ ⟧ᵀ [] → ⟦ T ⟧ᵀ (envOf η)
coeᵀ⁻ η T = subst id (⟦⟧ᵀ-closing η T)

coeᵀ-inv : ∀ {Δ l} (η : Sub Δ ∅) (T : Type Δ l) (z : ⟦ T [ η ]ˢ ⟧ᵀ []) →
           coeᵀ η T (coeᵀ⁻ η T z) ≡ z
coeᵀ-inv η T z = subst-sym-subst {P = id} (⟦⟧ᵀ-closing η T)

-- ── closing value substitutions (their LogicalPrelim §CSub) ──

--! CSub
CSub : ∀ {Δ} → Sub Δ ∅ → Ctx Δ → Set
CSub {Δ} η Γ = ∀ l (T : Type Δ l) → Γ ∋ T → CValue (T [ η ]ˢ)

--! ESSC
ES←SC : ∀ {Δ}{Γ : Ctx Δ} (η : Sub Δ ∅) → CSub η Γ → η ∣ Γ ⇒ˢ ∅
ES←SC η χ l T x = exp (χ l T x)

--! Csub
Csub : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} (η : Sub Δ ∅) →
       CSub η Γ → Expr Γ T → CExpr (T [ η ]ˢ)
Csub η χ e = η ∣ e [ ES←SC η χ ]ˢ

--! Cextend
Cextend : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} (η : Sub Δ ∅) →
          CSub η Γ → CValue (T [ η ]ˢ) → CSub η (Γ ▷ T)
Cextend η χ w _ _ zero    = w
Cextend η χ w _ _ (suc x) = χ _ _ x

--! Cdropt
-- their `Cdrop-t` carries `subst CValue (fusion-Tsub-Tren T (Twkᵣ Tidᵣ) σ*)`.
-- GONE: `(weaken T) [ η ]ˢ ≡ T [ ⟨ wkᴿ ⟩ ⨟ˢ η ]ˢ` is a registered rewrite.
Cdrop-t : ∀ {Δ}{Γ : Ctx Δ}{l} (η : Sub (l ∙ Δ) ∅) →
          CSub η (Γ ▷* l) → CSub (⟨ wkᴿ ⟩ ⨟ˢ η) Γ
Cdrop-t η χ l₀ T x = χ l₀ (weaken T) (suc* x)

--! Cextt
-- their `Cextt` carries `subst CValue (sym (σT≡TextₛσTwkT σ* T))`.
-- GONE: `(weaken T) [ T′ ∙ˢ η ]ˢ ≡ T [ η ]ˢ` is a registered rewrite.
Cextt : ∀ {Δ}{Γ : Ctx Δ}{l} (η : Sub Δ ∅) (T′ : Type ∅ l) →
        CSub η Γ → CSub (T′ ∙ˢ η) (Γ ▷* l)
Cextt η T′ χ _ _ (suc* x) = χ _ _ x

-- their `Cextend-Eext`
ES-Cextend : ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} (η : Sub Δ ∅)
             (χ : CSub η Γ) (w : CValue (T [ η ]ˢ)) →
             ES←SC η (Cextend {T = T} η χ w) ≡ (η ∣ exp w ∙ˢ ES←SC η χ)
ES-Cextend η χ w =
  fun-ext λ _ → fun-ext λ _ → fun-ext λ { zero → refl ; (suc x) → refl }

-- their `Cextt-Eextₛ-l` (which needs `dist-subst'` and a nested `trans`
-- chain over three fusion lemmas); here every component is `refl`.
ES-Cextt : ∀ {Δ}{Γ : Ctx Δ}{l} (η : Sub Δ ∅) (T′ : Type ∅ l) (χ : CSub η Γ) →
           ES←SC (T′ ∙ˢ η) (Cextt η T′ χ) ≡ (η ∣ T′ ∙ˢ* ES←SC η χ)
ES-Cextt η T′ χ = fun-ext λ _ → fun-ext λ _ → fun-ext λ { (suc* x) → refl }

-- their `Cextend-Elift`
Csub-Cextend : ∀ {Δ}{Γ : Ctx Δ}{l₁ l₂}{T₁ : Type Δ l₁}{T₂ : Type Δ l₂}
               (η : Sub Δ ∅) (χ : CSub η Γ) (w : CValue (T₁ [ η ]ˢ))
               (b : Expr (Γ ▷ T₁) T₂) →
               Csub η (Cextend η χ w) b
               ≡ (η ∣ b [ (η ∣ ES←SC η χ ⇑ˢ T₁) ]ˢ) [ exp w ]
Csub-Cextend η χ w b =
  trans (cong (η ∣ b [_]ˢ) (ES-Cextend η χ w))
        (sym (lift-cons-sub η b (ES←SC η χ) (exp w)))

-- the `Λ`-case analogue
Csub-Cextt : ∀ {Δ}{Γ : Ctx Δ}{l l′}{T : Type (l ∙ Δ) l′}
             (η : Sub Δ ∅) (χ : CSub η Γ) (T′ : Type ∅ l) (b : Expr (Γ ▷* l) T) →
             Csub (T′ ∙ˢ η) (Cextt η T′ χ) b
             ≡ (((η ↑ˢ) ∣ b [ (η ∣ ES←SC η χ ⇑ˢ*) ]ˢ) [* T′ *])
Csub-Cextt η χ T′ b =
  trans (cong ((T′ ∙ˢ η) ∣ b [_]ˢ) (ES-Cextt η T′ χ))
        (sym (lift*-cons-sub η b (ES←SC η χ) T′))

-- ── the relational environment (their `𝓖⟦_⟧`) ──
--! MCG
𝓖⟦_⟧ : ∀ {Δ} (Γ : Ctx Δ) {η : Sub Δ ∅} → 𝓓⟦ Δ ⟧ η →
       CSub η Γ → Envᵥ Γ (envOf η) → Set (maxC Γ)
𝓖⟦ ∅ ⟧        ρ χ γ = ⊤
𝓖⟦ Γ ▷ T ⟧ {η} ρ χ γ =
  𝓥⟦ T ⟧ ρ (χ _ _ zero) (coeᵀ η T (proj₁ γ)) ×
  𝓖⟦ Γ ⟧ ρ (λ l A x → χ l A (suc x)) (proj₂ γ)
𝓖⟦ Γ ▷* l ⟧ {η} ρ χ γ = 𝓖⟦ Γ ⟧ (proj₂ ρ) (Cdrop-t η χ) γ

--! MCGlookup
-- their `𝓖-lookup`.  The `suc*` case is the one
-- that needs `LRVwk-eq`; ours needs `𝓥⟦⟧-weaken` plus pure coercion
-- coherence, which `coe²` discharges.
𝓖-lookup : ∀ {Δ}{Γ : Ctx Δ}{η : Sub Δ ∅} (ρ : 𝓓⟦ Δ ⟧ η)
           (χ : CSub η Γ) (γ : Envᵥ Γ (envOf η)) → 𝓖⟦ Γ ⟧ ρ χ γ →
           ∀ {l}{T : Type Δ l} (x : Γ ∋ T) →
           𝓥⟦ T ⟧ ρ (χ _ _ x) (coeᵀ η T (lookupᵥ x (envOf η) γ))
𝓖-lookup ρ χ γ g zero    = proj₁ g
𝓖-lookup ρ χ γ g (suc x) =
  𝓖-lookup ρ (λ l A y → χ l A (suc y)) (proj₂ γ) (proj₂ g) x
𝓖-lookup {η = η} ρ χ γ g (suc* {T = T} x) =
  subst (λ R → R (χ _ _ (suc* x)) (coeᵀ η (weaken T) (lookupᵥ (suc* x) (envOf η) γ)))
        (sym (𝓥⟦⟧-weaken T η ρ))
        (subst (𝓥⟦ T ⟧ (proj₂ ρ) (χ _ _ (suc* x))) denot
               (𝓖-lookup (proj₂ ρ) (Cdrop-t η χ) γ g x))
  where
  a : ⟦ T ⟧ᵀ (envOf (⟨ wkᴿ ⟩ ⨟ˢ η))
  a = lookupᵥ x (envOf (⟨ wkᴿ ⟩ ⨟ˢ η)) γ
  p₁ : ⟦ T ⟧ᵀ (envOf (⟨ wkᴿ ⟩ ⨟ˢ η)) ≡ ⟦ weaken T ⟧ᵀ (envOf η)
  p₁ = sym (⟦⟧ᵀ-ren wkᴿ (envOf (⟨ wkᴿ ⟩ ⨟ˢ η)) (envOf η)
                    (Ren*ᵀ-wk (envOf (⟨ wkᴿ ⟩ ⨟ˢ η)) (⟦ here &ˢ η ⟧ᵀ [])) T)
  p₂ : ⟦ weaken T ⟧ᵀ (envOf η) ≡ ⟦ (weaken T) [ η ]ˢ ⟧ᵀ []
  p₂ = sym (⟦⟧ᵀ-closing η (weaken T))
  s  : ⟦ T ⟧ᵀ (envOf (⟨ wkᴿ ⟩ ⨟ˢ η)) ≡ ⟦ T [ ⟨ wkᴿ ⟩ ⨟ˢ η ]ˢ ⟧ᵀ []
  s  = sym (⟦⟧ᵀ-closing (⟨ wkᴿ ⟩ ⨟ˢ η) T)
  denot : coeᵀ (⟨ wkᴿ ⟩ ⨟ˢ η) T a ≡ coeᵀ η (weaken T) (lookupᵥ (suc* x) (envOf η) γ)
  denot = sym (coe² p₁ p₂ s a)

-- ══════════════ §A8  THE FUNDAMENTAL THEOREM  (their Fundamental.agda) ═══
-- canonical-forms helpers: a value whose expression is a λ (resp. Λ) IS
-- that λ (resp. Λ) paired with the only possible `isValue` proof.
value-ƛ : ∀ {l₁ l₂}{T₁ : Type ∅ l₁}{T₂ : Type ∅ l₂}
          (u : CValue (T₁ ⇒ T₂)) (b : Expr (∅ ▷ T₁) T₂) →
          exp u ≡ λx b → u ≡ (λx b , V-ƛ)
value-ƛ (_ , V-ƛ) b refl = refl

value-Λ : ∀ {l l′}{T : Type (l ∙ ∅) l′}
          (u : CValue (∀α T)) (b : Expr (∅ ▷* l) T) →
          exp u ≡ Λα b → u ≡ (Λα b , V-Λ)
value-Λ (_ , V-Λ) b refl = refl

--! SemanticSoundness
-- Their `Γ ⊨ e ⦂ T` / `fundamental`.  The ONE difference to their
-- statement is the `coeᵀ` on the denotation, which is deviation D1's
-- entire cost: their `E⟦ e ⟧ η γ` already has type `⟦ T ⟧ (⟦ π₁ ρ ⟧* [])`,
-- ours has type `⟦ T ⟧ᵀ (envOf η)` and must be moved to
-- `⟦ T [ η ]ˢ ⟧ᵀ []` by their own `Tsub-preserves-semantics`.
semantic-soundness :
  ∀ {Δ}{Γ : Ctx Δ}{l}{T : Type Δ l} (e : Expr Γ T)
    {η : Sub Δ ∅} (ρ : 𝓓⟦ Δ ⟧ η) (χ : CSub η Γ) (γ : Envᵥ Γ (envOf η)) →
    𝓖⟦ Γ ⟧ ρ χ γ → 𝓔⟦ T ⟧ ρ (Csub η χ e) (coeᵀ η T (E⟦ e ⟧ (envOf η) γ))

semantic-soundness (` x) ρ χ γ g =
  (χ _ _ x , Value-⇓ (χ _ _ x) , 𝓖-lookup ρ χ γ g x)

semantic-soundness true  ρ χ γ g = ((true  , V-true)  , ⇓-true  , lift refl)
semantic-soundness false ρ χ γ g = ((false , V-false) , ⇓-false , lift refl)

semantic-soundness (_·_ {T₁ = T₁} {T₂ = T₂} e₁ e₂) {η} ρ χ γ g =
  let (u , d₁ , (b , p , h)) = semantic-soundness e₁ ρ χ γ g
      (w , d₂ , r)           = semantic-soundness e₂ ρ χ γ g
      (v , d₃ , rv)          = h w (coeᵀ η T₁ (E⟦ e₂ ⟧ (envOf η) γ)) r
  in ( v
     , ⇓-· (subst (Csub η χ e₁ ⇓_) (value-ƛ u b p) d₁) d₂ d₃
     , subst (𝓥⟦ T₂ ⟧ ρ v) (eqf u b p) rv )
  where
  F₀ = E⟦ e₁ ⟧ (envOf η) γ
  z₂ = E⟦ e₂ ⟧ (envOf η) γ
  q₁ = ⟦⟧ᵀ-closing η T₁
  q₂ = ⟦⟧ᵀ-closing η T₂
  eqf : ∀ u b (p : exp u ≡ λx b) →
        coeᵀ η (T₁ ⇒ T₂) F₀ (coeᵀ η T₁ z₂) ≡ coeᵀ η T₂ (F₀ z₂)
  eqf u b p =
    trans (coe-⇒ q₁ q₂ F₀ (coeᵀ η T₁ z₂))
          (cong (λ y → subst id (sym q₂) (F₀ y)) (subst-subst-sym {P = id} q₁))

semantic-soundness (λx {T₁ = T₁} {T₂ = T₂} b) {η} ρ χ γ g =
  ( (λx b′ , V-ƛ) , ⇓-ƛ , (b′ , refl , fn) )
  where
  b′ = η ∣ b [ (η ∣ ES←SC η χ ⇑ˢ T₁) ]ˢ
  F₀ = λ (y : ⟦ T₁ ⟧ᵀ (envOf η)) → E⟦ b ⟧ (envOf η) (y , γ)
  q₁ = ⟦⟧ᵀ-closing η T₁
  q₂ = ⟦⟧ᵀ-closing η T₂
  fn : ∀ (w : CValue (T₁ [ η ]ˢ)) (z : ⟦ T₁ [ η ]ˢ ⟧ᵀ []) → 𝓥⟦ T₁ ⟧ ρ w z →
       𝓔⟦ T₂ ⟧ ρ (b′ [ exp w ]) (coeᵀ η (T₁ ⇒ T₂) F₀ z)
  fn w z r =
    subst₂ (𝓔⟦ T₂ ⟧ ρ)
           (Csub-Cextend η χ w b)
           (sym (coe-⇒ q₁ q₂ F₀ z))
           (semantic-soundness b ρ (Cextend η χ w) (coeᵀ⁻ η T₁ z , γ)
              ( subst (𝓥⟦ T₁ ⟧ ρ w) (sym (coeᵀ-inv η T₁ z)) r , g ))

semantic-soundness (Λα {l = l} {T = T} b) {η} ρ χ γ g =
  ( (Λα b′ , V-Λ) , ⇓-Λ , (b′ , refl , k) )
  where
  b′ = (η ↑ˢ) ∣ b [ (η ∣ ES←SC η χ ⇑ˢ*) ]ˢ
  G₀ = λ (A : Set l) → E⟦ b ⟧ (A ∷ envOf η) γ
  P  = fun-ext λ (A : Set l) →
         ⟦⟧ᵀ-sub (η ↑ˢ) (A ∷ envOf η) (A ∷ [])
                 (Sub*ᵀ-lift η (envOf η) [] A (Sub*ᵀ-envOf η)) T
  k : ∀ (T′ : Type ∅ l) (R : REL T′) →
      Σ[ v ∈ CValue (T [ T′ ∙ˢ η ]ˢ) ] (((b′ [* T′ *]) ⇓ v) ×
        𝓥⟦ T ⟧ {T′ ∙ˢ η} (R , ρ) v
          (subst id (sym (⟦⟧ᵀ-single [] T′ (T [ η ↑ˢ ]ˢ)))
                 (coeᵀ η (∀α T) G₀ (⟦ T′ ⟧ᵀ []))))
  k T′ R =
    subst₂ (𝓔⟦ T ⟧ {T′ ∙ˢ η} (R , ρ))
           (Csub-Cextt η χ T′ b) denot
           (semantic-soundness b (R , ρ) (Cextt η T′ χ) γ g)
    where
    A₀ = ⟦ T′ ⟧ᵀ []
    S₁ = sym (⟦⟧ᵀ-single [] T′ (T [ η ↑ˢ ]ˢ))
    Q  = sym (cong (λ (κ : Set l → Set _) → κ A₀) P)
    S₀ = sym (⟦⟧ᵀ-closing (T′ ∙ˢ η) T)
    denot : coeᵀ (T′ ∙ˢ η) T (G₀ A₀)
          ≡ subst id S₁ (coeᵀ η (∀α T) G₀ A₀)
    denot = sym (trans (cong (subst id S₁) (coe-Π P G₀ A₀))
                       (coe² Q S₁ S₀ (G₀ A₀)))

semantic-soundness (_·*_ {l = l} {T = T} e T′) {η} ρ χ γ g =
  let (u , d , (b , p , k)) = semantic-soundness e ρ χ γ g
      (v , d₂ , rv)         = k (T′ [ η ]ˢ) (𝓥⟦ T′ ⟧ {η} ρ)
  in ( v
     , ⇓-∙ (subst (Csub η χ e ⇓_) (value-Λ u b p) d) d₂
     , subst (λ R → R v _) (sym (𝓥⟦⟧-[]* T T′ η ρ))
             (subst (𝓥⟦ T ⟧ {(T′ [ η ]ˢ) ∙ˢ η} (𝓥⟦ T′ ⟧ {η} ρ , ρ) v) denot rv) )
  where
  G₀ = E⟦ e ⟧ (envOf η) γ
  A₁ = ⟦ T′ [ η ]ˢ ⟧ᵀ []
  A₂ = ⟦ T′ ⟧ᵀ (envOf η)
  B  = λ (A : Set l) → ⟦ T ⟧ᵀ (A ∷ envOf η)
  P  = fun-ext λ (A : Set l) →
         ⟦⟧ᵀ-sub (η ↑ˢ) (A ∷ envOf η) (A ∷ [])
                 (Sub*ᵀ-lift η (envOf η) [] A (Sub*ᵀ-envOf η)) T
  S₁ = sym (⟦⟧ᵀ-single [] (T′ [ η ]ˢ) (T [ η ↑ˢ ]ˢ))
  Q  = sym (cong (λ (κ : Set l → Set _) → κ A₁) P)
  S₃ = sym (⟦⟧ᵀ-single (envOf η) T′ T)
  S₂ = sym (⟦⟧ᵀ-closing η (T [ T′ ]*))
  -- both denotations are coercions of the SAME element `G₀ A₁` into the
  -- SAME type; UIP (via coe²/coe³) identifies them.
  denot : subst id S₁ (coeᵀ η (∀α T) G₀ A₁)
        ≡ coeᵀ η (T [ T′ ]*) (subst id S₃ (G₀ A₂))
  denot =
    trans (trans (cong (subst id S₁) (coe-Π P G₀ A₁))
                 (coe² Q S₁ (trans Q S₁) (G₀ A₁)))
          (sym (trans (cong (λ y → subst id S₂ (subst id S₃ y))
                            (trans (sym (dapp G₀ (⟦⟧ᵀ-closing η T′)))
                                   (substᴮ B (⟦⟧ᵀ-closing η T′) (G₀ A₁))))
                      (coe³ (cong B (⟦⟧ᵀ-closing η T′)) S₃ S₂ (trans Q S₁) (G₀ A₁))))

-- ══════════════ §A9  ADEQUACY ══════════════════════════════════════

χ∅ : CSub {∅} idˢ ∅
χ∅ _ _ ()

ES∅ : ES←SC {Γ = ∅} idˢ χ∅ ≡ Idˢ
ES∅ = fun-ext λ _ → fun-ext λ _ → fun-ext λ ()

coeᵀ-idˢ : ∀ {l} (T : Type ∅ l) (z : ⟦ T ⟧ᵀ []) → coeᵀ idˢ T z ≡ z
coeᵀ-idˢ T z = coe¹ (sym (⟦⟧ᵀ-closing idˢ T)) refl z

--! Fundamental
fundamental : ∀ {l} {T : Type ∅ l} (e : CExpr T) →
              𝓔⟦ T ⟧ {idˢ} tt e (E⟦ e ⟧ [] tt)
fundamental {T = T} e =
  subst₂ (𝓔⟦ T ⟧ {idˢ} tt)
         (trans (cong (idˢ ∣ e [_]ˢ) ES∅) (Identityᵣ e))
         (coeᵀ-idˢ T (E⟦ e ⟧ [] tt))
         (semantic-soundness e tt χ∅ tt tt)

𝔹val : Bool → CValue 𝔹
𝔹val tt𝔹 = (true  , V-true)
𝔹val ff𝔹 = (false , V-false)

--! Adequacy
-- their `adequacy : ∀ (e : CExpr `ℕ) n → E⟦ e ⟧ [] γ₀ ≡ n → e ⇓ (# n , V-♯)`
adequacy : ∀ (e : CExpr 𝔹) (b : Bool) → E⟦ e ⟧ [] tt ≡ lift b → e ⇓ 𝔹val b
adequacy e b h with fundamental e
... | (v , d , lift q) = go v d (trans q h)
  where
  go : (v : CValue 𝔹) → e ⇓ v → E⟦ exp v ⟧ [] tt ≡ lift b → e ⇓ 𝔹val b
  go (_ , V-true)  d eq = subst (λ c → e ⇓ 𝔹val c) (cong lower eq) d
  go (_ , V-false) d eq = subst (λ c → e ⇓ 𝔹val c) (cong lower eq) d

-- the tag-free corollary: every closed boolean expression evaluates to
-- one of the two literals
canonicity-⇓ : ∀ (e : CExpr 𝔹) →
               (e ⇓ (true , V-true)) ⊎ (e ⇓ (false , V-false))
-- (`Lift` is a record, so `lift (lower z) ≡ z` holds by η and no
-- `inspect` idiom is needed)
canonicity-⇓ e = go (lower (E⟦ e ⟧ [] tt)) refl
  where
  go : ∀ (b : Bool) → E⟦ e ⟧ [] tt ≡ lift b →
       (e ⇓ (true , V-true)) ⊎ (e ⇓ (false , V-false))
  go tt𝔹 eq = inj₁ (adequacy e tt𝔹 eq)
  go ff𝔹 eq = inj₂ (adequacy e ff𝔹 eq)
