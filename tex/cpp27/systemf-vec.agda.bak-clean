{-# OPTIONS --rewriting --local-confluence-check #-}

-- systemf.agda with maps as inductive vectors instead of functions.
-- Equality of maps is then equality of data, so this module assumes
-- nothing: no function extensionality and no postulates.  The same
-- syntax, the same 72 rules and the same subject reduction.  §3.4 of
-- the paper compares the two models.
--
-- Two halves, and only the first is generated:
--
--   the σ-calculus, down to the REWRITE block
--       supplement/generator/agdasubst.py --model=vectors --no-star \
--           systemf.sg systemf-vec.agda
--
--   the typing rules and subject reduction, below it
--       hand-written, and not reproduced by the generator
--
-- Regenerating therefore replaces the first half only.
--
-- The 72 rules are the same rules.  61 carry the same names as in
-- systemf.agda; the 11 traversal rules differ, because the generator
-- names them after their constructor (`inst-λx_`) where the
-- hand-written file abbreviates (`inst-λ`).

module systemf-vec where

open import Data.List using (drop)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

cong1 : ∀ {A1 A2 : Set} (f : A1 → A2) {a1 a2} →
  a1 ≡ a2 → f a1 ≡ f a2
cong1 f refl = refl

cong2 : ∀ {A1 A2 A3 : Set} (f : A1 → A2 → A3) {a1 a2 a3 a4} →
  a1 ≡ a2 → a3 ≡ a4 → f a1 a3 ≡ f a2 a4
cong2 f refl refl = refl

infixr 5 _⇒_
infixl 6 _·_
infixl 6 _•_

-- ─── syntax ─────────────────────────────────────────────────────────

data Sort : Set where
  kind type expr : Sort
Scope = List Sort

variable
  s s₁ s₂ s′ : Sort
  S S₁ S₂ S₃ : Scope


data Mode : Set where V T : Mode

variable
  m : Mode

data _⊢[_]_ : Scope → Mode → Sort → Set

_⊢_ = _⊢[ T ]_
_∋_ = _⊢[ V ]_

data _⊢[_]_ where
  zero    : (s ∷ S) ∋ s
  suc     : S ∋ s → (s′ ∷ S) ∋ s
  `_      : S ∋ s → S ⊢ s
  λx_     : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_     : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_ : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_     : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_     : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_     : S ⊢ type → S ⊢ type → S ⊢ type
  *       : S ⊢ kind

variable
  t t₁ t₂ t′ : S ⊢ s
  x x′       : S ∋ s
  x/t x/t′   : S ⊢[ m ] s

variable
  expr0 expr1 : S ⊢ expr
  kind0 : S ⊢ kind
  type0 type1 : S ⊢ type

-- ─── maps as vectors ────────────────────────────────────────────────

infixr 5 _∙ᴿ_ _∙ˢ_

data _→ᴿ_ : Scope → Scope → Set where
  []   : [] →ᴿ S
  _∙ᴿ_ : S₂ ∋ s → S₁ →ᴿ S₂ → (s ∷ S₁) →ᴿ S₂

data _→ˢ_ : Scope → Scope → Set where
  []   : [] →ˢ S
  _∙ˢ_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂

variable
  ξ ξ′ ξ₁ ξ₂ ξ₃ : S₁ →ᴿ S₂
  σ σ′ σ₁ σ₂ σ₃ τ ρ : S₁ →ˢ S₂

-- ─── the renaming world ─────────────────────────────────────────────

opaque
  -- post-composition with weakening: the primitive recursion that lets
  -- lifting and the identity be defined without a composition cycle
  wk*ᴿ : ∀ s′ → S₁ →ᴿ S₂ → S₁ →ᴿ (s′ ∷ S₂)
  wk*ᴿ s′ []       = []
  wk*ᴿ s′ (x ∙ᴿ ξ) = suc x ∙ᴿ wk*ᴿ s′ ξ

  idᴿ : S →ᴿ S
  idᴿ {[]}    = []
  idᴿ {s ∷ S} = zero ∙ᴿ wk*ᴿ s idᴿ

  wkᴿ : ∀ s′ → S →ᴿ (s′ ∷ S)
  wkᴿ s′ = wk*ᴿ s′ idᴿ

  _↑ᴿ_ : S₁ →ᴿ S₂ → ∀ s → (s ∷ S₁) →ᴿ (s ∷ S₂)
  ξ ↑ᴿ s = zero ∙ᴿ wk*ᴿ s ξ

opaque
  unfolding wk*ᴿ idᴿ wkᴿ _↑ᴿ_

  _[_]ᴿ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → S₂ ⊢[ m ] s
  zero    [ x ∙ᴿ ξ ]ᴿ = x
  (suc y) [ x ∙ᴿ ξ ]ᴿ = y [ ξ ]ᴿ
  (`_ x) [ ξ ]ᴿ = `_ (x [ ξ ]ᴿ)
  (λx_ expr0)           [ ξ ]ᴿ = λx_ (expr0 [ ξ ↑ᴿ expr ]ᴿ)
  (Λα_ expr0)           [ ξ ]ᴿ = Λα_ (expr0 [ ξ ↑ᴿ type ]ᴿ)
  (∀[α∶_]_ kind0 type0) [ ξ ]ᴿ = ∀[α∶_]_ (kind0 [ ξ ]ᴿ) (type0 [ ξ ↑ᴿ type ]ᴿ)
  (_·_ expr0 expr1)     [ ξ ]ᴿ = _·_ (expr0 [ ξ ]ᴿ) (expr1 [ ξ ]ᴿ)
  (_•_ expr0 type0)     [ ξ ]ᴿ = _•_ (expr0 [ ξ ]ᴿ) (type0 [ ξ ]ᴿ)
  (_⇒_ type0 type1)     [ ξ ]ᴿ = _⇒_ (type0 [ ξ ]ᴿ) (type1 [ ξ ]ᴿ)
  *                     [ ξ ]ᴿ = *

  _⨟ᴿ_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
  []       ⨟ᴿ ξ₂ = []
  (x ∙ᴿ ξ) ⨟ᴿ ξ₂ = (x [ ξ₂ ]ᴿ) ∙ᴿ (ξ ⨟ᴿ ξ₂)

-- ─── the substitution world ─────────────────────────────────────────

opaque
  unfolding wk*ᴿ idᴿ wkᴿ _↑ᴿ_ _[_]ᴿ _⨟ᴿ_

  ⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂
  ⟨ [] ⟩     = []
  ⟨ x ∙ᴿ ξ ⟩ = (`_ x) ∙ˢ ⟨ ξ ⟩

  -- post-composition of a substitution with a renaming: keeps ↑ˢ
  -- structural, and is erased by ⨟ˢᴿ-def before any rule sees it
  _⨟ˢᴿ_ : S₁ →ˢ S₂ → S₂ →ᴿ S₃ → S₁ →ˢ S₃
  []       ⨟ˢᴿ ξ = []
  (t ∙ˢ σ) ⨟ˢᴿ ξ = (t [ ξ ]ᴿ) ∙ˢ (σ ⨟ˢᴿ ξ)

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s = (`_ zero) ∙ˢ (σ ⨟ˢᴿ wkᴿ s)

opaque
  unfolding wk*ᴿ idᴿ wkᴿ _↑ᴿ_ _[_]ᴿ ⟨_⟩ _⨟ˢᴿ_ _↑ˢ_

  _[_]ˢ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
  zero    [ t ∙ˢ σ ]ˢ = t
  (suc y) [ t ∙ˢ σ ]ˢ = y [ σ ]ˢ
  (`_ x) [ σ ]ˢ = x [ σ ]ˢ
  (λx_ expr0)           [ σ ]ˢ = λx_ (expr0 [ σ ↑ˢ expr ]ˢ)
  (Λα_ expr0)           [ σ ]ˢ = Λα_ (expr0 [ σ ↑ˢ type ]ˢ)
  (∀[α∶_]_ kind0 type0) [ σ ]ˢ = ∀[α∶_]_ (kind0 [ σ ]ˢ) (type0 [ σ ↑ˢ type ]ˢ)
  (_·_ expr0 expr1)     [ σ ]ˢ = _·_ (expr0 [ σ ]ˢ) (expr1 [ σ ]ˢ)
  (_•_ expr0 type0)     [ σ ]ˢ = _•_ (expr0 [ σ ]ˢ) (type0 [ σ ]ˢ)
  (_⇒_ type0 type1)     [ σ ]ˢ = _⇒_ (type0 [ σ ]ˢ) (type1 [ σ ]ˢ)
  *                     [ σ ]ˢ = *

  _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  []       ⨟ σ₂ = []
  (t ∙ˢ σ) ⨟ σ₂ = (t [ σ₂ ]ˢ) ∙ˢ (σ ⨟ σ₂)

idˢ : S →ˢ S
idˢ = ⟨ idᴿ ⟩

wkˢ : ∀ s′ → S →ˢ (s′ ∷ S)
wkˢ s′ = ⟨ wkᴿ s′ ⟩

-- ─── the two-world rewrite system ───────────────────────────────────

opaque
  unfolding wk*ᴿ idᴿ wkᴿ _↑ᴿ_ _[_]ᴿ _⨟ᴿ_ ⟨_⟩ _⨟ˢᴿ_ _↑ˢ_ _[_]ˢ _⨟_

  -- ══ Iᴿ. applied rules, renaming world ═════════════════════════════
  def-∙ᴿ-zero : zero [ (x ∙ᴿ ξ) ]ᴿ ≡ x
  def-∙ᴿ-zero = refl

  def-∙ᴿ-suc : (suc {s′ = s′} x′) [ (x ∙ᴿ ξ) ]ᴿ ≡ x′ [ ξ ]ᴿ
  def-∙ᴿ-suc = refl

  lookup-wk*ᴿ : ∀ (x : S₁ ∋ s) (ξ : S₁ →ᴿ S₂) → x [ wk*ᴿ s′ ξ ]ᴿ ≡ suc (x [ ξ ]ᴿ)
  lookup-wk*ᴿ zero    (y ∙ᴿ ξ) = refl
  lookup-wk*ᴿ (suc x) (y ∙ᴿ ξ) = lookup-wk*ᴿ x ξ

  lookup-idᴿ : ∀ (x : S ∋ s) → x [ idᴿ ]ᴿ ≡ x
  lookup-idᴿ zero    = refl
  lookup-idᴿ (suc x) = trans (lookup-wk*ᴿ x idᴿ) (cong suc (lookup-idᴿ x))

  def-wkᴿ : x [ wkᴿ s′ ]ᴿ ≡ suc x
  def-wkᴿ {x = x} = trans (lookup-wk*ᴿ x idᴿ) (cong suc (lookup-idᴿ x))

  def-↑ᴿ-zero : zero [ (ξ ↑ᴿ s) ]ᴿ ≡ zero
  def-↑ᴿ-zero = refl

  def-↑ᴿ-suc : (suc x) [ (ξ ↑ᴿ s) ]ᴿ ≡ suc (x [ ξ ]ᴿ)
  def-↑ᴿ-suc {x = x} {ξ = ξ} = lookup-wk*ᴿ x ξ

  lift-idᴿ : (idᴿ {S} ↑ᴿ s) ≡ idᴿ
  lift-idᴿ = refl

  -- ══ IIᴿ. traversal rules, renaming world ═════════════════════════
  instᴿ-var : (`_ x) [ ξ ]ᴿ ≡ `_ (x [ ξ ]ᴿ)
  instᴿ-λx_     : (λx_ expr0) [ ξ ]ᴿ           ≡ λx_ (expr0 [ ξ ↑ᴿ expr ]ᴿ)
  instᴿ-Λα_     : (Λα_ expr0) [ ξ ]ᴿ           ≡ Λα_ (expr0 [ ξ ↑ᴿ type ]ᴿ)
  instᴿ-∀[α∶_]_ : (∀[α∶_]_ kind0 type0) [ ξ ]ᴿ ≡ ∀[α∶_]_ (kind0 [ ξ ]ᴿ) (type0 [ ξ ↑ᴿ type ]ᴿ)
  instᴿ-_·_     : (_·_ expr0 expr1) [ ξ ]ᴿ     ≡ _·_ (expr0 [ ξ ]ᴿ) (expr1 [ ξ ]ᴿ)
  instᴿ-_•_     : (_•_ expr0 type0) [ ξ ]ᴿ     ≡ _•_ (expr0 [ ξ ]ᴿ) (type0 [ ξ ]ᴿ)
  instᴿ-_⇒_     : (_⇒_ type0 type1) [ ξ ]ᴿ     ≡ _⇒_ (type0 [ ξ ]ᴿ) (type1 [ ξ ]ᴿ)
  instᴿ-*       : * {S = S} [ ξ ]ᴿ             ≡ *
  instᴿ-var = refl
  instᴿ-λx_     = refl
  instᴿ-Λα_     = refl
  instᴿ-∀[α∶_]_ = refl
  instᴿ-_·_     = refl
  instᴿ-_•_     = refl
  instᴿ-_⇒_     = refl
  instᴿ-*       = refl

  -- ══ IIIᴿ. map algebra, renaming world ════════════════════════════
  distᴿ : (x ∙ᴿ ξ₁) ⨟ᴿ ξ₂ ≡ (x [ ξ₂ ]ᴿ) ∙ᴿ (ξ₁ ⨟ᴿ ξ₂)
  distᴿ = refl

  compositionalityᴿᴿ-var : ∀ (x : S₁ ∋ s) {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    x [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ ≡ (x [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ
  compositionalityᴿᴿ-var zero    {ξ₁ = y ∙ᴿ ξ₁} = refl
  compositionalityᴿᴿ-var (suc x) {ξ₁ = y ∙ᴿ ξ₁} = compositionalityᴿᴿ-var x

  wk*ᴿ-⨟ᴿ : ∀ (ξ₁ : S₁ →ᴿ S₂) (x : S₃ ∋ s′) (ξ₂ : S₂ →ᴿ S₃) →
    wk*ᴿ s′ ξ₁ ⨟ᴿ (x ∙ᴿ ξ₂) ≡ ξ₁ ⨟ᴿ ξ₂
  wk*ᴿ-⨟ᴿ []        x ξ₂ = refl
  wk*ᴿ-⨟ᴿ (y ∙ᴿ ξ₁) x ξ₂ = cong (_ ∙ᴿ_) (wk*ᴿ-⨟ᴿ ξ₁ x ξ₂)

  comp-idₗᴿ : idᴿ ⨟ᴿ ξ ≡ ξ
  comp-idₗᴿ {ξ = []}     = refl
  comp-idₗᴿ {ξ = x ∙ᴿ ξ} = cong (x ∙ᴿ_) (trans (wk*ᴿ-⨟ᴿ idᴿ x ξ) comp-idₗᴿ)

  comp-idᵣᴿ : ξ ⨟ᴿ idᴿ ≡ ξ
  comp-idᵣᴿ {ξ = []}     = refl
  comp-idᵣᴿ {ξ = x ∙ᴿ ξ} = cong2 _∙ᴿ_ (lookup-idᴿ x) comp-idᵣᴿ

  interactᴿ : wkᴿ s ⨟ᴿ (x ∙ᴿ ξ) ≡ ξ
  interactᴿ {x = x} {ξ = ξ} = trans (wk*ᴿ-⨟ᴿ idᴿ x ξ) comp-idₗᴿ

  lift-consᴿ : (ξ ↑ᴿ s) ⨟ᴿ (x ∙ᴿ ξ′) ≡ x ∙ᴿ (ξ ⨟ᴿ ξ′)
  lift-consᴿ {ξ = ξ} {x = x} {ξ′ = ξ′} = cong (x ∙ᴿ_) (wk*ᴿ-⨟ᴿ ξ x ξ′)

  assocᴿ : (ξ₁ ⨟ᴿ ξ₂) ⨟ᴿ ξ₃ ≡ ξ₁ ⨟ᴿ (ξ₂ ⨟ᴿ ξ₃)
  assocᴿ {ξ₁ = []}      = refl
  assocᴿ {ξ₁ = x ∙ᴿ ξ₁} = cong2 _∙ᴿ_ (sym (compositionalityᴿᴿ-var x)) assocᴿ

  wk*ᴿ-comp : ∀ (ξ₁ : S₁ →ᴿ S₂) (ξ₂ : S₂ →ᴿ S₃) →
    wk*ᴿ s ξ₁ ⨟ᴿ (ξ₂ ↑ᴿ s) ≡ wk*ᴿ s (ξ₁ ⨟ᴿ ξ₂)
  wk*ᴿ-comp []        ξ₂ = refl
  wk*ᴿ-comp (x ∙ᴿ ξ₁) ξ₂ = cong2 _∙ᴿ_ (lookup-wk*ᴿ x ξ₂) (wk*ᴿ-comp ξ₁ ξ₂)

  ⨟ᴿ-wk*ᴿ : ∀ (ξ₁ : S₁ →ᴿ S₂) (ξ₂ : S₂ →ᴿ S₃) →
    ξ₁ ⨟ᴿ wk*ᴿ s ξ₂ ≡ wk*ᴿ s (ξ₁ ⨟ᴿ ξ₂)
  ⨟ᴿ-wk*ᴿ []        ξ₂ = refl
  ⨟ᴿ-wk*ᴿ (x ∙ᴿ ξ₁) ξ₂ = cong2 _∙ᴿ_ (lookup-wk*ᴿ x ξ₂) (⨟ᴿ-wk*ᴿ ξ₁ ξ₂)

  lift-dist-compᴿᴿ : ((ξ₁ ↑ᴿ s) ⨟ᴿ (ξ₂ ↑ᴿ s)) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂} = cong (zero ∙ᴿ_) (wk*ᴿ-comp ξ₁ ξ₂)

  lift-wkᴿ : wkᴿ s ⨟ᴿ (ξ ↑ᴿ s) ≡ ξ ⨟ᴿ wkᴿ s
  lift-wkᴿ {ξ = ξ} = trans (wk*ᴿ-comp idᴿ ξ)
    (trans (cong (wk*ᴿ _) comp-idₗᴿ)
    (sym (trans (⨟ᴿ-wk*ᴿ ξ idᴿ) (cong (wk*ᴿ _) comp-idᵣᴿ))))

  -- ══ VIᴿ. completion companions, renaming world ═══════════════════
  -- `assocᴿ` right-nests ⨟ᴿ, so a rule whose right operand is not a
  -- metavariable stops matching once a continuation is appended.
  interactᴿ-⨟ᴿ : ∀ {x : S₂ ∋ s} {ξ : S₁ →ᴿ S₂} {ξ′ : S₂ →ᴿ S₃} →
    wkᴿ s ⨟ᴿ ((x ∙ᴿ ξ) ⨟ᴿ ξ′) ≡ ξ ⨟ᴿ ξ′
  interactᴿ-⨟ᴿ {s = s} {x = x} {ξ = ξ} {ξ′ = ξ′} =
    trans (sym (assocᴿ {ξ₁ = wkᴿ s} {ξ₂ = x ∙ᴿ ξ} {ξ₃ = ξ′}))
          (cong (_⨟ᴿ ξ′) (interactᴿ {s = s} {x = x} {ξ = ξ}))

  lift-wkᴿ-⨟ᴿ : ∀ {ξ : S₁ →ᴿ S₂} {ξ′ : (s ∷ S₂) →ᴿ S₃} →
    wkᴿ s ⨟ᴿ ((ξ ↑ᴿ s) ⨟ᴿ ξ′) ≡ ξ ⨟ᴿ (wkᴿ s ⨟ᴿ ξ′)
  lift-wkᴿ-⨟ᴿ {s = s} {ξ = ξ} {ξ′ = ξ′} =
    trans (sym (assocᴿ {ξ₁ = wkᴿ s} {ξ₂ = ξ ↑ᴿ s} {ξ₃ = ξ′}))
          (trans (cong (_⨟ᴿ ξ′) (lift-wkᴿ {s = s} {ξ = ξ}))
                 (assocᴿ {ξ₁ = ξ} {ξ₂ = wkᴿ s} {ξ₃ = ξ′}))

  lift-dist-compᴿᴿ-⨟ᴿ : ∀ {S₄ : Scope} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃}
    {ξ′ : (s ∷ S₃) →ᴿ S₄} →
    (ξ₁ ↑ᴿ s) ⨟ᴿ ((ξ₂ ↑ᴿ s) ⨟ᴿ ξ′) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ⨟ᴿ ξ′
  lift-dist-compᴿᴿ-⨟ᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂} {ξ′ = ξ′} =
    trans (sym (assocᴿ {ξ₁ = ξ₁ ↑ᴿ _} {ξ₂ = ξ₂ ↑ᴿ _} {ξ₃ = ξ′}))
          (cong (_⨟ᴿ ξ′) (lift-dist-compᴿᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂}))

  lift-dist-compᴿᴿ-var : ∀ {x : (s ∷ S₁) ∋ s′} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    (x [ (ξ₁ ↑ᴿ s) ]ᴿ) [ (ξ₂ ↑ᴿ s) ]ᴿ ≡ x [ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s) ]ᴿ
  lift-dist-compᴿᴿ-var {x = x} {ξ₁ = ξ₁} {ξ₂ = ξ₂} =
    trans (sym (compositionalityᴿᴿ-var x {ξ₁ = ξ₁ ↑ᴿ _} {ξ₂ = ξ₂ ↑ᴿ _}))
          (cong (λ z → x [ z ]ᴿ) (lift-dist-compᴿᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂}))

  -- ══ Vᴿ. monad laws, renaming world ═══════════════════════════════
  right-idᴿ : ∀ (x/t : S ⊢[ m ] s) → x/t [ idᴿ ]ᴿ ≡ x/t
  right-idᴿ zero    = refl
  right-idᴿ (suc x) = lookup-idᴿ (suc x)
  right-idᴿ (`_ x)   = cong `_ (lookup-idᴿ x)
  right-idᴿ (λx_ expr0)           = cong1 λx_ (trans (cong (expr0 [_]ᴿ) lift-idᴿ) (right-idᴿ expr0))
  right-idᴿ (Λα_ expr0)           = cong1 Λα_ (trans (cong (expr0 [_]ᴿ) lift-idᴿ) (right-idᴿ expr0))
  right-idᴿ (∀[α∶_]_ kind0 type0) = cong2 ∀[α∶_]_ (right-idᴿ kind0) (trans (cong (type0 [_]ᴿ) lift-idᴿ) (right-idᴿ type0))
  right-idᴿ (_·_ expr0 expr1)     = cong2 _·_ (right-idᴿ expr0) (right-idᴿ expr1)
  right-idᴿ (_•_ expr0 type0)     = cong2 _•_ (right-idᴿ expr0) (right-idᴿ type0)
  right-idᴿ (_⇒_ type0 type1)     = cong2 _⇒_ (right-idᴿ type0) (right-idᴿ type1)
  right-idᴿ *                     = refl

  -- T-only.  Its V-instance is compositionalityᴿᴿ-var read backwards, and
  -- registering both loops: this rule folds (x [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ into
  -- x [ ξ₁ ⨟ᴿ ξ₂ ]ᴿ and compositionalityᴿᴿ-var pushes it straight back.
  compositionalityᴿᴿ : ∀ (t : S₁ ⊢ s) {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    (t [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ ≡ t [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ
  compositionalityᴿᴿ (`_ x) {ξ₁ = ξ₁} {ξ₂ = ξ₂} = cong `_ (sym (compositionalityᴿᴿ-var x {ξ₁ = ξ₁} {ξ₂ = ξ₂}))
  compositionalityᴿᴿ (λx_ expr0)           = cong1 λx_ (trans (compositionalityᴿᴿ expr0) (cong (expr0 [_]ᴿ) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (Λα_ expr0)           = cong1 Λα_ (trans (compositionalityᴿᴿ expr0) (cong (expr0 [_]ᴿ) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (∀[α∶_]_ kind0 type0) = cong2 ∀[α∶_]_ (compositionalityᴿᴿ kind0) (trans (compositionalityᴿᴿ type0) (cong (type0 [_]ᴿ) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (_·_ expr0 expr1)     = cong2 _·_ (compositionalityᴿᴿ expr0) (compositionalityᴿᴿ expr1)
  compositionalityᴿᴿ (_•_ expr0 type0)     = cong2 _•_ (compositionalityᴿᴿ expr0) (compositionalityᴿᴿ type0)
  compositionalityᴿᴿ (_⇒_ type0 type1)     = cong2 _⇒_ (compositionalityᴿᴿ type0) (compositionalityᴿᴿ type1)
  compositionalityᴿᴿ *                     = refl

  -- ─── the substitution world ───────────────────────────────────────

  ⟨⟩-⨟ˢᴿ-wk : ∀ (ξ : S₁ →ᴿ S₂) → ⟨ ξ ⟩ ⨟ˢᴿ wkᴿ s ≡ ⟨ wk*ᴿ s ξ ⟩
  ⟨⟩-⨟ˢᴿ-wk []       = refl
  ⟨⟩-⨟ˢᴿ-wk (x ∙ᴿ ξ) = cong2 _∙ˢ_ (cong `_ def-wkᴿ) (⟨⟩-⨟ˢᴿ-wk ξ)

  ⟨⟩-lift : (⟨ ξ ⟩ ↑ˢ s) ≡ ⟨ ξ ↑ᴿ s ⟩
  ⟨⟩-lift {ξ = ξ} = cong ((`_ zero) ∙ˢ_) (⟨⟩-⨟ˢᴿ-wk ξ)

  coincidence-var : ∀ (x : S₁ ∋ s) (ξ : S₁ →ᴿ S₂) → x [ ⟨ ξ ⟩ ]ˢ ≡ `_ (x [ ξ ]ᴿ)
  coincidence-var zero    (y ∙ᴿ ξ) = refl
  coincidence-var (suc x) (y ∙ᴿ ξ) = coincidence-var x ξ

  coincidence : ∀ (t : S₁ ⊢ s) (ξ : S₁ →ᴿ S₂) → t [ ⟨ ξ ⟩ ]ˢ ≡ t [ ξ ]ᴿ
  coincidence (`_ x) ξ = coincidence-var x ξ
  coincidence (λx_ expr0) ξ           = cong1 λx_ (trans (cong (expr0 [_]ˢ) (⟨⟩-lift {ξ = ξ})) (coincidence expr0 (ξ ↑ᴿ expr)))
  coincidence (Λα_ expr0) ξ           = cong1 Λα_ (trans (cong (expr0 [_]ˢ) (⟨⟩-lift {ξ = ξ})) (coincidence expr0 (ξ ↑ᴿ type)))
  coincidence (∀[α∶_]_ kind0 type0) ξ = cong2 ∀[α∶_]_ (coincidence kind0 ξ) (trans (cong (type0 [_]ˢ) (⟨⟩-lift {ξ = ξ})) (coincidence type0 (ξ ↑ᴿ type)))
  coincidence (_·_ expr0 expr1) ξ     = cong2 _·_ (coincidence expr0 ξ) (coincidence expr1 ξ)
  coincidence (_•_ expr0 type0) ξ     = cong2 _•_ (coincidence expr0 ξ) (coincidence type0 ξ)
  coincidence (_⇒_ type0 type1) ξ     = cong2 _⇒_ (coincidence type0 ξ) (coincidence type1 ξ)
  coincidence * ξ                     = refl

  ⨟ˢᴿ-def : ∀ (σ : S₁ →ˢ S₂) (ξ : S₂ →ᴿ S₃) → σ ⨟ˢᴿ ξ ≡ σ ⨟ ⟨ ξ ⟩
  ⨟ˢᴿ-def []       ξ = refl
  ⨟ˢᴿ-def (t ∙ˢ σ) ξ = cong2 _∙ˢ_ (sym (coincidence t ξ)) (⨟ˢᴿ-def σ ξ)

  -- ══ Iˢ. applied rules, substitution world ════════════════════════
  def-∙ˢ-zero : zero [ (t ∙ˢ σ) ]ˢ ≡ t
  def-∙ˢ-zero = refl

  def-∙ˢ-suc : (suc {s′ = s′} x) [ (t ∙ˢ σ) ]ˢ ≡ x [ σ ]ˢ
  def-∙ˢ-suc = refl

  def-↑ˢ-zero : zero [ (σ ↑ˢ s) ]ˢ ≡ `_ zero
  def-↑ˢ-zero = refl

  def-↑ˢ-suc : (suc x) [ (σ ↑ˢ s) ]ˢ ≡ x [ (σ ⨟ ⟨ wkᴿ s ⟩) ]ˢ
  def-↑ˢ-suc {x = x} {σ = σ} {s = s} = cong (x [_]ˢ) (⨟ˢᴿ-def σ (wkᴿ s))

  -- ══ lookup through the two hybrid compositions ═══════════════════
  lookup-⨟ˢᴿ : ∀ (x : S₁ ∋ s) (σ : S₁ →ˢ S₂) (ξ : S₂ →ᴿ S₃) →
    x [ σ ⨟ˢᴿ ξ ]ˢ ≡ (x [ σ ]ˢ) [ ξ ]ᴿ
  lookup-⨟ˢᴿ zero    (t ∙ˢ σ) ξ = refl
  lookup-⨟ˢᴿ (suc x) (t ∙ˢ σ) ξ = lookup-⨟ˢᴿ x σ ξ

  lookup-⨟ˢ : ∀ (x : S₁ ∋ s) (σ₁ : S₁ →ˢ S₂) (σ₂ : S₂ →ˢ S₃) →
    x [ σ₁ ⨟ σ₂ ]ˢ ≡ (x [ σ₁ ]ˢ) [ σ₂ ]ˢ
  lookup-⨟ˢ zero    (t ∙ˢ σ₁) σ₂ = refl
  lookup-⨟ˢ (suc x) (t ∙ˢ σ₁) σ₂ = lookup-⨟ˢ x σ₁ σ₂

  -- ══ IIIˢ/IVˢ. map algebra and lifting, substitution world ════════
  dist : (t ∙ˢ σ₁) ⨟ σ₂ ≡ (t [ σ₂ ]ˢ) ∙ˢ (σ₁ ⨟ σ₂)
  dist = refl

  ⟨wk*⟩-cons : ∀ (ξ : S₁ →ᴿ S₂) (t : S₃ ⊢ s′) (σ : S₂ →ˢ S₃) →
    ⟨ wk*ᴿ s′ ξ ⟩ ⨟ (t ∙ˢ σ) ≡ ⟨ ξ ⟩ ⨟ σ
  ⟨wk*⟩-cons []       t σ = refl
  ⟨wk*⟩-cons (x ∙ᴿ ξ) t σ = cong (_ ∙ˢ_) (⟨wk*⟩-cons ξ t σ)

  comp-idₗ : ⟨ idᴿ {S₁} ⟩ ⨟ σ ≡ σ
  comp-idₗ {σ = []}     = refl
  comp-idₗ {σ = t ∙ˢ σ} = cong (t ∙ˢ_) (trans (⟨wk*⟩-cons idᴿ t σ) comp-idₗ)

  interact : ⟨ wkᴿ s ⟩ ⨟ (t ∙ˢ σ) ≡ σ
  interact {t = t} {σ = σ} = trans (⟨wk*⟩-cons idᴿ t σ) comp-idₗ

  ⟨wk*⟩-lift : ∀ (ξ : S₁ →ᴿ S₂) (σ : S₂ →ˢ S₃) →
    ⟨ wk*ᴿ s ξ ⟩ ⨟ (σ ↑ˢ s) ≡ (⟨ ξ ⟩ ⨟ σ) ⨟ˢᴿ wkᴿ s
  ⟨wk*⟩-lift []       σ = refl
  ⟨wk*⟩-lift (x ∙ᴿ ξ) σ = cong2 _∙ˢ_ (lookup-⨟ˢᴿ x σ (wkᴿ _)) (⟨wk*⟩-lift ξ σ)

  lift-dist-compᴿˢ : ⟨ ξ ↑ᴿ s ⟩ ⨟ (σ ↑ˢ s) ≡ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ s)
  lift-dist-compᴿˢ {ξ = ξ} {σ = σ} = cong ((`_ zero) ∙ˢ_) (⟨wk*⟩-lift ξ σ)

  -- ══ the mixed compositionality laws, stratified ══════════════════
  -- the variable instance, kept separate: registering it alongside a
  -- mode-generic compositionalityᴿˢ would loop, since at mode V the two
  -- are inverse.  At V everything pushes, at T everything folds.
  compositionalityᴿˢ-var : ∀ (x : S₁ ∋ s) {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    (x [ ξ ]ᴿ) [ σ ]ˢ ≡ x [ (⟨ ξ ⟩ ⨟ σ) ]ˢ
  compositionalityᴿˢ-var zero    {ξ = y ∙ᴿ ξ} = refl
  compositionalityᴿˢ-var (suc x) {ξ = y ∙ᴿ ξ} = compositionalityᴿˢ-var x

  -- T-only, for the same reason compositionalityᴿᴿ is.
  compositionalityᴿˢ : ∀ (t : S₁ ⊢ s) {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    (t [ ξ ]ᴿ) [ σ ]ˢ ≡ t [ (⟨ ξ ⟩ ⨟ σ) ]ˢ
  compositionalityᴿˢ (`_ x) = compositionalityᴿˢ-var x
  compositionalityᴿˢ (λx_ expr0)           = cong1 λx_ (trans (compositionalityᴿˢ expr0) (cong (expr0 [_]ˢ) lift-dist-compᴿˢ))
  compositionalityᴿˢ (Λα_ expr0)           = cong1 Λα_ (trans (compositionalityᴿˢ expr0) (cong (expr0 [_]ˢ) lift-dist-compᴿˢ))
  compositionalityᴿˢ (∀[α∶_]_ kind0 type0) = cong2 ∀[α∶_]_ (compositionalityᴿˢ kind0) (trans (compositionalityᴿˢ type0) (cong (type0 [_]ˢ) lift-dist-compᴿˢ))
  compositionalityᴿˢ (_·_ expr0 expr1)     = cong2 _·_ (compositionalityᴿˢ expr0) (compositionalityᴿˢ expr1)
  compositionalityᴿˢ (_•_ expr0 type0)     = cong2 _•_ (compositionalityᴿˢ expr0) (compositionalityᴿˢ type0)
  compositionalityᴿˢ (_⇒_ type0 type1)     = cong2 _⇒_ (compositionalityᴿˢ type0) (compositionalityᴿˢ type1)
  compositionalityᴿˢ *                     = refl

  ⨟ˢᴿ-lift : ∀ (σ : S₁ →ˢ S₂) (ξ : S₂ →ᴿ S₃) →
    (σ ⨟ˢᴿ wkᴿ s) ⨟ˢᴿ (ξ ↑ᴿ s) ≡ (σ ⨟ˢᴿ ξ) ⨟ˢᴿ wkᴿ s
  ⨟ˢᴿ-lift []       ξ = refl
  ⨟ˢᴿ-lift (t ∙ˢ σ) ξ = cong2 _∙ˢ_
    (trans (compositionalityᴿᴿ t) (trans (cong (t [_]ᴿ) lift-wkᴿ) (sym (compositionalityᴿᴿ t))))
    (⨟ˢᴿ-lift σ ξ)

  lift-⨟ˢᴿ : ∀ {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
    (σ ↑ˢ s) ⨟ˢᴿ (ξ ↑ᴿ s) ≡ ((σ ⨟ˢᴿ ξ) ↑ˢ s)
  lift-⨟ˢᴿ {σ = σ} {ξ = ξ} = cong ((`_ zero) ∙ˢ_) (⨟ˢᴿ-lift σ ξ)

  compositionalityˢᴿ′ : ∀ (x/t : S₁ ⊢[ m ] s) {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
    (x/t [ σ ]ˢ) [ ξ ]ᴿ ≡ x/t [ (σ ⨟ˢᴿ ξ) ]ˢ
  compositionalityˢᴿ′ zero    {σ = t ∙ˢ σ} = refl
  compositionalityˢᴿ′ (suc x) {σ = t ∙ˢ σ} = compositionalityˢᴿ′ x
  compositionalityˢᴿ′ (`_ x) = compositionalityˢᴿ′ x
  compositionalityˢᴿ′ (λx_ expr0)           = cong1 λx_ (trans (compositionalityˢᴿ′ expr0) (cong (expr0 [_]ˢ) lift-⨟ˢᴿ))
  compositionalityˢᴿ′ (Λα_ expr0)           = cong1 Λα_ (trans (compositionalityˢᴿ′ expr0) (cong (expr0 [_]ˢ) lift-⨟ˢᴿ))
  compositionalityˢᴿ′ (∀[α∶_]_ kind0 type0) = cong2 ∀[α∶_]_ (compositionalityˢᴿ′ kind0) (trans (compositionalityˢᴿ′ type0) (cong (type0 [_]ˢ) lift-⨟ˢᴿ))
  compositionalityˢᴿ′ (_·_ expr0 expr1)     = cong2 _·_ (compositionalityˢᴿ′ expr0) (compositionalityˢᴿ′ expr1)
  compositionalityˢᴿ′ (_•_ expr0 type0)     = cong2 _•_ (compositionalityˢᴿ′ expr0) (compositionalityˢᴿ′ type0)
  compositionalityˢᴿ′ (_⇒_ type0 type1)     = cong2 _⇒_ (compositionalityˢᴿ′ type0) (compositionalityˢᴿ′ type1)
  compositionalityˢᴿ′ *                     = refl

  compositionalityˢᴿ : ∀ (x/t : S₁ ⊢[ m ] s) {σ₁ : S₁ →ˢ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    (x/t [ σ₁ ]ˢ) [ ξ₂ ]ᴿ ≡ x/t [ (σ₁ ⨟ ⟨ ξ₂ ⟩) ]ˢ
  compositionalityˢᴿ x/t {σ₁ = σ} {ξ₂ = ξ} =
    trans (compositionalityˢᴿ′ x/t) (cong (x/t [_]ˢ) (⨟ˢᴿ-def σ ξ))

  lift-dist-compˢᴿ : ∀ {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
    ((σ ↑ˢ s) ⨟ ⟨ ξ ↑ᴿ s ⟩) ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s)
  lift-dist-compˢᴿ {σ = σ} {ξ = ξ} =
    trans (sym (⨟ˢᴿ-def (σ ↑ˢ _) (ξ ↑ᴿ _)))
          (trans lift-⨟ˢᴿ (cong (_↑ˢ _) (⨟ˢᴿ-def σ ξ)))

  lift-wk : ⟨ wkᴿ s ⟩ ⨟ (σ ↑ˢ s) ≡ σ ⨟ ⟨ wkᴿ s ⟩
  lift-wk {s = s} {σ = σ} = trans (⟨wk*⟩-lift idᴿ σ)
    (trans (cong (_⨟ˢᴿ wkᴿ s) comp-idₗ) (⨟ˢᴿ-def σ (wkᴿ s)))

  ⨟ˢᴿwk-lift : ∀ (σ₁ : S₁ →ˢ S₂) (σ₂ : S₂ →ˢ S₃) →
    (σ₁ ⨟ˢᴿ wkᴿ s) ⨟ (σ₂ ↑ˢ s) ≡ (σ₁ ⨟ σ₂) ⨟ˢᴿ wkᴿ s
  ⨟ˢᴿwk-lift []       σ₂ = refl
  ⨟ˢᴿwk-lift {s = s} (t ∙ˢ σ₁) σ₂ = cong2 _∙ˢ_
    (trans (compositionalityᴿˢ t)
      (trans (cong (t [_]ˢ) (trans lift-wk (sym (⨟ˢᴿ-def σ₂ (wkᴿ s)))))
             (sym (compositionalityˢᴿ′ t))))
    (⨟ˢᴿwk-lift σ₁ σ₂)

  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = cong ((`_ zero) ∙ˢ_) (⨟ˢᴿwk-lift σ₁ σ₂)

  -- ══ Vˢ. monad laws, substitution world ═══════════════════════════
  compositionalityˢˢ : ∀ (x/t : S₁ ⊢[ m ] s) {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} →
    (x/t [ σ₁ ]ˢ) [ σ₂ ]ˢ ≡ x/t [ (σ₁ ⨟ σ₂) ]ˢ
  compositionalityˢˢ zero    {σ₁ = t ∙ˢ σ₁} = refl
  compositionalityˢˢ (suc x) {σ₁ = t ∙ˢ σ₁} = compositionalityˢˢ x
  compositionalityˢˢ (`_ x) = compositionalityˢˢ x
  compositionalityˢˢ (λx_ expr0)           = cong1 λx_ (trans (compositionalityˢˢ expr0) (cong (expr0 [_]ˢ) lift-dist-compˢˢ))
  compositionalityˢˢ (Λα_ expr0)           = cong1 Λα_ (trans (compositionalityˢˢ expr0) (cong (expr0 [_]ˢ) lift-dist-compˢˢ))
  compositionalityˢˢ (∀[α∶_]_ kind0 type0) = cong2 ∀[α∶_]_ (compositionalityˢˢ kind0) (trans (compositionalityˢˢ type0) (cong (type0 [_]ˢ) lift-dist-compˢˢ))
  compositionalityˢˢ (_·_ expr0 expr1)     = cong2 _·_ (compositionalityˢˢ expr0) (compositionalityˢˢ expr1)
  compositionalityˢˢ (_•_ expr0 type0)     = cong2 _•_ (compositionalityˢˢ expr0) (compositionalityˢˢ type0)
  compositionalityˢˢ (_⇒_ type0 type1)     = cong2 _⇒_ (compositionalityˢˢ type0) (compositionalityˢˢ type1)
  compositionalityˢˢ *                     = refl

  assoc : (σ₁ ⨟ σ₂) ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)
  assoc {σ₁ = []}      = refl
  assoc {σ₁ = t ∙ˢ σ₁} = cong2 _∙ˢ_ (compositionalityˢˢ t) assoc

  comp-idᵣ : σ ⨟ ⟨ idᴿ ⟩ ≡ σ
  comp-idᵣ {σ = []}     = refl
  comp-idᵣ {σ = t ∙ˢ σ} = cong2 _∙ˢ_ (trans (coincidence t idᴿ) (right-idᴿ t)) comp-idᵣ

  ⨟ˢᴿwk-cons : ∀ (σ : S₁ →ˢ S₂) (t : S₃ ⊢ s) (τ : S₂ →ˢ S₃) →
    (σ ⨟ˢᴿ wkᴿ s) ⨟ (t ∙ˢ τ) ≡ σ ⨟ τ
  ⨟ˢᴿwk-cons []       t τ = refl
  ⨟ˢᴿwk-cons (u ∙ˢ σ) t τ =
    cong2 _∙ˢ_ (trans (compositionalityᴿˢ u) (cong (u [_]ˢ) interact)) (⨟ˢᴿwk-cons σ t τ)

  lift-cons : (σ ↑ˢ s) ⨟ (t ∙ˢ τ) ≡ t ∙ˢ (σ ⨟ τ)
  lift-cons {σ = σ} {t = t} {τ = τ} = cong (t ∙ˢ_) (⨟ˢᴿwk-cons σ t τ)

  -- ══ the collapse family: ⟨_⟩ is pushed back into the ᴿ world ═════
  ⟨⟩-comp : ⟨ ξ₁ ⟩ ⨟ ⟨ ξ₂ ⟩ ≡ ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩
  ⟨⟩-comp {ξ₁ = []}      = refl
  ⟨⟩-comp {ξ₁ = x ∙ᴿ ξ₁} {ξ₂ = ξ₂} = cong2 _∙ˢ_ (coincidence-var x ξ₂) ⟨⟩-comp

  ⟨⟩-split-⨟ : ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩ ⨟ σ ≡ ⟨ ξ₁ ⟩ ⨟ (⟨ ξ₂ ⟩ ⨟ σ)
  ⟨⟩-split-⨟ {ξ₁ = []}      = refl
  ⟨⟩-split-⨟ {ξ₁ = x ∙ᴿ ξ₁} = cong2 _∙ˢ_ (compositionalityᴿˢ-var x) ⟨⟩-split-⨟

  ⟨⟩-lift-cons : ⟨ ξ ↑ᴿ s ⟩ ⨟ (t ∙ˢ σ) ≡ t ∙ˢ (⟨ ξ ⟩ ⨟ σ)
  ⟨⟩-lift-cons {ξ = ξ} {t = t} {σ = σ} = cong (t ∙ˢ_) (⟨wk*⟩-cons ξ t σ)


  -- ══ VIˢ. completion companions, substitution world ═══════════════
  lift-wk-⨟ : ∀ {σ : S₁ →ˢ S₂} {τ : (s ∷ S₂) →ˢ S₃} →
    ⟨ wkᴿ s ⟩ ⨟ ((σ ↑ˢ s) ⨟ τ) ≡ σ ⨟ (⟨ wkᴿ s ⟩ ⨟ τ)
  lift-wk-⨟ {σ = σ} {τ = τ} =
    trans (sym (assoc {σ₁ = ⟨ wkᴿ _ ⟩} {σ₂ = σ ↑ˢ _} {σ₃ = τ}))
          (trans (cong (_⨟ τ) (lift-wk {σ = σ}))
                 (assoc {σ₁ = σ} {σ₂ = ⟨ wkᴿ _ ⟩} {σ₃ = τ}))

  lift-dist-compˢˢ-⨟ : ∀ {S₄ : Scope} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃}
    {τ : (s ∷ S₃) →ˢ S₄} →
    (σ₁ ↑ˢ s) ⨟ ((σ₂ ↑ˢ s) ⨟ τ) ≡ ((σ₁ ⨟ σ₂) ↑ˢ s) ⨟ τ
  lift-dist-compˢˢ-⨟ {σ₁ = σ₁} {σ₂ = σ₂} {τ = τ} =
    trans (sym (assoc {σ₁ = σ₁ ↑ˢ _} {σ₂ = σ₂ ↑ˢ _} {σ₃ = τ}))
          (cong (_⨟ τ) (lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂}))

  lift-dist-compᴿˢ-⨟ : ∀ {S₄ : Scope} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃}
    {τ : (s ∷ S₃) →ˢ S₄} →
    ⟨ ξ ↑ᴿ s ⟩ ⨟ ((σ ↑ˢ s) ⨟ τ) ≡ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ s) ⨟ τ
  lift-dist-compᴿˢ-⨟ {ξ = ξ} {σ = σ} {τ = τ} =
    trans (sym (assoc {σ₁ = ⟨ ξ ↑ᴿ _ ⟩} {σ₂ = σ ↑ˢ _} {σ₃ = τ}))
          (cong (_⨟ τ) (lift-dist-compᴿˢ {ξ = ξ} {σ = σ}))

  lift-dist-compˢᴿ-⨟ : ∀ {S₄ : Scope} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃}
    {τ : (s ∷ S₃) →ˢ S₄} →
    (σ ↑ˢ s) ⨟ (⟨ ξ ↑ᴿ s ⟩ ⨟ τ) ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s) ⨟ τ
  lift-dist-compˢᴿ-⨟ {σ = σ} {ξ = ξ} {τ = τ} =
    trans (sym (assoc {σ₁ = σ ↑ˢ _} {σ₂ = ⟨ ξ ↑ᴿ _ ⟩} {σ₃ = τ}))
          (cong (_⨟ τ) (lift-dist-compˢᴿ {σ = σ} {ξ = ξ}))

  ⟨⟩-comp-⨟-interactᴿ : ∀ {ξ : S₁ →ᴿ S₂} {x : S₂ ∋ s} {τ : S₂ →ˢ S₃} →
    ⟨ wkᴿ s ⟩ ⨟ (⟨ x ∙ᴿ ξ ⟩ ⨟ τ) ≡ ⟨ ξ ⟩ ⨟ τ
  ⟨⟩-comp-⨟-interactᴿ {ξ = ξ} {x = x} {τ = τ} =
    trans (sym (assoc {σ₁ = ⟨ wkᴿ _ ⟩} {σ₂ = ⟨ x ∙ᴿ ξ ⟩} {σ₃ = τ}))
          (trans (cong (_⨟ τ) (⟨⟩-comp {ξ₁ = wkᴿ _} {ξ₂ = x ∙ᴿ ξ}))
                 (cong (λ z → ⟨ z ⟩ ⨟ τ) (interactᴿ {x = x} {ξ = ξ})))

  ⟨⟩-comp-⨟-lift-wkᴿ : ∀ {S₄ : Scope} {ξ : S₁ →ᴿ S₂} {τ : (s ∷ S₂) →ˢ S₄} →
    ⟨ wkᴿ s ⟩ ⨟ (⟨ ξ ↑ᴿ s ⟩ ⨟ τ) ≡ ⟨ ξ ⟩ ⨟ (⟨ wkᴿ s ⟩ ⨟ τ)
  ⟨⟩-comp-⨟-lift-wkᴿ {ξ = ξ} {τ = τ} =
    trans (sym (assoc {σ₁ = ⟨ wkᴿ _ ⟩} {σ₂ = ⟨ ξ ↑ᴿ _ ⟩} {σ₃ = τ}))
          (trans (cong (_⨟ τ) (⟨⟩-comp {ξ₁ = wkᴿ _} {ξ₂ = ξ ↑ᴿ _}))
          (trans (cong (λ z → ⟨ z ⟩ ⨟ τ) (lift-wkᴿ {ξ = ξ}))
          (trans (cong (_⨟ τ) (sym (⟨⟩-comp {ξ₁ = ξ} {ξ₂ = wkᴿ _})))
                 (assoc {σ₁ = ⟨ ξ ⟩} {σ₂ = ⟨ wkᴿ _ ⟩} {σ₃ = τ}))))

  ⟨⟩-comp-⨟-lift-dist-compᴿᴿ : ∀ {S₄ : Scope} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃}
    {τ : (s ∷ S₃) →ˢ S₄} →
    ⟨ ξ₁ ↑ᴿ s ⟩ ⨟ (⟨ ξ₂ ↑ᴿ s ⟩ ⨟ τ) ≡ ⟨ (ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s ⟩ ⨟ τ
  ⟨⟩-comp-⨟-lift-dist-compᴿᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂} {τ = τ} =
    trans (sym (assoc {σ₁ = ⟨ ξ₁ ↑ᴿ _ ⟩} {σ₂ = ⟨ ξ₂ ↑ᴿ _ ⟩} {σ₃ = τ}))
          (trans (cong (_⨟ τ) (⟨⟩-comp {ξ₁ = ξ₁ ↑ᴿ _} {ξ₂ = ξ₂ ↑ᴿ _}))
                 (cong (λ z → ⟨ z ⟩ ⨟ τ) (lift-dist-compᴿᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂})))

  ⟨⟩-split-tail : ∀ {S₄ : Scope} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃}
    {ξ′ : (s ∷ S₃) →ᴿ S₄} →
    (σ ↑ˢ s) ⨟ ⟨ (ξ ↑ᴿ s) ⨟ᴿ ξ′ ⟩ ≡ ((σ ⨟ ⟨ ξ ⟩) ↑ˢ s) ⨟ ⟨ ξ′ ⟩
  ⟨⟩-split-tail {σ = σ} {ξ = ξ} {ξ′ = ξ′} =
    trans (cong ((σ ↑ˢ _) ⨟_) (sym (⟨⟩-comp {ξ₁ = ξ ↑ᴿ _} {ξ₂ = ξ′})))
          (trans (sym (assoc {σ₁ = σ ↑ˢ _} {σ₂ = ⟨ ξ ↑ᴿ _ ⟩} {σ₃ = ⟨ ξ′ ⟩}))
                 (cong (_⨟ ⟨ ξ′ ⟩) (lift-dist-compˢᴿ {σ = σ} {ξ = ξ})))

  compositionalityᴿˢ-⨟-var : ∀ {x : S₁ ∋ s} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    x [ (⟨ ξ ⟩ ⨟ σ) ]ˢ ≡ (x [ ξ ]ᴿ) [ σ ]ˢ
  compositionalityᴿˢ-⨟-var {x = x} = sym (compositionalityᴿˢ-var x)

  lift-dist-compᴿˢ-var : ∀ {x : (s ∷ S₁) ∋ s′} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    (x [ (ξ ↑ᴿ s) ]ᴿ) [ (σ ↑ˢ s) ]ˢ ≡ x [ ((⟨ ξ ⟩ ⨟ σ) ↑ˢ s) ]ˢ
  lift-dist-compᴿˢ-var {x = x} {ξ = ξ} {σ = σ} =
    trans (compositionalityᴿˢ-var x)
          (cong (λ z → x [ z ]ˢ) (lift-dist-compᴿˢ {ξ = ξ} {σ = σ}))

  lift-dist-compᴿˢ-⨟-var : ∀ {S₄ : Scope} {x : (s ∷ S₁) ∋ s′} {ξ : S₁ →ᴿ S₂}
    {σ : S₂ →ˢ S₃} {τ : (s ∷ S₃) →ˢ S₄} →
    (x [ (ξ ↑ᴿ s) ]ᴿ) [ ((σ ↑ˢ s) ⨟ τ) ]ˢ ≡ x [ (((⟨ ξ ⟩ ⨟ σ) ↑ˢ s) ⨟ τ) ]ˢ
  lift-dist-compᴿˢ-⨟-var {x = x} {ξ = ξ} {σ = σ} {τ = τ} =
    trans (compositionalityᴿˢ-var x)
          (trans (cong (λ z → x [ z ]ˢ)
                       (sym (assoc {σ₁ = ⟨ ξ ↑ᴿ _ ⟩} {σ₂ = σ ↑ˢ _} {σ₃ = τ})))
                 (cong (λ z → x [ (z ⨟ τ) ]ˢ) (lift-dist-compᴿˢ {ξ = ξ} {σ = σ})))

  ⟨⟩-lift-cons-var : ∀ {x : (s ∷ S₁) ∋ s′} {ξ : S₁ →ᴿ S₂} {t : S₃ ⊢ s}
    {σ : S₂ →ˢ S₃} →
    (x [ (ξ ↑ᴿ s) ]ᴿ) [ (t ∙ˢ σ) ]ˢ ≡ x [ (t ∙ˢ (⟨ ξ ⟩ ⨟ σ)) ]ˢ
  ⟨⟩-lift-cons-var {x = x} {ξ = ξ} {t = t} {σ = σ} =
    trans (compositionalityᴿˢ-var x)
          (cong (λ z → x [ z ]ˢ) (⟨⟩-lift-cons {ξ = ξ} {t = t} {σ = σ}))

  def-↑ˢ-zero-⨟ : ∀ {σ : S₁ →ˢ S₂} {τ : (s ∷ S₂) →ˢ S₃} →
    zero [ ((σ ↑ˢ s) ⨟ τ) ]ˢ ≡ zero [ τ ]ˢ
  def-↑ˢ-zero-⨟ {σ = σ} {τ = τ} = lookup-⨟ˢ zero (σ ↑ˢ _) τ

  def-↑ˢ-suc-⨟ : ∀ {x : S₁ ∋ s′} {σ : S₁ →ˢ S₂} {τ : (s ∷ S₂) →ˢ S₃} →
    (suc x) [ ((σ ↑ˢ s) ⨟ τ) ]ˢ ≡ x [ (σ ⨟ (⟨ wkᴿ s ⟩ ⨟ τ)) ]ˢ
  def-↑ˢ-suc-⨟ {x = x} {σ = σ} {τ = τ} =
    trans (lookup-⨟ˢ (suc x) (σ ↑ˢ _) τ)
          (trans (cong (_[ τ ]ˢ) (def-↑ˢ-suc {x = x} {σ = σ}))
                 (trans (sym (lookup-⨟ˢ x (σ ⨟ ⟨ wkᴿ _ ⟩) τ))
                        (cong (x [_]ˢ) (assoc {σ₁ = σ} {σ₂ = ⟨ wkᴿ _ ⟩} {σ₃ = τ}))))

  lift-id : (⟨ idᴿ {S} ⟩ ↑ˢ s) ≡ ⟨ idᴿ ⟩
  lift-id = ⟨⟩-lift



  -- ══ IIˢ. traversal rules, substitution world ═════════════════════
  inst-var : (`_ x) [ σ ]ˢ ≡ x [ σ ]ˢ
  inst-λx_     : (λx_ expr0) [ σ ]ˢ           ≡ λx_ (expr0 [ σ ↑ˢ expr ]ˢ)
  inst-Λα_     : (Λα_ expr0) [ σ ]ˢ           ≡ Λα_ (expr0 [ σ ↑ˢ type ]ˢ)
  inst-∀[α∶_]_ : (∀[α∶_]_ kind0 type0) [ σ ]ˢ ≡ ∀[α∶_]_ (kind0 [ σ ]ˢ) (type0 [ σ ↑ˢ type ]ˢ)
  inst-_·_     : (_·_ expr0 expr1) [ σ ]ˢ     ≡ _·_ (expr0 [ σ ]ˢ) (expr1 [ σ ]ˢ)
  inst-_•_     : (_•_ expr0 type0) [ σ ]ˢ     ≡ _•_ (expr0 [ σ ]ˢ) (type0 [ σ ]ˢ)
  inst-_⇒_     : (_⇒_ type0 type1) [ σ ]ˢ     ≡ _⇒_ (type0 [ σ ]ˢ) (type1 [ σ ]ˢ)
  inst-*       : * {S = S} [ σ ]ˢ             ≡ *
  inst-var = refl
  inst-λx_     = refl
  inst-Λα_     = refl
  inst-∀[α∶_]_ = refl
  inst-_·_     = refl
  inst-_•_     = refl
  inst-_⇒_     = refl
  inst-*       = refl
-- ═══ The completed two-world system ════════════════════════════════
--
-- The vector model needs no completion families: a vector composition
-- reduces structurally where a function composition is stuck.

-- 72 rules: 56 signature-independent, and 16 traversal rules, one
-- instᴿ-* and one inst-* per constructor plus the variable case.

{-# REWRITE
  def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-↑ᴿ-zero def-↑ᴿ-suc
  instᴿ-var instᴿ-λx_ instᴿ-Λα_ instᴿ-∀[α∶_]_ instᴿ-_·_ instᴿ-_•_ instᴿ-_⇒_
  instᴿ-*
  assocᴿ comp-idₗᴿ comp-idᵣᴿ interactᴿ
  lift-idᴿ lift-dist-compᴿᴿ lift-wkᴿ
  right-idᴿ compositionalityᴿᴿ-var compositionalityᴿᴿ
  lift-dist-compᴿᴿ-var interactᴿ-⨟ᴿ lift-wkᴿ-⨟ᴿ lift-dist-compᴿᴿ-⨟ᴿ
  coincidence-var def-∙ˢ-zero def-∙ˢ-suc def-↑ˢ-zero def-↑ˢ-suc
  inst-var inst-λx_ inst-Λα_ inst-∀[α∶_]_ inst-_·_ inst-_•_ inst-_⇒_ inst-*
  assoc dist interact comp-idₗ comp-idᵣ
  lift-wk lift-cons lift-dist-compˢˢ lift-wk-⨟ lift-dist-compˢˢ-⨟
  compositionalityᴿˢ-⨟-var def-↑ˢ-zero-⨟ def-↑ˢ-suc-⨟
  compositionalityˢˢ compositionalityᴿˢ compositionalityˢᴿ
  lift-dist-compᴿˢ lift-dist-compˢᴿ lift-dist-compᴿˢ-⨟ lift-dist-compˢᴿ-⨟
  lift-dist-compᴿˢ-var lift-dist-compᴿˢ-⨟-var ⟨⟩-lift-cons-var
  ⟨⟩-comp-⨟-lift-wkᴿ ⟨⟩-comp-⨟-interactᴿ ⟨⟩-comp-⨟-lift-dist-compᴿᴿ ⟨⟩-split-tail
  coincidence ⟨⟩-comp ⟨⟩-split-⨟ ⟨⟩-lift ⟨⟩-lift-cons

#-}

-- ─── the derived operations ─────────────────────────────────────────
-- Neither is primitive and neither has rules of its own: weakening is a
-- renaming, single substitution is a cons onto the identity.  The
-- rewrite system computes through both without knowing they exist.

weaken : S ⊢ s → (s′ ∷ S) ⊢ s
weaken t = t [ wkᴿ _ ]ᴿ

_[_]₀ : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
t [ t′ ]₀ = t [ (t′ ∙ˢ idˢ) ]ˢ

-- ═══ The theory is definitional, in both worlds ════════════════════
-- The checks systemf.agda makes, verbatim.  Each is `refl` here too.

var-zero : ∀ {t′ : S ⊢ s′} → (` zero) [ t′ ]₀ ≡ t′
var-zero = refl
var-suc : ∀ {x : S ∋ s} {t′ : S ⊢ s′} → (` suc x) [ t′ ]₀ ≡ ` x
var-suc = refl
wk-cancel : ∀ {t : S ⊢ s} {t′ : S ⊢ s′} → (weaken t) [ t′ ]₀ ≡ t
wk-cancel = refl
wk-comm : ∀ {t : S₁ ⊢ s} {σ : S₁ →ˢ S₂} →
  (weaken {s′ = s′} t) [ (σ ↑ˢ s′) ]ˢ ≡ weaken (t [ σ ]ˢ)
wk-comm = refl
subst-commute : ∀ {t : (s′ ∷ S₁) ⊢ s} {t′ : S₁ ⊢ s′}
  {σ : S₁ →ˢ S₂} →
  (t [ (σ ↑ˢ s′) ]ˢ) [ t′ [ σ ]ˢ ]₀ ≡ (t [ t′ ]₀) [ σ ]ˢ
subst-commute = refl
subst-subst : ∀ {t : (s₁ ∷ s₂ ∷ S) ⊢ s} {t′ : (s₂ ∷ S) ⊢ s₁} {t₂ : S ⊢ s₂} →
  (t [ t′ ]₀) [ t₂ ]₀ ≡ (t [ ((t₂ ∙ˢ idˢ) ↑ˢ s₁) ]ˢ) [ t′ [ t₂ ]₀ ]₀
subst-subst = refl
lift-comp : ∀ {t : (s′ ∷ S₁) ⊢ s} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} →
  (t [ (σ₁ ↑ˢ s′) ]ˢ) [ (σ₂ ↑ˢ s′) ]ˢ ≡ t [ ((σ₁ ⨟ σ₂) ↑ˢ s′) ]ˢ
lift-comp = refl

renᴿ-id : ∀ {x/t : S ⊢[ m ] s} → x/t [ idᴿ ]ᴿ ≡ x/t
renᴿ-id = refl
renᴿ-comp : ∀ {t : S₁ ⊢ s} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
  (t [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ ≡ t [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ
renᴿ-comp = refl
renᴿ-lift : ∀ {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
  ((ξ₁ ↑ᴿ s) ⨟ᴿ (ξ₂ ↑ᴿ s)) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s)
renᴿ-lift = refl
mixed-RS : ∀ {t : S₁ ⊢ s} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
  (t [ ξ ]ᴿ) [ σ ]ˢ ≡ t [ (⟨ ξ ⟩ ⨟ σ) ]ˢ
mixed-RS = refl
mixed-SR : ∀ {t : S₁ ⊢ s} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
  (t [ σ ]ˢ) [ ξ ]ᴿ ≡ t [ (σ ⨟ ⟨ ξ ⟩) ]ˢ
mixed-SR = refl
emb-collapse : ∀ {t : S₁ ⊢ s} {ξ : S₁ →ᴿ S₂} → t [ ⟨ ξ ⟩ ]ˢ ≡ t [ ξ ]ᴿ
emb-collapse = refl

-- ═══ Typing and subject reduction ══════════════════════════════════
-- Copied from systemf.agda without a single change.

↑ˢᵗ_ : Sort → Sort
↑ˢᵗ expr = type
↑ˢᵗ type = kind
↑ˢᵗ kind = kind

_∶⊢_ : Scope → Sort → Set
S ∶⊢ s = S ⊢ (↑ˢᵗ s)

depth : S ∋ s → ℕ
depth zero    = zero
depth (suc x) = suc (depth x)

drop-∈ : S ∋ s → Scope → Scope
drop-∈ x S = drop (suc (depth x)) S

Ctx : Scope → Set
Ctx S = ∀ s → (x : S ∋ s) → drop-∈ x S ∶⊢ s

_∷ₜ_ : S ∶⊢ s → Ctx S → Ctx (s ∷ S)
(t ∷ₜ Γ) _ zero    = t
(t ∷ₜ Γ) _ (suc x) = Γ _ x

wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s′ → S ⊢ s′
wk-drop-∈ zero    t = weaken t
wk-drop-∈ (suc x) t = weaken (wk-drop-∈ x t)

wk-telescope : Ctx S → S ∋ s → S ∶⊢ s
wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

_∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

variable
  e e₁ e₂ e′ : S ⊢ expr
  k k′       : S ⊢ kind
  Γ Γ₁ Γ₂    : Ctx S

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  ⊢` : ∀ {x : S ∋ s} {t} →
    Γ ∋ x ∶ t →
    Γ ⊢ (` x) ∶ t
  ⊢λ :
    (t ∷ₜ Γ) ⊢ e ∶ (weaken t′) →
    Γ ⊢ (λx e) ∶ (t ⇒ t′)
  ⊢Λ :
    (k ∷ₜ Γ) ⊢ e ∶ t →
    Γ ⊢ (Λα e) ∶ (∀[α∶ k ] t)
  ⊢· :
    Γ ⊢ e₁ ∶ (t₁ ⇒ t₂) →
    Γ ⊢ e₂ ∶ t₁ →
    Γ ⊢ (e₁ · e₂) ∶ t₂
  ⊢• :
    Γ ⊢ e ∶ (∀[α∶ k ] t′) →
    Γ ⊢ t ∶ k →
    (k ∷ₜ Γ) ⊢ t′ ∶ k′ →
    Γ ⊢ (e • t) ∶ (t′ [ t ]₀)
  ⊢* : {t : S ⊢ type} →
    Γ ⊢ t ∶ *

-- one notion of well-typed map
_∶_→ˢ_ : S₁ →ˢ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ˢ_ {S₁} σ Γ₁ Γ₂ = ∀ s (x : S₁ ∋ s) (t : S₁ ∶⊢ s) →
  Γ₁ ∋ x ∶ t → Γ₂ ⊢ (x [ σ ]ˢ) ∶ (t [ σ ]ˢ)

-- Phase 1 of the preservation lemma.  With renamings first class this
-- is a plain judgment on ᴿ-maps: _[_]ᴿ preserves the mode, so a typed
-- renaming sends a variable to a variable by construction and ⊢` is a
-- direct application.  Without them phase 1 is a Σ-predicate on
-- substitutions and extracting the variable costs a transport.
_∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ᴿ_ {S₁} ξ Γ₁ Γ₂ = ∀ s (x : S₁ ∋ s) (t : S₁ ∶⊢ s) →
  Γ₁ ∋ x ∶ t → Γ₂ ∋ (x [ ξ ]ᴿ) ∶ (t [ ξ ]ᴿ)

⊢wkᴿ : (t′ : S ∶⊢ s′) → wkᴿ s′ ∶ Γ →ᴿ (t′ ∷ₜ Γ)
⊢wkᴿ t′ _ x _ refl = refl

⊢↑ᴿ : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} → ξ ∶ Γ₁ →ᴿ Γ₂ →
  (t : S₁ ∶⊢ s) → (ξ ↑ᴿ s) ∶ (t ∷ₜ Γ₁) →ᴿ ((t [ ξ ]ᴿ) ∷ₜ Γ₂)
⊢↑ᴿ ⊢ξ t _ zero    _ refl = refl
⊢↑ᴿ ⊢ξ t _ (suc x) _ refl = cong weaken (⊢ξ _ x _ refl)

ren-pres : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
  Γ₁ ⊢ e ∶ t → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (e [ ξ ]ᴿ) ∶ (t [ ξ ]ᴿ)
ren-pres (⊢` ⊢x) ⊢ξ = ⊢` (⊢ξ _ _ _ ⊢x)   -- no transport, no Σ
ren-pres (⊢λ ⊢e) ⊢ξ = ⊢λ (ren-pres ⊢e (⊢↑ᴿ ⊢ξ _))
ren-pres (⊢Λ ⊢e) ⊢ξ = ⊢Λ (ren-pres ⊢e (⊢↑ᴿ ⊢ξ _))
ren-pres (⊢· ⊢e₁ ⊢e₂) ⊢ξ = ⊢· (ren-pres ⊢e₁ ⊢ξ) (ren-pres ⊢e₂ ⊢ξ)
ren-pres (⊢• ⊢e ⊢t ⊢t′) ⊢ξ = ⊢• (ren-pres ⊢e ⊢ξ) (ren-pres ⊢t ⊢ξ) (ren-pres ⊢t′ (⊢↑ᴿ ⊢ξ _))
ren-pres ⊢*             ⊢ξ = ⊢*

-- phase 2: the entry typings go through ren-pres, so this stays structural
-- the binder cases pin the lifted σ: the goal's type index is already
-- rewritten, so it no longer determines σ by unification
sub-pres : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
  Γ₁ ⊢ e ∶ t → σ ∶ Γ₁ →ˢ Γ₂ →
  Γ₂ ⊢ (e [ σ ]ˢ) ∶ (t [ σ ]ˢ)
⊢↑ˢ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} →
  σ ∶ Γ₁ →ˢ Γ₂ → (t : S₁ ∶⊢ s) →
  (σ ↑ˢ s) ∶ (t ∷ₜ Γ₁) →ˢ ((t [ σ ]ˢ) ∷ₜ Γ₂)
⊢↑ˢ ⊢σ t _ zero    _ refl = ⊢` refl
⊢↑ˢ {σ = σ} ⊢σ t _ (suc x) _ refl = ren-pres (⊢σ _ x _ refl) (⊢wkᴿ (t [ σ ]ˢ))
sub-pres (⊢` ⊢x)                     ⊢σ = ⊢σ _ _ _ ⊢x
-- the induction hypothesis types the body at (weaken t′) [ σ ↑ˢ _ ]ˢ,
-- while ⊢λ demands weaken (t′ [ σ ]ˢ).  Discharged by wk-comm.
sub-pres {σ = σ} (⊢λ ⊢e)             ⊢σ = ⊢λ (sub-pres {σ = σ ↑ˢ _} ⊢e (⊢↑ˢ {σ = σ} ⊢σ _))
-- ⊢Λ and ⊢· use no substitution law: neither typing rule moves a
-- substitution past a binder in its conclusion.
sub-pres {σ = σ} (⊢Λ ⊢e)             ⊢σ = ⊢Λ (sub-pres {σ = σ ↑ˢ _} ⊢e (⊢↑ˢ {σ = σ} ⊢σ _))
sub-pres {σ = σ} (⊢· ⊢e₁ ⊢e₂)        ⊢σ = ⊢· (sub-pres {σ = σ} ⊢e₁ ⊢σ) (sub-pres {σ = σ} ⊢e₂ ⊢σ)
-- ⊢• concludes at t′ [ t ]₀, so the two sides are
-- (t′ [ σ ↑ˢ _ ]ˢ) [ t [ σ ]ˢ ]₀  and  (t′ [ t ]₀) [ σ ]ˢ.
-- Discharged by subst-commute.
sub-pres {σ = σ} (⊢• ⊢e ⊢t ⊢t′)      ⊢σ = ⊢• (sub-pres {σ = σ} ⊢e ⊢σ) (sub-pres {σ = σ} ⊢t ⊢σ)
                                         (sub-pres {σ = σ ↑ˢ _} ⊢t′ (⊢↑ˢ {σ = σ} ⊢σ _))
sub-pres ⊢*                          ⊢σ = ⊢*

⊢[] : ∀ {Γ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s} →
  Γ ⊢ e ∶ t → (e ∙ˢ idˢ) ∶ (t ∷ₜ Γ) →ˢ Γ
⊢[] ⊢e _ zero    _ refl = ⊢e
⊢[] ⊢e _ (suc x) _ refl = ⊢` refl

data Val : S ⊢ expr → Set where
  vλ : Val (λx e)
  vΛ : Val (Λα e)

data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  β-λ :
    Val e₂ →
    ((λx e₁) · e₂) ↪ (e₁ [ e₂ ]₀)
  β-Λ :
    ((Λα e) • t) ↪ (e [ t ]₀)
  ξ-·₁ :
    e₁ ↪ e →
    (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ :
    e₂ ↪ e →
    Val e₁ →
    (e₁ · e₂) ↪ (e₁ · e)
  ξ-• :
    e ↪ e′ →
    (e • t) ↪ (e′ • t)

-- the two β-cases pin σ explicitly: with the two-world rule set the
-- index of the goal has already been rewritten, so Agda can no longer
-- read σ back off  e [ σ ]ˢ ≟ e [ (v ]ˢ ∙ˢ idˢ)
sr : Γ ⊢ e ∶ t → e ↪ e′ → Γ ⊢ e′ ∶ t
-- ⊢λ stores the result type weakened, so the redex is typed at
-- (weaken t₂) [ e₂ ]₀ where the goal is t₂.  Discharged by wk-cancel.
sr (⊢· {e₂ = e₂} (⊢λ ⊢e₁) ⊢e₂) (β-λ v₂) =
  sub-pres {σ = e₂ ∙ˢ idˢ} ⊢e₁ (⊢[] ⊢e₂)
-- the type-application β-case uses no law: t′ [ t ]₀ is t′ [ t ∙ˢ idˢ ]ˢ.
sr (⊢• {t = t} (⊢Λ ⊢e) ⊢t ⊢t′) β-Λ =
  sub-pres {σ = t ∙ˢ idˢ} ⊢e (⊢[] ⊢t)
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ st)       = ⊢· (sr ⊢e₁ st) ⊢e₂
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ st v₁)    = ⊢· ⊢e₁ (sr ⊢e₂ st)
sr (⊢• ⊢e ⊢t ⊢t′) (ξ-• st)      = ⊢• (sr ⊢e st) ⊢t ⊢t′
