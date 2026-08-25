{-# OPTIONS --rewriting --local-confluence-check #-}

-- Multi-sorted, intrinsically scoped System F with FIRST-CLASS RENAMINGS,
-- and its σ-calculus as a locally confluent Agda REWRITE system, with maps
-- modeled as VECTORS (inductive data) rather than as functions.
--
-- Companion to systemf.agda, which is byte-for-byte the same development
-- over the function model.  Everything below the map definitions is meant
-- to read the same; the point of the file is that the user layer, the
-- typing rules and the subject-reduction proof are literally unchanged.
--
-- No funext.  Equality of vectors is equality of data.

module systemf-vec where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_; drop)
open import Data.Nat using (ℕ; zero; suc)

-- ─── syntax ─────────────────────────────────────────────────────────

data Sort : Set where
  expr type kind : Sort
Scope = List Sort

variable
  s s₁ s₂ s′ : Sort
  S S₁ S₂ S₃ S₄ : Scope

data Mode : Set where V T : Mode

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
  m          : Mode
  e e₁ e₂ e′ : S ⊢ expr
  k k′       : S ⊢ kind
  t t₁ t₂ t′ : S ⊢ s
  x x′ y     : S ∋ s
  x/t x/t′   : S ⊢[ m ] s

-- ─── maps as vectors ────────────────────────────────────────────────
-- One image per variable in the domain scope.  Extension is a
-- CONSTRUCTOR, so it is stuck by construction; every other operation is
-- an ordinary definition and therefore needs the same opacity the
-- function model needs.

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
  -- post-composition with weakening, the primitive recursion that lets
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

  _[_]ᴿ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → S₂ ⊢[ m ] s
  zero          [ x ∙ᴿ ξ ]ᴿ = x
  (suc y)       [ x ∙ᴿ ξ ]ᴿ = y [ ξ ]ᴿ
  (` x)         [ ξ ]ᴿ = ` (x [ ξ ]ᴿ)
  (λx e)        [ ξ ]ᴿ = λx (e [ ξ ↑ᴿ _ ]ᴿ)
  (Λα e)        [ ξ ]ᴿ = Λα (e [ ξ ↑ᴿ _ ]ᴿ)
  (∀[α∶ k ] t)  [ ξ ]ᴿ = ∀[α∶ k [ ξ ]ᴿ ] (t [ ξ ↑ᴿ _ ]ᴿ)
  (e₁ · e₂)     [ ξ ]ᴿ = (e₁ [ ξ ]ᴿ) · (e₂ [ ξ ]ᴿ)
  (e • t)       [ ξ ]ᴿ = (e [ ξ ]ᴿ) • (t [ ξ ]ᴿ)
  (t₁ ⇒ t₂)     [ ξ ]ᴿ = (t₁ [ ξ ]ᴿ) ⇒ (t₂ [ ξ ]ᴿ)
  *             [ ξ ]ᴿ = *

  _⨟ᴿ_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
  []       ⨟ᴿ ξ₂ = []
  (x ∙ᴿ ξ) ⨟ᴿ ξ₂ = (x [ ξ₂ ]ᴿ) ∙ᴿ (ξ ⨟ᴿ ξ₂)

-- ─── the substitution world ─────────────────────────────────────────

opaque
  ⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂
  ⟨ [] ⟩     = []
  ⟨ x ∙ᴿ ξ ⟩ = (` x) ∙ˢ ⟨ ξ ⟩

  -- post-composition of a substitution with a renaming, the ˢᴿ fusion
  -- taken as a primitive so that lifting stays structural
  _⨟ˢᴿ_ : S₁ →ˢ S₂ → S₂ →ᴿ S₃ → S₁ →ˢ S₃
  []       ⨟ˢᴿ ξ = []
  (t ∙ˢ σ) ⨟ˢᴿ ξ = (t [ ξ ]ᴿ) ∙ˢ (σ ⨟ˢᴿ ξ)

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s = (` zero) ∙ˢ (σ ⨟ˢᴿ wkᴿ s)

  _[_]ˢ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
  zero          [ t ∙ˢ σ ]ˢ = t
  (suc y)       [ t ∙ˢ σ ]ˢ = y [ σ ]ˢ
  (` x)         [ σ ]ˢ = x [ σ ]ˢ
  (λx e)        [ σ ]ˢ = λx (e [ σ ↑ˢ _ ]ˢ)
  (Λα e)        [ σ ]ˢ = Λα (e [ σ ↑ˢ _ ]ˢ)
  (∀[α∶ k ] t)  [ σ ]ˢ = ∀[α∶ k [ σ ]ˢ ] (t [ σ ↑ˢ _ ]ˢ)
  (e₁ · e₂)     [ σ ]ˢ = (e₁ [ σ ]ˢ) · (e₂ [ σ ]ˢ)
  (e • t)       [ σ ]ˢ = (e [ σ ]ˢ) • (t [ σ ]ˢ)
  (t₁ ⇒ t₂)     [ σ ]ˢ = (t₁ [ σ ]ˢ) ⇒ (t₂ [ σ ]ˢ)
  *             [ σ ]ˢ = *

  _⨟ˢ_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  []       ⨟ˢ σ₂ = []
  (t ∙ˢ σ) ⨟ˢ σ₂ = (t [ σ₂ ]ˢ) ∙ˢ (σ ⨟ˢ σ₂)

idˢ : S →ˢ S
idˢ = ⟨ idᴿ ⟩

wkˢ : ∀ s′ → S →ˢ (s′ ∷ S)
wkˢ s′ = ⟨ wkᴿ s′ ⟩

_[_]₀ : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
t [ t′ ]₀ = t [ (t′ ∙ˢ idˢ) ]ˢ

weaken : S ⊢ s → (s′ ∷ S) ⊢ s
weaken t = t [ wkᴿ _ ]ᴿ

-- ═══ THE RULE SET, RENAMING WORLD ═══════════════════════════════════

opaque
  unfolding wk*ᴿ idᴿ wkᴿ _↑ᴿ_ _[_]ᴿ _⨟ᴿ_

  -- the two structural lookups are the defining clauses themselves
  def-∙ᴿ-zero : zero [ (x ∙ᴿ ξ) ]ᴿ ≡ x
  def-∙ᴿ-zero = refl

  def-∙ᴿ-suc : (suc {s′ = s′} x′) [ (x ∙ᴿ ξ) ]ᴿ ≡ x′ [ ξ ]ᴿ
  def-∙ᴿ-suc = refl

  -- looking up in a weakened map
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

  -- lifting the identity, definitional here: both sides are the same cons
  lift-idᴿ : (idᴿ {S} ↑ᴿ s) ≡ idᴿ
  lift-idᴿ = refl

  -- the traversal rules are the defining clauses
  instᴿ-x : (` x)        [ ξ ]ᴿ ≡ ` (x [ ξ ]ᴿ)
  instᴿ-x = refl
  instᴿ-λ : (λx e)       [ ξ ]ᴿ ≡ λx (e [ (ξ ↑ᴿ _) ]ᴿ)
  instᴿ-λ = refl
  instᴿ-Λ : (Λα e)       [ ξ ]ᴿ ≡ Λα (e [ (ξ ↑ᴿ _) ]ᴿ)
  instᴿ-Λ = refl
  instᴿ-∀ : (∀[α∶ k ] t) [ ξ ]ᴿ ≡ ∀[α∶ k [ ξ ]ᴿ ] (t [ (ξ ↑ᴿ _) ]ᴿ)
  instᴿ-∀ = refl
  instᴿ-· : (e₁ · e₂)    [ ξ ]ᴿ ≡ (e₁ [ ξ ]ᴿ) · (e₂ [ ξ ]ᴿ)
  instᴿ-· = refl
  instᴿ-• : (e • t)      [ ξ ]ᴿ ≡ (e [ ξ ]ᴿ) • (t [ ξ ]ᴿ)
  instᴿ-• = refl
  instᴿ-⇒ : (t₁ ⇒ t₂)    [ ξ ]ᴿ ≡ (t₁ [ ξ ]ᴿ) ⇒ (t₂ [ ξ ]ᴿ)
  instᴿ-⇒ = refl
  instᴿ-* : * {S = S}    [ ξ ]ᴿ ≡ *
  instᴿ-* = refl

  -- the map algebra
  distᴿ : (x ∙ᴿ ξ₁) ⨟ᴿ ξ₂ ≡ (x [ ξ₂ ]ᴿ) ∙ᴿ (ξ₁ ⨟ᴿ ξ₂)
  distᴿ = refl

  -- composition at a variable PUSHES
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
  comp-idᵣᴿ {ξ = x ∙ᴿ ξ} = cong₂ _∙ᴿ_ (lookup-idᴿ x) comp-idᵣᴿ

  interactᴿ : wkᴿ s ⨟ᴿ (x ∙ᴿ ξ) ≡ ξ
  interactᴿ {x = x} {ξ = ξ} = trans (wk*ᴿ-⨟ᴿ idᴿ x ξ) comp-idₗᴿ

  lift-consᴿ : (ξ ↑ᴿ s) ⨟ᴿ (x ∙ᴿ ξ′) ≡ x ∙ᴿ (ξ ⨟ᴿ ξ′)
  lift-consᴿ {ξ = ξ} {x = x} {ξ′ = ξ′} = cong (x ∙ᴿ_) (wk*ᴿ-⨟ᴿ ξ x ξ′)

  assocᴿ : (ξ₁ ⨟ᴿ ξ₂) ⨟ᴿ ξ₃ ≡ ξ₁ ⨟ᴿ (ξ₂ ⨟ᴿ ξ₃)
  assocᴿ {ξ₁ = []}      = refl
  assocᴿ {ξ₁ = x ∙ᴿ ξ₁} = cong₂ _∙ᴿ_ (sym (compositionalityᴿᴿ-var x)) assocᴿ

  wk*ᴿ-comp : ∀ (ξ₁ : S₁ →ᴿ S₂) (ξ₂ : S₂ →ᴿ S₃) →
    wk*ᴿ s ξ₁ ⨟ᴿ (ξ₂ ↑ᴿ s) ≡ wk*ᴿ s (ξ₁ ⨟ᴿ ξ₂)
  wk*ᴿ-comp []        ξ₂ = refl
  wk*ᴿ-comp (x ∙ᴿ ξ₁) ξ₂ = cong₂ _∙ᴿ_ (lookup-wk*ᴿ x ξ₂) (wk*ᴿ-comp ξ₁ ξ₂)

  lift-dist-compᴿᴿ : ((ξ₁ ↑ᴿ s) ⨟ᴿ (ξ₂ ↑ᴿ s)) ≡ ((ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ {ξ₁ = ξ₁} {ξ₂ = ξ₂} = cong (zero ∙ᴿ_) (wk*ᴿ-comp ξ₁ ξ₂)

  ⨟ᴿ-wk*ᴿ : ∀ (ξ₁ : S₁ →ᴿ S₂) (ξ₂ : S₂ →ᴿ S₃) →
    ξ₁ ⨟ᴿ wk*ᴿ s ξ₂ ≡ wk*ᴿ s (ξ₁ ⨟ᴿ ξ₂)
  ⨟ᴿ-wk*ᴿ []        ξ₂ = refl
  ⨟ᴿ-wk*ᴿ (x ∙ᴿ ξ₁) ξ₂ = cong₂ _∙ᴿ_ (lookup-wk*ᴿ x ξ₂) (⨟ᴿ-wk*ᴿ ξ₁ ξ₂)

  lift-wkᴿ : wkᴿ s ⨟ᴿ (ξ ↑ᴿ s) ≡ ξ ⨟ᴿ wkᴿ s
  lift-wkᴿ {ξ = ξ} = trans (wk*ᴿ-comp idᴿ ξ)
    (trans (cong (wk*ᴿ _) comp-idₗᴿ)
    (sym (trans (⨟ᴿ-wk*ᴿ ξ idᴿ) (cong (wk*ᴿ _) comp-idᵣᴿ))))

  right-idᴿ : ∀ (x/t : S ⊢[ m ] s) → x/t [ idᴿ ]ᴿ ≡ x/t
  right-idᴿ zero          = refl
  right-idᴿ (suc x)       = lookup-idᴿ (suc x)
  right-idᴿ (` x)         = cong `_ (lookup-idᴿ x)
  right-idᴿ (λx e)        = cong λx_ (right-idᴿ e)
  right-idᴿ (Λα e)        = cong Λα_ (right-idᴿ e)
  right-idᴿ (∀[α∶ k ] t)  = cong₂ ∀[α∶_]_ (right-idᴿ k) (right-idᴿ t)
  right-idᴿ (e₁ · e₂)     = cong₂ _·_ (right-idᴿ e₁) (right-idᴿ e₂)
  right-idᴿ (e • t)       = cong₂ _•_ (right-idᴿ e) (right-idᴿ t)
  right-idᴿ (t₁ ⇒ t₂)     = cong₂ _⇒_ (right-idᴿ t₁) (right-idᴿ t₂)
  right-idᴿ *             = refl

  compositionalityᴿᴿ : ∀ (x/t : S₁ ⊢[ m ] s) {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
    (x/t [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ ≡ x/t [ (ξ₁ ⨟ᴿ ξ₂) ]ᴿ
  compositionalityᴿᴿ zero    {ξ₁ = y ∙ᴿ ξ₁} = refl
  compositionalityᴿᴿ (suc x) {ξ₁ = y ∙ᴿ ξ₁} = compositionalityᴿᴿ x
  compositionalityᴿᴿ (` x)        = cong `_ (compositionalityᴿᴿ x)
  compositionalityᴿᴿ (λx e)       = cong λx_ (trans (compositionalityᴿᴿ e) (cong (e [_]ᴿ) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (Λα e)       = cong Λα_ (trans (compositionalityᴿᴿ e) (cong (e [_]ᴿ) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿᴿ k)
                                      (trans (compositionalityᴿᴿ t) (cong (t [_]ᴿ) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿᴿ e₁) (compositionalityᴿᴿ e₂)
  compositionalityᴿᴿ (e • t)      = cong₂ _•_ (compositionalityᴿᴿ e) (compositionalityᴿᴿ t)
  compositionalityᴿᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)
  compositionalityᴿᴿ *            = refl

-- ═══ THE RULE SET, SUBSTITUTION WORLD ═══════════════════════════════

opaque
  unfolding wk*ᴿ idᴿ wkᴿ _↑ᴿ_ _[_]ᴿ _⨟ᴿ_ ⟨_⟩ _⨟ˢᴿ_ _↑ˢ_ _[_]ˢ _⨟ˢ_

  -- ── the coercion commutes with weakening and with lifting ─────────
  ⟨⟩-⨟ˢᴿ-wk : ∀ (ξ : S₁ →ᴿ S₂) → ⟨ ξ ⟩ ⨟ˢᴿ wkᴿ s ≡ ⟨ wk*ᴿ s ξ ⟩
  ⟨⟩-⨟ˢᴿ-wk []       = refl
  ⟨⟩-⨟ˢᴿ-wk (x ∙ᴿ ξ) = cong₂ _∙ˢ_ (cong `_ def-wkᴿ) (⟨⟩-⨟ˢᴿ-wk ξ)

  ⟨⟩-lift : (⟨ ξ ⟩ ↑ˢ s) ≡ ⟨ ξ ↑ᴿ s ⟩
  ⟨⟩-lift {ξ = ξ} = cong ((` zero) ∙ˢ_) (⟨⟩-⨟ˢᴿ-wk ξ)

  -- ── coincidence: the substitution world collapses into the ᴿ world ─
  coincidence-var : ∀ (x : S₁ ∋ s) (ξ : S₁ →ᴿ S₂) → x [ ⟨ ξ ⟩ ]ˢ ≡ ` (x [ ξ ]ᴿ)
  coincidence-var zero    (y ∙ᴿ ξ) = refl
  coincidence-var (suc x) (y ∙ᴿ ξ) = coincidence-var x ξ

  coincidence : ∀ (t : S₁ ⊢ s) (ξ : S₁ →ᴿ S₂) → t [ ⟨ ξ ⟩ ]ˢ ≡ t [ ξ ]ᴿ
  coincidence (` x)        ξ = coincidence-var x ξ
  coincidence (λx e)       ξ = cong λx_ (trans (cong (e [_]ˢ) ⟨⟩-lift) (coincidence e (ξ ↑ᴿ _)))
  coincidence (Λα e)       ξ = cong Λα_ (trans (cong (e [_]ˢ) ⟨⟩-lift) (coincidence e (ξ ↑ᴿ _)))
  coincidence (∀[α∶ k ] t) ξ = cong₂ ∀[α∶_]_ (coincidence k ξ)
                                  (trans (cong (t [_]ˢ) ⟨⟩-lift) (coincidence t (ξ ↑ᴿ _)))
  coincidence (e₁ · e₂)    ξ = cong₂ _·_ (coincidence e₁ ξ) (coincidence e₂ ξ)
  coincidence (e • t)      ξ = cong₂ _•_ (coincidence e ξ) (coincidence t ξ)
  coincidence (t₁ ⇒ t₂)    ξ = cong₂ _⇒_ (coincidence t₁ ξ) (coincidence t₂ ξ)
  coincidence *            ξ = refl

  -- ── ⨟ˢᴿ is the ᴿ-coercion of ⨟ˢ, so it never reaches a rule ────────
  ⨟ˢᴿ-def : ∀ (σ : S₁ →ˢ S₂) (ξ : S₂ →ᴿ S₃) → σ ⨟ˢᴿ ξ ≡ σ ⨟ˢ ⟨ ξ ⟩
  ⨟ˢᴿ-def []       ξ = refl
  ⨟ˢᴿ-def (t ∙ˢ σ) ξ = cong₂ _∙ˢ_ (sym (coincidence t ξ)) (⨟ˢᴿ-def σ ξ)

  -- ── the structural lookups ────────────────────────────────────────
  def-∙ˢ-zero : zero [ (t ∙ˢ σ) ]ˢ ≡ t
  def-∙ˢ-zero = refl

  def-∙ˢ-suc : (suc {s′ = s′} x) [ (t ∙ˢ σ) ]ˢ ≡ x [ σ ]ˢ
  def-∙ˢ-suc = refl

  def-↑ˢ-zero : zero [ (σ ↑ˢ s) ]ˢ ≡ ` zero
  def-↑ˢ-zero = refl

  def-↑ˢ-suc : (suc x) [ (σ ↑ˢ s) ]ˢ ≡ x [ (σ ⨟ˢ ⟨ wkᴿ s ⟩) ]ˢ
  def-↑ˢ-suc {x = x} {σ = σ} {s = s} = cong (x [_]ˢ) (⨟ˢᴿ-def σ (wkᴿ s))

  -- ── the traversal rules are the defining clauses ──────────────────
  inst-x : (` x)        [ σ ]ˢ ≡ x [ σ ]ˢ
  inst-x = refl
  inst-λ : (λx e)       [ σ ]ˢ ≡ λx (e [ (σ ↑ˢ _) ]ˢ)
  inst-λ = refl
  inst-Λ : (Λα e)       [ σ ]ˢ ≡ Λα (e [ (σ ↑ˢ _) ]ˢ)
  inst-Λ = refl
  inst-∀ : (∀[α∶ k ] t) [ σ ]ˢ ≡ ∀[α∶ k [ σ ]ˢ ] (t [ (σ ↑ˢ _) ]ˢ)
  inst-∀ = refl
  inst-· : (e₁ · e₂)    [ σ ]ˢ ≡ (e₁ [ σ ]ˢ) · (e₂ [ σ ]ˢ)
  inst-· = refl
  inst-• : (e • t)      [ σ ]ˢ ≡ (e [ σ ]ˢ) • (t [ σ ]ˢ)
  inst-• = refl
  inst-⇒ : (t₁ ⇒ t₂)    [ σ ]ˢ ≡ (t₁ [ σ ]ˢ) ⇒ (t₂ [ σ ]ˢ)
  inst-⇒ = refl
  inst-* : * {S = S}    [ σ ]ˢ ≡ *
  inst-* = refl

  dist : (t ∙ˢ σ₁) ⨟ˢ σ₂ ≡ (t [ σ₂ ]ˢ) ∙ˢ (σ₁ ⨟ˢ σ₂)
  dist = refl

  -- ── lookup through the two hybrid compositions ────────────────────
  lookup-⨟ˢᴿ : ∀ (x : S₁ ∋ s) (σ : S₁ →ˢ S₂) (ξ : S₂ →ᴿ S₃) →
    x [ σ ⨟ˢᴿ ξ ]ˢ ≡ (x [ σ ]ˢ) [ ξ ]ᴿ
  lookup-⨟ˢᴿ zero    (t ∙ˢ σ) ξ = refl
  lookup-⨟ˢᴿ (suc x) (t ∙ˢ σ) ξ = lookup-⨟ˢᴿ x σ ξ

  lookup-⨟ˢ : ∀ (x : S₁ ∋ s) (σ₁ : S₁ →ˢ S₂) (σ₂ : S₂ →ˢ S₃) →
    x [ σ₁ ⨟ˢ σ₂ ]ˢ ≡ (x [ σ₁ ]ˢ) [ σ₂ ]ˢ
  lookup-⨟ˢ zero    (t ∙ˢ σ₁) σ₂ = refl
  lookup-⨟ˢ (suc x) (t ∙ˢ σ₁) σ₂ = lookup-⨟ˢ x σ₁ σ₂

  -- ── the left unit and the interaction law ─────────────────────────
  ⟨wk*⟩-cons : ∀ (ξ : S₁ →ᴿ S₂) (t : S₃ ⊢ s′) (σ : S₂ →ˢ S₃) →
    ⟨ wk*ᴿ s′ ξ ⟩ ⨟ˢ (t ∙ˢ σ) ≡ ⟨ ξ ⟩ ⨟ˢ σ
  ⟨wk*⟩-cons []       t σ = refl
  ⟨wk*⟩-cons (x ∙ᴿ ξ) t σ = cong (_ ∙ˢ_) (⟨wk*⟩-cons ξ t σ)

  comp-idₗ : ⟨ idᴿ {S₁} ⟩ ⨟ˢ σ ≡ σ
  comp-idₗ {σ = []}     = refl
  comp-idₗ {σ = t ∙ˢ σ} = cong (t ∙ˢ_) (trans (⟨wk*⟩-cons idᴿ t σ) comp-idₗ)

  interact : ⟨ wkᴿ s ⟩ ⨟ˢ (t ∙ˢ σ) ≡ σ
  interact {t = t} {σ = σ} = trans (⟨wk*⟩-cons idᴿ t σ) comp-idₗ

  -- ── ᴿˢ fusion: needs only ᴿ-facts ─────────────────────────────────
  ⟨wk*⟩-lift : ∀ (ξ : S₁ →ᴿ S₂) (σ : S₂ →ˢ S₃) →
    ⟨ wk*ᴿ s ξ ⟩ ⨟ˢ (σ ↑ˢ s) ≡ (⟨ ξ ⟩ ⨟ˢ σ) ⨟ˢᴿ wkᴿ s
  ⟨wk*⟩-lift []       σ = refl
  ⟨wk*⟩-lift (x ∙ᴿ ξ) σ = cong₂ _∙ˢ_ (lookup-⨟ˢᴿ x σ (wkᴿ _)) (⟨wk*⟩-lift ξ σ)

  lift-dist-compᴿˢ : ⟨ ξ ↑ᴿ s ⟩ ⨟ˢ (σ ↑ˢ s) ≡ ((⟨ ξ ⟩ ⨟ˢ σ) ↑ˢ s)
  lift-dist-compᴿˢ {ξ = ξ} {σ = σ} = cong ((` zero) ∙ˢ_) (⟨wk*⟩-lift ξ σ)

  compositionalityᴿˢ : ∀ (x/t : S₁ ⊢[ m ] s) {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    (x/t [ ξ ]ᴿ) [ σ ]ˢ ≡ x/t [ (⟨ ξ ⟩ ⨟ˢ σ) ]ˢ
  compositionalityᴿˢ zero    {ξ = y ∙ᴿ ξ} = refl
  compositionalityᴿˢ (suc x) {ξ = y ∙ᴿ ξ} = compositionalityᴿˢ x
  compositionalityᴿˢ (` x)        = compositionalityᴿˢ x
  compositionalityᴿˢ (λx e)       = cong λx_ (trans (compositionalityᴿˢ e) (cong (e [_]ˢ) lift-dist-compᴿˢ))
  compositionalityᴿˢ (Λα e)       = cong Λα_ (trans (compositionalityᴿˢ e) (cong (e [_]ˢ) lift-dist-compᴿˢ))
  compositionalityᴿˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿˢ k)
                                      (trans (compositionalityᴿˢ t) (cong (t [_]ˢ) lift-dist-compᴿˢ))
  compositionalityᴿˢ (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿˢ e₁) (compositionalityᴿˢ e₂)
  compositionalityᴿˢ (e • t)      = cong₂ _•_ (compositionalityᴿˢ e) (compositionalityᴿˢ t)
  compositionalityᴿˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿˢ t₁) (compositionalityᴿˢ t₂)
  compositionalityᴿˢ *            = refl

  -- ── ˢᴿ fusion, stated over the internal ⨟ˢᴿ ───────────────────────
  ⨟ˢᴿ-lift : ∀ (σ : S₁ →ˢ S₂) (ξ : S₂ →ᴿ S₃) →
    (σ ⨟ˢᴿ wkᴿ s) ⨟ˢᴿ (ξ ↑ᴿ s) ≡ (σ ⨟ˢᴿ ξ) ⨟ˢᴿ wkᴿ s
  ⨟ˢᴿ-lift []       ξ = refl
  ⨟ˢᴿ-lift (t ∙ˢ σ) ξ = cong₂ _∙ˢ_
    (trans (compositionalityᴿᴿ t) (trans (cong (t [_]ᴿ) lift-wkᴿ) (sym (compositionalityᴿᴿ t))))
    (⨟ˢᴿ-lift σ ξ)

  lift-⨟ˢᴿ : ∀ (σ : S₁ →ˢ S₂) (ξ : S₂ →ᴿ S₃) → (σ ↑ˢ s) ⨟ˢᴿ (ξ ↑ᴿ s) ≡ ((σ ⨟ˢᴿ ξ) ↑ˢ s)
  lift-⨟ˢᴿ σ ξ = cong ((` zero) ∙ˢ_) (⨟ˢᴿ-lift σ ξ)

  compositionalityˢᴿ′ : ∀ (x/t : S₁ ⊢[ m ] s) {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
    (x/t [ σ ]ˢ) [ ξ ]ᴿ ≡ x/t [ (σ ⨟ˢᴿ ξ) ]ˢ
  compositionalityˢᴿ′ zero    {σ = t ∙ˢ σ} = refl
  compositionalityˢᴿ′ (suc x) {σ = t ∙ˢ σ} = compositionalityˢᴿ′ x
  compositionalityˢᴿ′ (` x)        = compositionalityˢᴿ′ x
  compositionalityˢᴿ′ (λx e)  {σ = σ} {ξ = ξ} =
    cong λx_ (trans (compositionalityˢᴿ′ e) (cong (e [_]ˢ) (lift-⨟ˢᴿ σ ξ)))
  compositionalityˢᴿ′ (Λα e)  {σ = σ} {ξ = ξ} =
    cong Λα_ (trans (compositionalityˢᴿ′ e) (cong (e [_]ˢ) (lift-⨟ˢᴿ σ ξ)))
  compositionalityˢᴿ′ (∀[α∶ k ] t) {σ = σ} {ξ = ξ} = cong₂ ∀[α∶_]_ (compositionalityˢᴿ′ k)
    (trans (compositionalityˢᴿ′ t) (cong (t [_]ˢ) (lift-⨟ˢᴿ σ ξ)))
  compositionalityˢᴿ′ (e₁ · e₂)    = cong₂ _·_ (compositionalityˢᴿ′ e₁) (compositionalityˢᴿ′ e₂)
  compositionalityˢᴿ′ (e • t)      = cong₂ _•_ (compositionalityˢᴿ′ e) (compositionalityˢᴿ′ t)
  compositionalityˢᴿ′ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢᴿ′ t₁) (compositionalityˢᴿ′ t₂)
  compositionalityˢᴿ′ *            = refl

  compositionalityˢᴿ : ∀ (x/t : S₁ ⊢[ m ] s) {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
    (x/t [ σ ]ˢ) [ ξ ]ᴿ ≡ x/t [ (σ ⨟ˢ ⟨ ξ ⟩) ]ˢ
  compositionalityˢᴿ x/t {σ = σ} {ξ = ξ} =
    trans (compositionalityˢᴿ′ x/t) (cong (x/t [_]ˢ) (⨟ˢᴿ-def σ ξ))

  -- ── the σ-world algebra ───────────────────────────────────────────
  lift-wk : ⟨ wkᴿ s ⟩ ⨟ˢ (σ ↑ˢ s) ≡ σ ⨟ˢ ⟨ wkᴿ s ⟩
  lift-wk {s = s} {σ = σ} = trans (⟨wk*⟩-lift idᴿ σ)
    (trans (cong (_⨟ˢᴿ wkᴿ s) comp-idₗ) (⨟ˢᴿ-def σ (wkᴿ s)))

  ⨟ˢᴿwk-lift : ∀ (σ₁ : S₁ →ˢ S₂) (σ₂ : S₂ →ˢ S₃) →
    (σ₁ ⨟ˢᴿ wkᴿ s) ⨟ˢ (σ₂ ↑ˢ s) ≡ (σ₁ ⨟ˢ σ₂) ⨟ˢᴿ wkᴿ s
  ⨟ˢᴿwk-lift []       σ₂ = refl
  ⨟ˢᴿwk-lift {s = s} (t ∙ˢ σ₁) σ₂ = cong₂ _∙ˢ_
    (trans (compositionalityᴿˢ t)
      (trans (cong (t [_]ˢ) (trans lift-wk (sym (⨟ˢᴿ-def σ₂ (wkᴿ s)))))
             (sym (compositionalityˢᴿ′ t))))
    (⨟ˢᴿwk-lift σ₁ σ₂)

  lift-dist-compˢˢ : ((σ₁ ↑ˢ s) ⨟ˢ (σ₂ ↑ˢ s)) ≡ ((σ₁ ⨟ˢ σ₂) ↑ˢ s)
  lift-dist-compˢˢ {σ₁ = σ₁} {σ₂ = σ₂} = cong ((` zero) ∙ˢ_) (⨟ˢᴿwk-lift σ₁ σ₂)

  compositionalityˢˢ : ∀ (x/t : S₁ ⊢[ m ] s) {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} →
    (x/t [ σ₁ ]ˢ) [ σ₂ ]ˢ ≡ x/t [ (σ₁ ⨟ˢ σ₂) ]ˢ
  compositionalityˢˢ zero    {σ₁ = t ∙ˢ σ₁} = refl
  compositionalityˢˢ (suc x) {σ₁ = t ∙ˢ σ₁} = compositionalityˢˢ x
  compositionalityˢˢ (` x)        = compositionalityˢˢ x
  compositionalityˢˢ (λx e)       = cong λx_ (trans (compositionalityˢˢ e) (cong (e [_]ˢ) lift-dist-compˢˢ))
  compositionalityˢˢ (Λα e)       = cong Λα_ (trans (compositionalityˢˢ e) (cong (e [_]ˢ) lift-dist-compˢˢ))
  compositionalityˢˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢˢ k)
                                      (trans (compositionalityˢˢ t) (cong (t [_]ˢ) lift-dist-compˢˢ))
  compositionalityˢˢ (e₁ · e₂)    = cong₂ _·_ (compositionalityˢˢ e₁) (compositionalityˢˢ e₂)
  compositionalityˢˢ (e • t)      = cong₂ _•_ (compositionalityˢˢ e) (compositionalityˢˢ t)
  compositionalityˢˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢˢ t₁) (compositionalityˢˢ t₂)
  compositionalityˢˢ *            = refl

  assoc : (σ₁ ⨟ˢ σ₂) ⨟ˢ σ₃ ≡ σ₁ ⨟ˢ (σ₂ ⨟ˢ σ₃)
  assoc {σ₁ = []}      = refl
  assoc {σ₁ = t ∙ˢ σ₁} = cong₂ _∙ˢ_ (compositionalityˢˢ t) assoc

  comp-idᵣ : σ ⨟ˢ ⟨ idᴿ ⟩ ≡ σ
  comp-idᵣ {σ = []}     = refl
  comp-idᵣ {σ = t ∙ˢ σ} = cong₂ _∙ˢ_ (trans (coincidence t idᴿ) (right-idᴿ t)) comp-idᵣ

  ⨟ˢᴿwk-cons : ∀ (σ : S₁ →ˢ S₂) (t : S₃ ⊢ s) (τ : S₂ →ˢ S₃) →
    (σ ⨟ˢᴿ wkᴿ s) ⨟ˢ (t ∙ˢ τ) ≡ σ ⨟ˢ τ
  ⨟ˢᴿwk-cons []       t τ = refl
  ⨟ˢᴿwk-cons (u ∙ˢ σ) t τ =
    cong₂ _∙ˢ_ (trans (compositionalityᴿˢ u) (cong (u [_]ˢ) interact)) (⨟ˢᴿwk-cons σ t τ)

  lift-cons : (σ ↑ˢ s) ⨟ˢ (t ∙ˢ τ) ≡ t ∙ˢ (σ ⨟ˢ τ)
  lift-cons {σ = σ} {t = t} {τ = τ} = cong (t ∙ˢ_) (⨟ˢᴿwk-cons σ t τ)

  -- ── the collapse family ───────────────────────────────────────────
  ⟨⟩-comp : ⟨ ξ₁ ⟩ ⨟ˢ ⟨ ξ₂ ⟩ ≡ ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩
  ⟨⟩-comp {ξ₁ = []}      = refl
  ⟨⟩-comp {ξ₁ = x ∙ᴿ ξ₁} {ξ₂ = ξ₂} = cong₂ _∙ˢ_ (coincidence-var x ξ₂) ⟨⟩-comp

  ⟨⟩-split-⨟ : ⟨ ξ₁ ⨟ᴿ ξ₂ ⟩ ⨟ˢ σ ≡ ⟨ ξ₁ ⟩ ⨟ˢ (⟨ ξ₂ ⟩ ⨟ˢ σ)
  ⟨⟩-split-⨟ {ξ₁ = []}      = refl
  ⟨⟩-split-⨟ {ξ₁ = x ∙ᴿ ξ₁} = cong₂ _∙ˢ_ (compositionalityᴿˢ x) ⟨⟩-split-⨟

  ⟨⟩-lift-cons : ⟨ ξ ↑ᴿ s ⟩ ⨟ˢ (t ∙ˢ σ) ≡ t ∙ˢ (⟨ ξ ⟩ ⨟ˢ σ)
  ⟨⟩-lift-cons {ξ = ξ} {t = t} {σ = σ} = cong (t ∙ˢ_) (⟨wk*⟩-cons ξ t σ)

  lift-id : (⟨ idᴿ {S} ⟩ ↑ˢ s) ≡ ⟨ idᴿ ⟩
  lift-id = ⟨⟩-lift

-- ═══ REGISTRATION ═══════════════════════════════════════════════════

{-# REWRITE
  def-wkᴿ def-∙ᴿ-zero def-∙ᴿ-suc def-↑ᴿ-zero def-↑ᴿ-suc
  instᴿ-x instᴿ-λ instᴿ-Λ instᴿ-∀ instᴿ-· instᴿ-• instᴿ-⇒ instᴿ-*
  assocᴿ comp-idₗᴿ comp-idᵣᴿ interactᴿ
  lift-idᴿ lift-dist-compᴿᴿ lift-wkᴿ
  right-idᴿ compositionalityᴿᴿ-var compositionalityᴿᴿ
  coincidence-var def-∙ˢ-zero def-∙ˢ-suc def-↑ˢ-zero def-↑ˢ-suc
  inst-x inst-λ inst-Λ inst-∀ inst-· inst-• inst-⇒ inst-*
  assoc dist interact comp-idₗ comp-idᵣ
  lift-wk lift-cons lift-dist-compˢˢ
  compositionalityˢˢ compositionalityᴿˢ compositionalityˢᴿ lift-dist-compᴿˢ
  coincidence ⟨⟩-comp ⟨⟩-split-⨟ ⟨⟩-lift ⟨⟩-lift-cons
#-}

-- ═══ THE THEORY IS DEFINITIONAL, IN BOTH WORLDS ═════════════════════
-- Exactly the checks systemf.agda makes, and each is `refl` here too.

var-zero : ∀ {t′ : S ⊢ s′} → (` zero) [ t′ ]₀ ≡ t′
var-zero = refl
var-suc : ∀ {x : S ∋ s} {t′ : S ⊢ s′} → (` suc x) [ t′ ]₀ ≡ ` x
var-suc = refl

wk-cancel : ∀ {t : S ⊢ s} {t′ : S ⊢ s′} → (weaken t) [ t′ ]₀ ≡ t
wk-cancel = refl

wk-comm : ∀ {t : S₁ ⊢ s} {σ : S₁ →ˢ S₂} →
  (weaken {s′ = s′} t) [ σ ↑ˢ s′ ]ˢ ≡ weaken (t [ σ ]ˢ)
wk-comm = refl

subst-commute : ∀ {t : (s′ ∷ S₁) ⊢ s} {t′ : S₁ ⊢ s′} {σ : S₁ →ˢ S₂} →
  (t [ σ ↑ˢ s′ ]ˢ) [ t′ [ σ ]ˢ ]₀ ≡ (t [ t′ ]₀) [ σ ]ˢ
subst-commute = refl

subst-subst : ∀ {t : (s₁ ∷ s₂ ∷ S) ⊢ s} {t′ : (s₂ ∷ S) ⊢ s₁} {t₂ : S ⊢ s₂} →
  (t [ t′ ]₀) [ t₂ ]₀ ≡ (t [ ((t₂ ∙ˢ idˢ) ↑ˢ s₁) ]ˢ) [ t′ [ t₂ ]₀ ]₀
subst-subst = refl

lift-comp : ∀ {t : (s′ ∷ S₁) ⊢ s} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} →
  (t [ σ₁ ↑ˢ s′ ]ˢ) [ σ₂ ↑ˢ s′ ]ˢ ≡ t [ (σ₁ ⨟ˢ σ₂) ↑ˢ s′ ]ˢ
lift-comp = refl

renᴿ-id : ∀ {x/t : S ⊢[ m ] s} → x/t [ idᴿ ]ᴿ ≡ x/t
renᴿ-id = refl
renᴿ-comp : ∀ {t : S₁ ⊢ s} {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
  (t [ ξ₁ ]ᴿ) [ ξ₂ ]ᴿ ≡ t [ ξ₁ ⨟ᴿ ξ₂ ]ᴿ
renᴿ-comp = refl
renᴿ-lift : ∀ {ξ₁ : S₁ →ᴿ S₂} {ξ₂ : S₂ →ᴿ S₃} →
  (ξ₁ ↑ᴿ s) ⨟ᴿ (ξ₂ ↑ᴿ s) ≡ (ξ₁ ⨟ᴿ ξ₂) ↑ᴿ s
renᴿ-lift = refl
mixed-RS : ∀ {t : S₁ ⊢ s} {ξ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
  (t [ ξ ]ᴿ) [ σ ]ˢ ≡ t [ ⟨ ξ ⟩ ⨟ˢ σ ]ˢ
mixed-RS = refl
mixed-SR : ∀ {t : S₁ ⊢ s} {σ : S₁ →ˢ S₂} {ξ : S₂ →ᴿ S₃} →
  (t [ σ ]ˢ) [ ξ ]ᴿ ≡ t [ σ ⨟ˢ ⟨ ξ ⟩ ]ˢ
mixed-SR = refl
emb-collapse : ∀ {t : S₁ ⊢ s} {ξ : S₁ →ᴿ S₂} → t [ ⟨ ξ ⟩ ]ˢ ≡ t [ ξ ]ᴿ
emb-collapse = refl

-- ═══ TYPING AND SUBJECT REDUCTION ══════════════════════════════════
-- Copied from systemf.agda without a single change.  That is the point
-- of the file: the map model is invisible above the rule set.

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
  Γ Γ₁ Γ₂ : Ctx S

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

-- TYPED RENAMINGS: phase 1 of the preservation lemma.  With renamings
-- first class this is a plain judgment on ᴿ-maps, and the payoff is
-- immediate.  _[_]ᴿ preserves the mode, so a typed renaming sends a
-- variable to a VARIABLE by construction, and the ⊢`-case below is a
-- direct application.  The one-world file cannot say this: there phase
-- 1 must be a Σ-PREDICATE on substitutions,
--
--   σ ∶ᵥ Γ₁ →ˢ Γ₂ = ∀ x t → Γ₁ ∋ x ∶ t → Σ y ((x [ σ) ]ˢ ≡ ` y) × …
--
-- and extracting that y costs a transport (its ⊢ᵥ-var, "the one
-- unavoidable transport", with a `rewrite` to dodge UnificationStuck).
-- HERE THE TRANSPORT DISAPPEARS — that is the clearest single win of
-- first-class renamings.
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
-- the type-application β-case uses no law: t′ [ t ]₀ IS t′ [ t ∙ˢ idˢ ]ˢ.
sr (⊢• {t = t} (⊢Λ ⊢e) ⊢t ⊢t′) β-Λ =
  sub-pres {σ = t ∙ˢ idˢ} ⊢e (⊢[] ⊢t)
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ st)       = ⊢· (sr ⊢e₁ st) ⊢e₂
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ st v₁)    = ⊢· ⊢e₁ (sr ⊢e₂ st)
sr (⊢• ⊢e ⊢t ⊢t′) (ξ-• st)      = ⊢• (sr ⊢e st) ⊢t ⊢t′