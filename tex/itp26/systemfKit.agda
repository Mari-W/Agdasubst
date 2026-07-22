{-# OPTIONS --rewriting --local-confluence-check #-}
-- MODE-INDEXED System F.  NEGATIVE RESULT: 50 critical pairs, vs 0 for the
-- two-sorted systemfOne.agda.  Do not adopt this design; read on for why.
--
-- The idea: one substitution family _→[_]_ indexed by Mode (→[ V ] a renaming,
-- →[ T ] a substitution) sharing ONE _⋯_, _⨟_, _↑_, id, wk, _∙_, with the
-- variable injection as a FUNCTION (var / ⌞_⌟) rather than a constructor.  The
-- hope was that systemfOne's last transport, def-⟨⟩, would have no counterpart
-- because ⟨_⟩ would not exist.
--
-- What actually happens, measured:
--
--  1. ⟨_⟩ DOES still exist — it is definable as id{T} ⨟ ρ.  See
--     coercion-is-definable at the bottom of this file, which typechecks by
--     refl.  Removing the former did not remove the operation; every mixed-mode
--     composition can now produce one, so the obstruction got BROADER, not
--     narrower.  This is the decisive point.
--
--  2. var and ⌞_⌟ do not compute at an abstract mode.  Any law whose RHS
--     produces a variable (def-id, def-wk, def-↑-zero, inst-x, def-⨟-↑zero)
--     must therefore commit to a mode and be split in two — undoing exactly the
--     collapse the design was for.
--
--  3. m ⊔ V is stuck for abstract m, so comp-idᵣ cannot be stated
--     mode-polymorphically.  Predicted cost: "a handful of laws split in two,
--     none of it a transport."  Actual cost: UNJOINABLE PAIRS, because the
--     rewrite engine cannot apply a mode-split rule to a term whose mode is a
--     variable.  ↑-id alone accounts for 9 of the 50.
--
-- Ablations (rules unregistered, pairs recounted):
--     baseline                     50
--     − ↑-id                       41
--     − def-idˢ, def-wkˢ           39
--     − right-id                   33
-- Even with the whole identity family gone it does not approach systemfOne.
module systemfKit where


open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

ext : {A : Set} {B : A → Set} {C : A → Set} → {f g : (a : A) → B a → C a} →
  (∀ {a} x → f a x ≡ g a x) → f ≡ g
ext f = fun-ext λ _ → fun-ext λ x → f x

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; drop)

data Sort : Set where
  expr type kind : Sort

variable
  s s₁ s₂ s′ : Sort
  S S₁ S₂ S₃ S₄ : List Sort

Scope = List Sort

data Mode : Set where V T : Mode
variable
  m m₁ m₂ m₃ : Mode

-- Matching on the FIRST argument: V is a definitional left unit, and
-- associativity is definitional as soon as the leftmost mode is concrete.
_⊔_ : Mode → Mode → Mode
V ⊔ m = m
T ⊔ m = T

data _⊢[_]_ : Scope → Mode → Sort → Set

_⊢_ = _⊢[ T ]_
_∋_ = _⊢[ V ]_

data _⊢[_]_ where
  zero     : (s ∷ S) ∋ s
  suc      : S ∋ s → (s′ ∷ S) ∋ s
  `_       : S ∋ s → S ⊢ s
  λx_      : (expr ∷ S) ⊢ expr → S ⊢ expr
  Λα_      : (type ∷ S) ⊢ expr → S ⊢ expr
  ∀[α∶_]_  : S ⊢ kind → (type ∷ S) ⊢ type → S ⊢ type
  _·_      : S ⊢ expr → S ⊢ expr → S ⊢ expr
  _•_      : S ⊢ expr → S ⊢ type → S ⊢ expr
  _⇒_      : S ⊢ type → S ⊢ type → S ⊢ type
  *        : S ⊢ kind

variable
  e e₁ e₂ e′ : S ⊢ expr
  k k′ : S ⊢ kind
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s

-- the variable, at mode m.  NOT a constructor: at mode T it computes to `_,
-- at mode V it is the identity.
var : S ∋ s → S ⊢[ m ] s
var {m = V} x = x
var {m = T} x = ` x

_→[_]_ : Scope → Mode → Scope → Set
S₁ →[ m ] S₂ = ∀ s → S₁ ∋ s → S₂ ⊢[ m ] s

variable
  φ φ₁ φ₂ φ₃ : S₁ →[ m ] S₂
  ρ ρ₁ ρ₂ ρ₃ : S₁ →[ V ] S₂
  σ σ₁ σ₂ σ₃ : S₁ →[ T ] S₂
  v v₁ v₂ : S ⊢[ m ] s

------------------------------------------------------------------------
-- Internal two-stage implementation.  Only _⋯_/_↑_ below are exposed; the
-- staging exists purely because the traversal's termination demands it.
------------------------------------------------------------------------

private
  _↑ᴿ_ : S₁ →[ V ] S₂ → ∀ s → (s ∷ S₁) →[ V ] (s ∷ S₂)
  (ρ ↑ᴿ s) _ zero    = zero
  (ρ ↑ᴿ s) _ (suc x) = suc (ρ _ x)

  _⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →[ V ] S₂ → S₂ ⊢[ m ] s
  _⋯ᴿ_ {m = V} x   ρ = ρ _ x
  (` x)         ⋯ᴿ ρ = ` (ρ _ x)
  (λx e)        ⋯ᴿ ρ = λx (e ⋯ᴿ (ρ ↑ᴿ _))
  (Λα e)        ⋯ᴿ ρ = Λα (e ⋯ᴿ (ρ ↑ᴿ _))
  (∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ (ρ ↑ᴿ _))
  (e₁ · e₂)     ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
  (e • t)       ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
  (t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
  *             ⋯ᴿ ρ = *

  _↑ˢ_ : S₁ →[ T ] S₂ → ∀ s → (s ∷ S₁) →[ T ] (s ∷ S₂)
  (σ ↑ˢ s) _ zero    = ` zero
  (σ ↑ˢ s) _ (suc x) = (σ _ x) ⋯ᴿ (λ _ y → suc y)

  _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →[ T ] S₂ → S₂ ⊢ s
  _⋯ˢ_ {m = V} x σ = σ _ x
  (` x)         ⋯ˢ σ = σ _ x
  (λx e)        ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ _))
  (Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ _))
  (∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  (e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  (e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  *             ⋯ˢ σ = *

------------------------------------------------------------------------
-- THE INTERFACE: one operation each.
------------------------------------------------------------------------

opaque
  id : S →[ m ] S
  id _ x = var x

  wk : ∀ s → S →[ m ] (s ∷ S)
  wk _ _ x = var (suc x)

  _∙_ : S₂ ⊢[ m ] s → S₁ →[ m ] S₂ → (s ∷ S₁) →[ m ] S₂
  (v ∙ φ) _ zero    = v
  (v ∙ φ) _ (suc x) = φ _ x

  -- the variable clause needs NO mode dispatch: V ⊔ m₂ = m₂ definitionally.
  _⋯_ : S₁ ⊢[ m₁ ] s → S₁ →[ m₂ ] S₂ → S₂ ⊢[ m₁ ⊔ m₂ ] s
  _⋯_ {m₁ = V}          x φ = φ _ x
  _⋯_ {m₁ = T} {m₂ = V} t φ = t ⋯ᴿ φ
  _⋯_ {m₁ = T} {m₂ = T} t φ = t ⋯ˢ φ

  _↑_ : S₁ →[ m ] S₂ → ∀ s → (s ∷ S₁) →[ m ] (s ∷ S₂)
  _↑_ {m = V} ρ s = ρ ↑ᴿ s
  _↑_ {m = T} σ s = σ ↑ˢ s

  _⨟_ : S₁ →[ m₁ ] S₂ → S₂ →[ m₂ ] S₃ → S₁ →[ m₁ ⊔ m₂ ] S₃
  (φ₁ ⨟ φ₂) _ x = (φ₁ _ x) ⋯ φ₂

infixl 8 _⋯_
infixr 9 _⨟_
infixr 10 _∙_

-- the injection of a mode-m result into a term.  A FUNCTION, not a constructor:
-- at mode T it is the identity and computes away entirely.
⌞_⌟ : S ⊢[ m ] s → S ⊢[ T ] s
⌞_⌟ {m = V} x = ` x
⌞_⌟ {m = T} t = t

opaque
  unfolding id wk _∙_ _⋯_ _↑_ _⨟_

  ---------------------------------------------------------------- internal
  coincidence : ∀ {S₁ S₂ s} {ρ : S₁ →[ V ] S₂} (t : S₁ ⊢ s) →
    t ⋯ᴿ ρ ≡ t ⋯ˢ (λ _ x → ` (ρ _ x))
  compᴿᴿ : ∀ {S₁ S₂ S₃ s} {ρ₁ : S₁ →[ V ] S₂} {ρ₂ : S₂ →[ V ] S₃} (t : S₁ ⊢ s) →
    (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂ ≡ t ⋯ᴿ (λ _ x → ρ₂ _ (ρ₁ _ x))
  compᴿˢ : ∀ {S₁ S₂ S₃ s} {ρ₁ : S₁ →[ V ] S₂} {σ₂ : S₂ →[ T ] S₃} (t : S₁ ⊢ s) →
    (t ⋯ᴿ ρ₁) ⋯ˢ σ₂ ≡ t ⋯ˢ (λ _ x → σ₂ _ (ρ₁ _ x))
  compˢᴿ : ∀ {S₁ S₂ S₃ s} {σ₁ : S₁ →[ T ] S₂} {ρ₂ : S₂ →[ V ] S₃} (t : S₁ ⊢ s) →
    (t ⋯ˢ σ₁) ⋯ᴿ ρ₂ ≡ t ⋯ˢ (λ _ x → (σ₁ _ x) ⋯ᴿ ρ₂)
  compˢˢ : ∀ {S₁ S₂ S₃ s} {σ₁ : S₁ →[ T ] S₂} {σ₂ : S₂ →[ T ] S₃} (t : S₁ ⊢ s) →
    (t ⋯ˢ σ₁) ⋯ˢ σ₂ ≡ t ⋯ˢ (λ _ x → (σ₁ _ x) ⋯ˢ σ₂)
  idᴿ-t : ∀ {S s} (t : S ⊢ s) → t ⋯ᴿ (λ _ x → x) ≡ t

  ---------------------------------------------------------------- the theory
  -- variable laws.  All mode-POLYMORPHIC: the m₁ = V clause of _⋯_ needs no
  -- mode dispatch, so one rule covers renaming and substitution at once.
  def-∙-zero : ∀ {m} {v : S₂ ⊢[ m ] s} {φ : S₁ →[ m ] S₂} → zero ⋯ (v ∙ φ) ≡ v
  def-∙-suc  : ∀ {m} {x : S₁ ∋ s} {v : S₂ ⊢[ m ] s′} {φ : S₁ →[ m ] S₂} →
    suc x ⋯ (v ∙ φ) ≡ x ⋯ φ
  -- these must commit to a mode: their RHS produces a VARIABLE, and var/⌞_⌟
  -- do not compute at an abstract mode.
  def-idᴿ : ∀ {x : S ∋ s} → x ⋯ (id {m = V}) ≡ x
  def-idˢ : ∀ {x : S ∋ s} → x ⋯ (id {m = T}) ≡ ` x
  def-wkᴿ : ∀ {s′} {x : S ∋ s} → x ⋯ (wk {m = V} s′) ≡ suc x
  def-wkˢ : ∀ {s′} {x : S ∋ s} → x ⋯ (wk {m = T} s′) ≡ ` (suc x)
  def-⨟      : ∀ {m₁ m₂} {x : S₁ ∋ s} {φ₁ : S₁ →[ m₁ ] S₂} {φ₂ : S₂ →[ m₂ ] S₃} →
    (x ⋯ φ₁) ⋯ φ₂ ≡ x ⋯ (φ₁ ⨟ φ₂)
  def-↑-zeroᴿ : ∀ {s′} {ρ : S₁ →[ V ] S₂} → zero ⋯ (ρ ↑ s′) ≡ zero
  def-↑-zeroˢ : ∀ {s′} {σ : S₁ →[ T ] S₂} → zero ⋯ (σ ↑ s′) ≡ ` zero
  -- lift's suc case names a MIXED composition φ ⨟ wk{V}: lifting weakens by a
  -- renaming at both modes, which is exactly what makes the recursion go.
  def-↑-sucᴿ : ∀ {s′} {x : S₁ ∋ s} {ρ : S₁ →[ V ] S₂} →
    suc x ⋯ (ρ ↑ s′) ≡ x ⋯ (ρ ⨟ wk {m = V} s′)
  def-↑-sucˢ : ∀ {s′} {x : S₁ ∋ s} {σ : S₁ →[ T ] S₂} →
    suc x ⋯ (σ ↑ s′) ≡ x ⋯ (σ ⨟ wk {m = V} s′)

  -- interaction laws
  assocᴿ : ∀ {m₂ m₃} {ρ₁ : S₁ →[ V ] S₂} {φ₂ : S₂ →[ m₂ ] S₃} {φ₃ : S₃ →[ m₃ ] S₄} →
    (ρ₁ ⨟ φ₂) ⨟ φ₃ ≡ ρ₁ ⨟ (φ₂ ⨟ φ₃)
  assocˢ : ∀ {m₂ m₃} {σ₁ : S₁ →[ T ] S₂} {φ₂ : S₂ →[ m₂ ] S₃} {φ₃ : S₃ →[ m₃ ] S₄} →
    (σ₁ ⨟ φ₂) ⨟ φ₃ ≡ σ₁ ⨟ (φ₂ ⨟ φ₃)
  dist : ∀ {m₁ m₂} {v : S₂ ⊢[ m₁ ] s} {φ₁ : S₁ →[ m₁ ] S₂} {φ₂ : S₂ →[ m₂ ] S₃} →
    (v ∙ φ₁) ⨟ φ₂ ≡ (v ⋯ φ₂) ∙ (φ₁ ⨟ φ₂)
  interact : ∀ {m s′} {v : S₂ ⊢[ m ] s′} {φ : S₁ →[ m ] S₂} →
    wk {m = V} s′ ⨟ (v ∙ φ) ≡ φ
  comp-idₗ : ∀ {m} {φ : S₁ →[ m ] S₂} → id {m = V} ⨟ φ ≡ φ
  comp-idᵣᴿ : ∀ {ρ : S₁ →[ V ] S₂} → ρ ⨟ id {m = V} ≡ ρ
  comp-idᵣˢ : ∀ {σ : S₁ →[ T ] S₂} → σ ⨟ id {m = T} ≡ σ

  -- lift laws (σ⇑: _↑_ is primitive)
  ↑-id : ∀ {m s′} → (id {S = S} {m = m}) ↑ s′ ≡ id {m = m}
  ↑-⨟  : ∀ {m₁ m₂ s′} {φ₁ : S₁ →[ m₁ ] S₂} {φ₂ : S₂ →[ m₂ ] S₃} →
    (φ₁ ↑ s′) ⨟ (φ₂ ↑ s′) ≡ (φ₁ ⨟ φ₂) ↑ s′
  ↑-consᴿ : ∀ {m₂ s′} {ρ₁ : S₁ →[ V ] S₂} {v : S₃ ⊢[ m₂ ] s′} {φ₂ : S₂ →[ m₂ ] S₃} →
    (ρ₁ ↑ s′) ⨟ (v ∙ φ₂) ≡ v ∙ (ρ₁ ⨟ φ₂)
  ↑-consˢ : ∀ {s′} {σ₁ : S₁ →[ T ] S₂} {v : S₃ ⊢[ T ] s′} {σ₂ : S₂ →[ T ] S₃} →
    (σ₁ ↑ s′) ⨟ (v ∙ σ₂) ≡ v ∙ (σ₁ ⨟ σ₂)
  wk-↑ᴿ : ∀ {s′} {ρ : S₁ →[ V ] S₂} →
    wk {m = V} s′ ⨟ (ρ ↑ s′) ≡ ρ ⨟ wk {m = V} s′
  wk-↑ˢ : ∀ {s′} {σ : S₁ →[ T ] S₂} →
    wk {m = V} s′ ⨟ (σ ↑ s′) ≡ σ ⨟ wk {m = V} s′

  -- completion rules (⨟-extended instances; Agda has no associative matching)
  def-⨟-wk : ∀ {m s′} {x : S₁ ∋ s} {φ : (s′ ∷ S₁) →[ m ] S₂} →
    x ⋯ (wk {m = V} s′ ⨟ φ) ≡ suc x ⋯ φ
  def-⨟-↑zeroᴿ : ∀ {m₂ s′} {ρ₁ : S₁ →[ V ] S₂} {φ₂ : (s′ ∷ S₂) →[ m₂ ] S₃} →
    zero ⋯ ((ρ₁ ↑ s′) ⨟ φ₂) ≡ zero ⋯ φ₂
  def-⨟-↑zeroˢᴿ : ∀ {s′} {σ₁ : S₁ →[ T ] S₂} {ρ₂ : (s′ ∷ S₂) →[ V ] S₃} →
    zero ⋯ ((σ₁ ↑ s′) ⨟ ρ₂) ≡ ` (zero ⋯ ρ₂)
  def-⨟-↑zeroˢˢ : ∀ {s′} {σ₁ : S₁ →[ T ] S₂} {σ₂ : (s′ ∷ S₂) →[ T ] S₃} →
    zero ⋯ ((σ₁ ↑ s′) ⨟ σ₂) ≡ zero ⋯ σ₂
  def-⨟-↑sucᴿ : ∀ {m₂ s′} {x : S₁ ∋ s} {ρ₁ : S₁ →[ V ] S₂} {φ₂ : (s′ ∷ S₂) →[ m₂ ] S₃} →
    suc x ⋯ ((ρ₁ ↑ s′) ⨟ φ₂) ≡ x ⋯ (ρ₁ ⨟ (wk {m = V} s′ ⨟ φ₂))
  def-⨟-↑sucˢ : ∀ {m₂ s′} {x : S₁ ∋ s} {σ₁ : S₁ →[ T ] S₂} {φ₂ : (s′ ∷ S₂) →[ m₂ ] S₃} →
    suc x ⋯ ((σ₁ ↑ s′) ⨟ φ₂) ≡ x ⋯ (σ₁ ⨟ (wk {m = V} s′ ⨟ φ₂))
  ↑-⨟-extᴿ : ∀ {m₂ m₃ s′} {ρ₁ : S₁ →[ V ] S₂} {φ₂ : S₂ →[ m₂ ] S₃} {φ₃ : (s′ ∷ S₃) →[ m₃ ] S₄} →
    (ρ₁ ↑ s′) ⨟ ((φ₂ ↑ s′) ⨟ φ₃) ≡ ((ρ₁ ⨟ φ₂) ↑ s′) ⨟ φ₃
  ↑-⨟-extˢ : ∀ {m₂ m₃ s′} {σ₁ : S₁ →[ T ] S₂} {φ₂ : S₂ →[ m₂ ] S₃} {φ₃ : (s′ ∷ S₃) →[ m₃ ] S₄} →
    (σ₁ ↑ s′) ⨟ ((φ₂ ↑ s′) ⨟ φ₃) ≡ ((σ₁ ⨟ φ₂) ↑ s′) ⨟ φ₃
  wk-↑-extᴿ : ∀ {m₃ s′} {ρ : S₁ →[ V ] S₂} {φ₃ : (s′ ∷ S₂) →[ m₃ ] S₃} →
    wk {m = V} s′ ⨟ ((ρ ↑ s′) ⨟ φ₃) ≡ ρ ⨟ (wk {m = V} s′ ⨟ φ₃)
  wk-↑-extˢ : ∀ {m₃ s′} {σ : S₁ →[ T ] S₂} {φ₃ : (s′ ∷ S₂) →[ m₃ ] S₃} →
    wk {m = V} s′ ⨟ ((σ ↑ s′) ⨟ φ₃) ≡ σ ⨟ (wk {m = V} s′ ⨟ φ₃)

  -- monad laws, mode-polymorphic
  right-id        : ∀ {m} (t : S ⊢ s) → t ⋯ (id {m = m}) ≡ t
  compositionality : ∀ {m₁ m₂} (t : S₁ ⊢ s) {φ₁ : S₁ →[ m₁ ] S₂} {φ₂ : S₂ →[ m₂ ] S₃} →
    (t ⋯ φ₁) ⋯ φ₂ ≡ t ⋯ (φ₁ ⨟ φ₂)

  -- traversal laws, mode-polymorphic.  inst-x is where the collapse shows: it
  -- subsumes both systemf.agda's inst-x and instᴿ-x, and systemfOne's def-⟨⟩.
  inst-xᴿ : ∀ {x : S₁ ∋ s} {ρ : S₁ →[ V ] S₂} → (` x) ⋯ ρ ≡ ` (x ⋯ ρ)
  inst-xˢ : ∀ {x : S₁ ∋ s} {σ : S₁ →[ T ] S₂} → (` x) ⋯ σ ≡ x ⋯ σ
  inst-λ : ∀ {m} {e : (expr ∷ S₁) ⊢ expr} {φ : S₁ →[ m ] S₂} →
    (λx e) ⋯ φ ≡ λx (e ⋯ (φ ↑ expr))
  inst-Λ : ∀ {m} {e : (type ∷ S₁) ⊢ expr} {φ : S₁ →[ m ] S₂} →
    (Λα e) ⋯ φ ≡ Λα (e ⋯ (φ ↑ type))
  inst-∀ : ∀ {m} {k : S₁ ⊢ kind} {t : (type ∷ S₁) ⊢ type} {φ : S₁ →[ m ] S₂} →
    (∀[α∶ k ] t) ⋯ φ ≡ ∀[α∶ k ⋯ φ ] (t ⋯ (φ ↑ type))
  inst-· : ∀ {m} {e₁ e₂ : S₁ ⊢ expr} {φ : S₁ →[ m ] S₂} →
    (e₁ · e₂) ⋯ φ ≡ (e₁ ⋯ φ) · (e₂ ⋯ φ)
  inst-• : ∀ {m} {e : S₁ ⊢ expr} {t : S₁ ⊢ type} {φ : S₁ →[ m ] S₂} →
    (e • t) ⋯ φ ≡ (e ⋯ φ) • (t ⋯ φ)
  inst-⇒ : ∀ {m} {t₁ t₂ : S₁ ⊢ type} {φ : S₁ →[ m ] S₂} →
    (t₁ ⇒ t₂) ⋯ φ ≡ (t₁ ⋯ φ) ⇒ (t₂ ⋯ φ)
  inst-* : ∀ {m} {φ : S₁ →[ m ] S₂} → (* {S = S₁}) ⋯ φ ≡ *

  ---------------------------------------------------------------- proofs

  ↑ᴿ-comp : ∀ {S₁ S₂ S₃ s′} {ρ₁ : S₁ →[ V ] S₂} {ρ₂ : S₂ →[ V ] S₃} →
    (λ s x → (ρ₂ ↑ᴿ s′) s ((ρ₁ ↑ᴿ s′) s x)) ≡ ((λ s x → ρ₂ s (ρ₁ s x)) ↑ᴿ s′)
  ↑ᴿ-comp = ext λ { zero → refl; (suc x) → refl }
  compᴿᴿ (` x)        = refl
  compᴿᴿ (λx e)       = cong λx_ (trans (compᴿᴿ e) (cong (e ⋯ᴿ_) ↑ᴿ-comp))
  compᴿᴿ (Λα e)       = cong Λα_ (trans (compᴿᴿ e) (cong (e ⋯ᴿ_) ↑ᴿ-comp))
  compᴿᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compᴿᴿ k) (trans (compᴿᴿ t) (cong (t ⋯ᴿ_) ↑ᴿ-comp))
  compᴿᴿ (e₁ · e₂)    = cong₂ _·_ (compᴿᴿ e₁) (compᴿᴿ e₂)
  compᴿᴿ (e • t)      = cong₂ _•_ (compᴿᴿ e) (compᴿᴿ t)
  compᴿᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compᴿᴿ t₁) (compᴿᴿ t₂)
  compᴿᴿ *            = refl

  ↑ᴿˢ-comp : ∀ {S₁ S₂ S₃ s′} {ρ₁ : S₁ →[ V ] S₂} {σ₂ : S₂ →[ T ] S₃} →
    (λ s x → (σ₂ ↑ˢ s′) s ((ρ₁ ↑ᴿ s′) s x)) ≡ ((λ s x → σ₂ s (ρ₁ s x)) ↑ˢ s′)
  ↑ᴿˢ-comp = ext λ { zero → refl; (suc x) → refl }
  compᴿˢ (` x)        = refl
  compᴿˢ {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compᴿˢ e) (cong (e ⋯ˢ_) (↑ᴿˢ-comp {σ₂ = σ₂})))
  compᴿˢ {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compᴿˢ e) (cong (e ⋯ˢ_) (↑ᴿˢ-comp {σ₂ = σ₂})))
  compᴿˢ {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compᴿˢ k) (trans (compᴿˢ t) (cong (t ⋯ˢ_) (↑ᴿˢ-comp {σ₂ = σ₂})))
  compᴿˢ (e₁ · e₂)    = cong₂ _·_ (compᴿˢ e₁) (compᴿˢ e₂)
  compᴿˢ (e • t)      = cong₂ _•_ (compᴿˢ e) (compᴿˢ t)
  compᴿˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compᴿˢ t₁) (compᴿˢ t₂)
  compᴿˢ *            = refl

  coincidence (` x)        = refl
  coincidence (λx e)       = cong λx_ (trans (coincidence e) (cong (e ⋯ˢ_) (ext λ { zero → refl ; (suc x) → refl })))
  coincidence (Λα e)       = cong Λα_ (trans (coincidence e) (cong (e ⋯ˢ_) (ext λ { zero → refl ; (suc x) → refl })))
  coincidence (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (coincidence k) (trans (coincidence t) (cong (t ⋯ˢ_) (ext λ { zero → refl ; (suc x) → refl })))
  coincidence (e₁ · e₂)    = cong₂ _·_ (coincidence e₁) (coincidence e₂)
  coincidence (e • t)      = cong₂ _•_ (coincidence e) (coincidence t)
  coincidence (t₁ ⇒ t₂)    = cong₂ _⇒_ (coincidence t₁) (coincidence t₂)
  coincidence *            = refl

  ↑ˢᴿ-comp : ∀ {S₁ S₂ S₃ s′} {σ₁ : S₁ →[ T ] S₂} {ρ₂ : S₂ →[ V ] S₃} →
    (λ s x → ((σ₁ ↑ˢ s′) s x) ⋯ᴿ (ρ₂ ↑ᴿ s′)) ≡ ((λ s x → (σ₁ s x) ⋯ᴿ ρ₂) ↑ˢ s′)
  ↑ˢᴿ-comp {σ₁ = σ₁} = ext λ { zero → refl
    ; (suc x) → trans (compᴿᴿ (σ₁ _ x)) (sym (compᴿᴿ (σ₁ _ x))) }
  compˢᴿ (` x)        = refl
  compˢᴿ {σ₁ = σ₁} (λx e)       = cong λx_ (trans (compˢᴿ e) (cong (e ⋯ˢ_) (↑ˢᴿ-comp {σ₁ = σ₁})))
  compˢᴿ {σ₁ = σ₁} (Λα e)       = cong Λα_ (trans (compˢᴿ e) (cong (e ⋯ˢ_) (↑ˢᴿ-comp {σ₁ = σ₁})))
  compˢᴿ {σ₁ = σ₁} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compˢᴿ k) (trans (compˢᴿ t) (cong (t ⋯ˢ_) (↑ˢᴿ-comp {σ₁ = σ₁})))
  compˢᴿ (e₁ · e₂)    = cong₂ _·_ (compˢᴿ e₁) (compˢᴿ e₂)
  compˢᴿ (e • t)      = cong₂ _•_ (compˢᴿ e) (compˢᴿ t)
  compˢᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compˢᴿ t₁) (compˢᴿ t₂)
  compˢᴿ *            = refl

  ↑ˢˢ-comp : ∀ {S₁ S₂ S₃ s′} {σ₁ : S₁ →[ T ] S₂} {σ₂ : S₂ →[ T ] S₃} →
    (λ s x → ((σ₁ ↑ˢ s′) s x) ⋯ˢ (σ₂ ↑ˢ s′)) ≡ ((λ s x → (σ₁ s x) ⋯ˢ σ₂) ↑ˢ s′)
  ↑ˢˢ-comp {σ₁ = σ₁} = ext λ { zero → refl
    ; (suc x) → trans (compᴿˢ (σ₁ _ x)) (sym (compˢᴿ (σ₁ _ x))) }
  compˢˢ (` x)        = refl
  compˢˢ {σ₁ = σ₁} (λx e)       = cong λx_ (trans (compˢˢ e) (cong (e ⋯ˢ_) (↑ˢˢ-comp {σ₁ = σ₁})))
  compˢˢ {σ₁ = σ₁} (Λα e)       = cong Λα_ (trans (compˢˢ e) (cong (e ⋯ˢ_) (↑ˢˢ-comp {σ₁ = σ₁})))
  compˢˢ {σ₁ = σ₁} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compˢˢ k) (trans (compˢˢ t) (cong (t ⋯ˢ_) (↑ˢˢ-comp {σ₁ = σ₁})))
  compˢˢ (e₁ · e₂)    = cong₂ _·_ (compˢˢ e₁) (compˢˢ e₂)
  compˢˢ (e • t)      = cong₂ _•_ (compˢˢ e) (compˢˢ t)
  compˢˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compˢˢ t₁) (compˢˢ t₂)
  compˢˢ *            = refl

  ↑ᴿ-idl : ∀ {S s′} → ((λ s (x : S ∋ s) → x) ↑ᴿ s′) ≡ (λ s x → x)
  ↑ᴿ-idl = ext λ { zero → refl; (suc x) → refl }
  idᴿ-t (` x)        = refl
  idᴿ-t (λx e)       = cong λx_ (trans (cong (e ⋯ᴿ_) ↑ᴿ-idl) (idᴿ-t e))
  idᴿ-t (Λα e)       = cong Λα_ (trans (cong (e ⋯ᴿ_) ↑ᴿ-idl) (idᴿ-t e))
  idᴿ-t (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (idᴿ-t k) (trans (cong (t ⋯ᴿ_) ↑ᴿ-idl) (idᴿ-t t))
  idᴿ-t (e₁ · e₂)    = cong₂ _·_ (idᴿ-t e₁) (idᴿ-t e₂)
  idᴿ-t (e • t)      = cong₂ _•_ (idᴿ-t e) (idᴿ-t t)
  idᴿ-t (t₁ ⇒ t₂)    = cong₂ _⇒_ (idᴿ-t t₁) (idᴿ-t t₂)
  idᴿ-t *            = refl

  idˢ-t : ∀ {S s} (t : S ⊢ s) → t ⋯ˢ (λ _ x → ` x) ≡ t
  ↑ˢ-idl : ∀ {S s′} → ((λ s (x : S ∋ s) → ` x) ↑ˢ s′) ≡ (λ s x → ` x)
  ↑ˢ-idl = ext λ { zero → refl; (suc x) → refl }
  idˢ-t (` x)        = refl
  idˢ-t (λx e)       = cong λx_ (trans (cong (e ⋯ˢ_) ↑ˢ-idl) (idˢ-t e))
  idˢ-t (Λα e)       = cong Λα_ (trans (cong (e ⋯ˢ_) ↑ˢ-idl) (idˢ-t e))
  idˢ-t (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (idˢ-t k) (trans (cong (t ⋯ˢ_) ↑ˢ-idl) (idˢ-t t))
  idˢ-t (e₁ · e₂)    = cong₂ _·_ (idˢ-t e₁) (idˢ-t e₂)
  idˢ-t (e • t)      = cong₂ _•_ (idˢ-t e) (idˢ-t t)
  idˢ-t (t₁ ⇒ t₂)    = cong₂ _⇒_ (idˢ-t t₁) (idˢ-t t₂)
  idˢ-t *            = refl

  -- the theory
  def-∙-zero = refl
  def-∙-suc  = refl
  def-idᴿ = refl
  def-idˢ = refl
  def-wkᴿ = refl
  def-wkˢ = refl
  def-⨟      = refl
  def-↑-zeroᴿ = refl
  def-↑-zeroˢ = refl
  def-↑-sucᴿ = refl
  def-↑-sucˢ = refl

  assocᴿ = ext λ x → refl
  assocˢ {m₂ = V} {m₃ = V} {σ₁ = σ₁} = ext λ x → compᴿᴿ (σ₁ _ x)
  assocˢ {m₂ = V} {m₃ = T} {σ₁ = σ₁} = ext λ x → compᴿˢ (σ₁ _ x)
  assocˢ {m₂ = T} {m₃ = V} {σ₁ = σ₁} = ext λ x → compˢᴿ (σ₁ _ x)
  assocˢ {m₂ = T} {m₃ = T} {σ₁ = σ₁} = ext λ x → compˢˢ (σ₁ _ x)
  dist      = ext λ { zero → refl; (suc x) → refl }
  interact  = ext λ x → refl
  comp-idₗ  = ext λ x → refl
  comp-idᵣᴿ = ext λ x → refl
  comp-idᵣˢ {σ = σ} = ext λ x → idˢ-t (σ _ x)

  ↑-id {m = V} = ext λ { zero → refl; (suc x) → refl }
  ↑-id {m = T} = ext λ { zero → refl; (suc x) → refl }
  ↑-⨟ {m₁ = V} {m₂ = V} = ext λ { zero → refl; (suc x) → refl }
  ↑-⨟ {m₁ = V} {m₂ = T} = ext λ { zero → refl; (suc x) → refl }
  ↑-⨟ {m₁ = T} {m₂ = V} {φ₁ = σ₁} = ext λ { zero → refl
    ; (suc x) → trans (compᴿᴿ (σ₁ _ x)) (sym (compᴿᴿ (σ₁ _ x))) }
  ↑-⨟ {m₁ = T} {m₂ = T} {φ₁ = σ₁} = ext λ { zero → refl
    ; (suc x) → trans (compᴿˢ (σ₁ _ x)) (sym (compˢᴿ (σ₁ _ x))) }
  ↑-consᴿ = ext λ { zero → refl; (suc x) → refl }
  ↑-consˢ {σ₁ = σ₁} = ext λ { zero → refl; (suc x) → compᴿˢ (σ₁ _ x) }
  wk-↑ᴿ = ext λ x → refl
  wk-↑ˢ = ext λ x → refl

  def-⨟-wk    = refl
  def-⨟-↑zeroᴿ = refl
  def-⨟-↑zeroˢᴿ = refl
  def-⨟-↑zeroˢˢ = refl
  def-⨟-↑sucᴿ = refl
  def-⨟-↑sucˢ {m₂ = V} {x = x} {σ₁ = σ₁} = compᴿᴿ (σ₁ _ x)
  def-⨟-↑sucˢ {m₂ = T} {x = x} {σ₁ = σ₁} = compᴿˢ (σ₁ _ x)
  ↑-⨟-extᴿ {s′ = s′} {ρ₁ = ρ₁} {φ₂ = φ₂} {φ₃ = φ₃} =
    trans (sym (assocᴿ {ρ₁ = ρ₁ ↑ s′} {φ₂ = φ₂ ↑ s′} {φ₃ = φ₃}))
          (cong (_⨟ φ₃) (↑-⨟ {φ₁ = ρ₁} {φ₂ = φ₂}))
  ↑-⨟-extˢ {s′ = s′} {σ₁ = σ₁} {φ₂ = φ₂} {φ₃ = φ₃} =
    trans (sym (assocˢ {σ₁ = σ₁ ↑ s′} {φ₂ = φ₂ ↑ s′} {φ₃ = φ₃}))
          (cong (_⨟ φ₃) (↑-⨟ {φ₁ = σ₁} {φ₂ = φ₂}))
  wk-↑-extᴿ {s′ = s′} {ρ = ρ} {φ₃ = φ₃} =
    trans (sym (assocᴿ {ρ₁ = wk {m = V} s′} {φ₂ = ρ ↑ s′} {φ₃ = φ₃}))
          (trans (cong (_⨟ φ₃) (wk-↑ᴿ {ρ = ρ}))
                 (assocᴿ {ρ₁ = ρ} {φ₂ = wk {m = V} s′} {φ₃ = φ₃}))
  wk-↑-extˢ {s′ = s′} {σ = σ} {φ₃ = φ₃} =
    trans (sym (assocᴿ {ρ₁ = wk {m = V} s′} {φ₂ = σ ↑ s′} {φ₃ = φ₃}))
          (trans (cong (_⨟ φ₃) (wk-↑ˢ {σ = σ}))
                 (assocˢ {σ₁ = σ} {φ₂ = wk {m = V} s′} {φ₃ = φ₃}))

  right-id {m = V} t = idᴿ-t t
  right-id {m = T} t = idˢ-t t
  compositionality {m₁ = V} {m₂ = V} t = compᴿᴿ t
  compositionality {m₁ = V} {m₂ = T} t = compᴿˢ t
  compositionality {m₁ = T} {m₂ = V} t = compˢᴿ t
  compositionality {m₁ = T} {m₂ = T} t = compˢˢ t

  inst-xᴿ = refl
  inst-xˢ = refl
  inst-λ {m = V} = refl
  inst-λ {m = T} = refl
  inst-Λ {m = V} = refl
  inst-Λ {m = T} = refl
  inst-∀ {m = V} = refl
  inst-∀ {m = T} = refl
  inst-· {m = V} = refl
  inst-· {m = T} = refl
  inst-• {m = V} = refl
  inst-• {m = T} = refl
  inst-⇒ {m = V} = refl
  inst-⇒ {m = T} = refl
  inst-* {m = V} = refl
  inst-* {m = T} = refl

{-# REWRITE
def-∙-zero def-∙-suc def-idᴿ def-idˢ def-wkᴿ def-wkˢ def-⨟
def-↑-zeroᴿ def-↑-zeroˢ def-↑-sucᴿ def-↑-sucˢ
assocᴿ assocˢ dist interact comp-idₗ comp-idᵣᴿ comp-idᵣˢ
↑-id ↑-⨟ ↑-consᴿ ↑-consˢ wk-↑ᴿ wk-↑ˢ
def-⨟-wk def-⨟-↑zeroᴿ def-⨟-↑zeroˢᴿ def-⨟-↑zeroˢˢ def-⨟-↑sucᴿ def-⨟-↑sucˢ
↑-⨟-extᴿ ↑-⨟-extˢ wk-↑-extᴿ wk-↑-extˢ
right-id compositionality
inst-xᴿ inst-xˢ inst-λ inst-Λ inst-∀ inst-· inst-• inst-⇒ inst-*
#-}

------------------------------------------------------------------------
-- The negative result, checked.
--
-- Collapsing the two algebras did NOT remove the coercion: ⟨_⟩ is DEFINABLE in
-- the mode-indexed algebra as id{T} ⨟ ρ.  Making it not-a-former only renames
-- it, so the obstruction it caused in systemfOne.agda survives the collapse in
-- derived form — and now every mixed-mode composition can produce one.
------------------------------------------------------------------------
opaque
  unfolding id _⋯_ _⨟_

  coercion-is-definable : ∀ {S₁ S₂ s} (x : S₁ ∋ s) (ρ : S₁ →[ V ] S₂) →
    (id {m = T} ⨟ ρ) s x ≡ ` (ρ s x)
  coercion-is-definable x ρ = refl
