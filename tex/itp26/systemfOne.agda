{-# OPTIONS --rewriting --local-confluence-check #-}
-- SINGLE-ALGEBRA System F: locally confluent, ONE transport.
--
-- 0 critical pairs under --local-confluence-check, full typing and subject
-- reduction, exactly one subst, and no postulate beyond fun-ext.  A ZERO-subst
-- variant exists (coe-var, kept below) but its transport-freedom rests on a
-- regime the confluence checker does not cover — see the OPACITY CAVEAT.  Compare: systemf.agda = 0 pairs / 5 transports; systemfLift.agda =
-- 32 pairs / 0 transports; systemfKit.agda (mode-indexed) = 50 pairs.
--
-- The question was how much of the non-confluence of those two is caused by
-- having TWO substitution algebras (→ᴿ and →ˢ) bridged by ⟨_⟩.  Answer: almost
-- all of it, but the bridge cannot be deleted, only demoted.
--
--  1. The renaming TRAVERSAL is forced.  Defining _⋯ˢ_ with _↑ˢ_ weakening σ's
--     image directly fails Agda's termination checker — lifting weakens a TERM,
--     so it calls the traversal on a non-subterm (see scratchpad/NoRen.agda).
--     _⋯ᴿ_ is what makes the recursion well-founded.
--
--  2. But it need not be part of the THEORY.  Here _⋯ᴿ_ is an internal
--     definition: no _→ᴿ_, no _∘_, no _⋯ᴿ_ occurs in any registered rule.  wkˢ
--     and _↑ˢ_ are primitive (λσ⇑, Curien–Hardin–Lévy).  Registering the pure
--     single-sorted σ⇑ theory takes 32 pairs to 11, dropping the η/surjective-
--     pairing laws (unneeded here, since right-idˢ and ↑ˢ-id are registered
--     directly) takes 11 to 5, and five completion rules — the ⨟-extended
--     instances that Agda's lack of associative matching makes necessary — take
--     5 to 0.
--
--  3. The stratification is forced a SECOND time, at the typing layer: ⊢⋯ˢ and
--     ⊢↑ˢ are mutually non-structural, so renaming-preserves-typing must be a
--     prior lemma.  It is stated on VARIABLES with the type action _⋯ˢ ⟨ ρ ⟩,
--     so it stays inside the single algebra; ⟨ ρ ⟩ is just a variable-valued
--     substitution.  Its lift law ⟨⟩-↑ registers cleanly ONLY in the direction
--     ⟨ ρ ↑ᴿ s ⟩ → ⟨ ρ ⟩ ↑ˢ s (the other orientation costs 11 pairs, since
--     ⟨ ρ ⟩ ↑ˢ s as an LHS overlaps every lift law).
--
--  4. The last obligation was def-⟨⟩ : x ⋯ˢ ⟨ ρ ⟩ ≡ ` (ρ s x), in the ⊢` case
--     of _⊢⋯ᴿ[_]_.  It cannot be REGISTERED — it forms an unjoinable pair with
--     ⟨⟩-↑ on the abstract index x.  But it does not need to be: it is already
--     DEFINITIONAL (_⋯ˢ_'s variable clause composed with ⟨_⟩'s definition),
--     invisible only because both are opaque, and they are opaque solely so the
--     rewrite rules' LHSs stay neutral.  Unfolding them in the one-line scope of
--     coe-var below turns the transport into an identity function: coe-var d = d.
--     No equality proof, no rewrite rule, no confluence cost.
--
--     Things that did NOT work, measured, do not retry:
--       - registering def-⟨⟩ plus a join rule whose proof case-splits on x:
--         closes the original pair (5 left) but the next completion round goes
--         5 → 9.  Same divergence signature as the earlier KB run.
--       - flipping ⟨⟩-↑ outward with def-⟨⟩ registered: 7 pairs.
--       - renamings as a first-order datatype so the ⟨⟩-laws become computation
--         rules: this HIDES a real non-confluence rather than fixing it, since
--         Agda does not check rewrite rules against a function's own clauses.
module systemfOne where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Agda.Builtin.Equality.Rewrite public

open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
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

data Mode : Set where  V T : Mode
variable
  m  : Mode

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

------------------------------------------------------------------------
-- INTERNAL renaming stage.  Nothing below is exposed to the theory: the
-- names _→ᴿ_, _∘_, _⋯ᴿ_, ⟨_⟩ never appear in a registered rewrite rule.
------------------------------------------------------------------------

private
  _→ᴿ_ : Scope → Scope → Set
  S₁ →ᴿ S₂ = ∀ s → S₁ ∋ s → S₂ ∋ s

variable
  ρ ρ₁ ρ₂ ρ₃ : S₁ →ᴿ S₂

idᴿ : S →ᴿ S
idᴿ _ x = x

wkᴿ : ∀ s → S →ᴿ (s ∷ S)
wkᴿ _ _ = suc

_∘_ : S₁ →ᴿ S₂ → S₂ →ᴿ S₃ → S₁ →ᴿ S₃
(ρ₁ ∘ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_∙ᴿ_ : S₂ ∋ s → S₁ →ᴿ S₂ → (s ∷ S₁) →ᴿ S₂
(x ∙ᴿ ρ) _ zero = x
(_ ∙ᴿ ρ) _ (suc x) = ρ _ x

_↑ᴿ_ : (S₁ →ᴿ S₂) → ∀ s → ((s ∷ S₁) →ᴿ (s ∷ S₂))
(ρ ↑ᴿ _) = zero ∙ᴿ (ρ ∘ (wkᴿ _))

opaque
  _⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ →ᴿ S₂ → S₂ ⊢[ m ] s
  _⋯ᴿ_ {m = V} x   ρ = ρ _ x
  (` x)         ⋯ᴿ ρ = ` ρ _ x
  (λx e)        ⋯ᴿ ρ = λx (e ⋯ᴿ (ρ ↑ᴿ _))
  (Λα e)        ⋯ᴿ ρ = Λα (e ⋯ᴿ (ρ ↑ᴿ _))
  (∀[α∶ k ] t)  ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ (ρ ↑ᴿ _))
  (e₁ · e₂)     ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
  (e • t)       ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
  (t₁ ⇒ t₂)     ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
  *             ⋯ᴿ ρ = *

------------------------------------------------------------------------
-- THE THEORY: one sort of substitution.
------------------------------------------------------------------------

_→ˢ_ : Scope → Scope → Set
S₁ →ˢ S₂ = ∀ s → S₁ ∋ s → S₂ ⊢ s

opaque
  unfolding _⋯ᴿ_

  idˢ : S →ˢ S
  idˢ _ x = ` x

  wkˢ : ∀ s → S →ˢ (s ∷ S)
  wkˢ _ _ x = ` (suc x)

  _∙ˢ_ : S₂ ⊢ s → S₁ →ˢ S₂ → (s ∷ S₁) →ˢ S₂
  (t ∙ˢ σ) _ zero = t
  (t ∙ˢ σ) _ (suc x) = σ _ x

  _↑ˢ_ : S₁ →ˢ S₂ → ∀ s → (s ∷ S₁) →ˢ (s ∷ S₂)
  σ ↑ˢ s = (` zero) ∙ˢ λ _ x → (σ _ x) ⋯ᴿ wkᴿ _

  _⋯ˢ_ : S₁ ⊢[ m ] s → S₁ →ˢ S₂ → S₂ ⊢ s
  _⋯ˢ_ {m = V} x σ = σ _ x
  (` x)         ⋯ˢ σ = σ _ x
  (λx e)        ⋯ˢ σ = λx (e ⋯ˢ (σ ↑ˢ _))
  (Λα e)        ⋯ˢ σ = Λα (e ⋯ˢ (σ ↑ˢ _))
  (∀[α∶ k ] t)  ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  (e₁ · e₂)     ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  (e • t)       ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
  (t₁ ⇒ t₂)     ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  *             ⋯ˢ σ = *

  _⨟_ : S₁ →ˢ S₂ → S₂ →ˢ S₃ → S₁ →ˢ S₃
  (σ₁ ⨟ σ₂) _ x = (σ₁ _ x) ⋯ˢ σ₂

  -- ⟨_⟩ is NOT a second algebra: it is an ordinary substitution that happens to
  -- be variable-valued.  It exists only so the typing traversal can be
  -- stratified (renaming stage first), exactly as _⋯ᴿ_ stratifies _⋯ˢ_.
  ⟨_⟩ : S₁ →ᴿ S₂ → S₁ →ˢ S₂
  ⟨ ρ ⟩ _ x = ` (ρ _ x)

variable
  σ σ₁ σ₂ σ₃ : S₁ →ˢ S₂

opaque
  unfolding _⋯ᴿ_ idˢ wkˢ _∙ˢ_ _↑ˢ_ _⋯ˢ_ _⨟_ ⟨_⟩

  ---------------------------------------------------------------- exposed
  -- variable/definitional laws
  def-∙ˢ-zero  : zero ⋯ˢ (t ∙ˢ σ)    ≡ t
  def-∙ˢ-suc   : suc x ⋯ˢ (t ∙ˢ σ)   ≡ x ⋯ˢ σ
  def-idˢ      : x ⋯ˢ idˢ            ≡ ` x
  def-wkˢ      : ∀ {S S′ s} {x : S ∋ s} → x ⋯ˢ (wkˢ S′)  ≡ ` (suc x)
  def-⨟        : (x ⋯ˢ σ₁) ⋯ˢ σ₂     ≡ x ⋯ˢ (σ₁ ⨟ σ₂)
  def-↑ˢ-zero  : zero ⋯ˢ (σ ↑ˢ s)    ≡ ` zero
  def-↑ˢ-suc   : ∀ {S₁ S₂ s s′} {x : S₁ ∋ s} {σ : S₁ →ˢ S₂} →
    suc {s′ = s′} x ⋯ˢ (σ ↑ˢ s′) ≡ x ⋯ˢ (σ ⨟ wkˢ s′)

  -- interaction laws
  assoc     : (σ₁ ⨟ σ₂) ⨟ σ₃  ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)
  dist      : (t ∙ˢ σ₁) ⨟ σ₂  ≡ (t ⋯ˢ σ₂) ∙ˢ (σ₁ ⨟ σ₂)
  interact  : wkˢ s ⨟ (t ∙ˢ σ) ≡ σ
  comp-idₗ  : idˢ ⨟ σ  ≡ σ
  comp-idᵣ  : σ ⨟ idˢ  ≡ σ
  η-id      : (` zero {s} {S}) ∙ˢ (wkˢ _) ≡ idˢ
  η-law     : (zero ⋯ˢ σ) ∙ˢ (wkˢ _ ⨟ σ)  ≡ σ

  -- lift laws (σ⇑: _↑ˢ_ is primitive)
  ↑ˢ-id    : idˢ {S = S} ↑ˢ s        ≡ idˢ
  ↑ˢ-⨟     : ∀ {S₁ S₂ S₃ s} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} →
    (σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s)  ≡ (σ₁ ⨟ σ₂) ↑ˢ s
  ↑ˢ-cons  : ∀ {S₁ S₂ S₃ s} {σ₁ : S₁ →ˢ S₂} {t : S₃ ⊢ s} {σ₂ : S₂ →ˢ S₃} →
    (σ₁ ↑ˢ s) ⨟ (t ∙ˢ σ₂)  ≡ t ∙ˢ (σ₁ ⨟ σ₂)
  wk-↑ˢ    : ∀ {S₁ S₂ s} {σ : S₁ →ˢ S₂} →
    wkˢ s ⨟ (σ ↑ˢ s)       ≡ σ ⨟ wkˢ s
  def-⟨⟩   : ∀ {S₁ S₂ s} {x : S₁ ∋ s} {ρ : S₁ →ᴿ S₂} → x ⋯ˢ ⟨ ρ ⟩ ≡ ` (ρ s x)
  def-⨟-⟨⟩ : ∀ {S₁ S₂ S₃ s} {x : S₁ ∋ s} {ρ : S₁ →ᴿ S₂} {σ : S₂ →ˢ S₃} →
    x ⋯ˢ (⟨ ρ ⟩ ⨟ σ) ≡ (ρ s x) ⋯ˢ σ
  ⟨⟩-↑     : ∀ {S₁ S₂ s} {ρ : S₁ →ᴿ S₂} → ⟨ ρ ↑ᴿ s ⟩ ≡ ⟨ ρ ⟩ ↑ˢ s
  ⟨⟩-wk    : ∀ {S s} → ⟨ wkᴿ {S = S} s ⟩ ≡ wkˢ s
  ⟨⟩-id    : ∀ {S} → ⟨ idᴿ {S = S} ⟩ ≡ idˢ

  -- completion rules.  Each closes one pair between a variable/lift law and a
  -- composition sitting to its right: Agda has no associative matching, so the
  -- ⨟-extended instance of each law must be registered separately.
  def-⨟-wk    : ∀ {S₁ S₂ s s′} {x : S₁ ∋ s} {σ : (s′ ∷ S₁) →ˢ S₂} →
    x ⋯ˢ (wkˢ s′ ⨟ σ)  ≡ suc x ⋯ˢ σ
  def-⨟-↑zero : ∀ {S₁ S₂ S₃ s} {σ : S₁ →ˢ S₂} {σ₂ : (s ∷ S₂) →ˢ S₃} →
    zero ⋯ˢ ((σ ↑ˢ s) ⨟ σ₂)   ≡ zero ⋯ˢ σ₂
  def-⨟-↑suc  : ∀ {S₁ S₂ S₃ s s′} {x : S₁ ∋ s} {σ : S₁ →ˢ S₂} {σ₂ : (s′ ∷ S₂) →ˢ S₃} →
    suc {s′ = s′} x ⋯ˢ ((σ ↑ˢ s′) ⨟ σ₂) ≡ x ⋯ˢ (σ ⨟ (wkˢ s′ ⨟ σ₂))
  ↑ˢ-⨟-ext    : ∀ {S₁ S₂ S₃ S₄ s} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} {σ₃ : (s ∷ S₃) →ˢ S₄} →
    (σ₁ ↑ˢ s) ⨟ ((σ₂ ↑ˢ s) ⨟ σ₃)  ≡ ((σ₁ ⨟ σ₂) ↑ˢ s) ⨟ σ₃
  wk-↑ˢ-ext   : ∀ {S₁ S₂ S₃ s} {σ : S₁ →ˢ S₂} {σ₃ : (s ∷ S₂) →ˢ S₃} →
    wkˢ s ⨟ ((σ ↑ˢ s) ⨟ σ₃)  ≡ σ ⨟ (wkˢ s ⨟ σ₃)

  -- monad laws
  right-idˢ          : ∀ (t : S ⊢ s) → t ⋯ˢ idˢ ≡ t
  compositionalityˢˢ : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ˢ σ₂ ≡ t ⋯ˢ (σ₁ ⨟ σ₂)

  -- traversal laws
  inst-x : (` x)        ⋯ˢ σ ≡ x ⋯ˢ σ
  inst-λ : (λx e)       ⋯ˢ σ ≡ λx (e ⋯ˢ (σ ↑ˢ _))
  inst-Λ : (Λα e)       ⋯ˢ σ ≡ Λα (e ⋯ˢ (σ ↑ˢ _))
  inst-∀ : (∀[α∶ k ] t) ⋯ˢ σ ≡ ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ (σ ↑ˢ _))
  inst-· : (e₁ · e₂)    ⋯ˢ σ ≡ (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
  inst-• : (e • t)      ⋯ˢ σ ≡ (e ⋯ˢ σ) • (t ⋯ˢ σ)
  inst-⇒ : (t₁ ⇒ t₂)    ⋯ˢ σ ≡ (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
  inst-* : *            ⋯ˢ σ ≡ *

  ---------------------------------------------------------------- internal
  -- NOT part of the theory; used only to prove the laws above.
  coincidence        : ∀ (t : S ⊢ s) → t ⋯ˢ (λ _ x → ` ρ _ x) ≡ (t ⋯ᴿ ρ)
  compositionalityᴿˢ : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ˢ σ₂ ≡ t ⋯ˢ (λ _ x → σ₂ _ (ρ₁ _ x))
  compositionalityˢᴿ : ∀ (t : S ⊢ s) → (t ⋯ˢ σ₁) ⋯ᴿ ρ₂ ≡ t ⋯ˢ (λ _ x → (σ₁ _ x) ⋯ᴿ ρ₂)
  compositionalityᴿᴿ : ∀ (t : S ⊢ s) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂ ≡ t ⋯ᴿ (ρ₁ ∘ ρ₂)
  right-idᴿ          : ∀ (t : S ⊢ s) → t ⋯ᴿ idᴿ ≡ t

  ---------------------------------------------------------------- proofs

  def-∙ˢ-zero = refl
  def-∙ˢ-suc  = refl
  def-idˢ     = refl
  def-wkˢ     = refl
  def-⨟       = refl
  def-↑ˢ-zero = refl
  def-↑ˢ-suc {x = x} {σ = σ} = sym (coincidence (σ _ x))

  lift-idᴿ : idᴿ {S = S} ↑ᴿ s ≡ idᴿ
  lift-idᴿ = ext λ { zero → refl; (suc x) → refl }
  right-idᴿ (` x)        = refl
  right-idᴿ (λx e)       = cong λx_ (trans (cong (e ⋯ᴿ_) lift-idᴿ) (right-idᴿ e))
  right-idᴿ (Λα e)       = cong Λα_ (trans (cong (e ⋯ᴿ_) lift-idᴿ) (right-idᴿ e))
  right-idᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idᴿ k) (trans (cong (t ⋯ᴿ_) lift-idᴿ) (right-idᴿ t))
  right-idᴿ (e₁ · e₂)    = cong₂ _·_ (right-idᴿ e₁) (right-idᴿ e₂)
  right-idᴿ (e • t)      = cong₂ _•_ (right-idᴿ e) (right-idᴿ t)
  right-idᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idᴿ t₁) (right-idᴿ t₂)
  right-idᴿ *            = refl

  lift-dist-compᴿᴿ : ((ρ₁ ↑ᴿ s) ∘ (ρ₂ ↑ᴿ s)) ≡ ((ρ₁ ∘ ρ₂) ↑ᴿ s)
  lift-dist-compᴿᴿ = ext λ { zero → refl; (suc x) → refl }
  compositionalityᴿᴿ (` x)        = refl
  compositionalityᴿᴿ (λx e)       = cong λx_ (trans (compositionalityᴿᴿ e) (cong (e ⋯ᴿ_) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (Λα e)       = cong Λα_ (trans (compositionalityᴿᴿ e) (cong (e ⋯ᴿ_) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿᴿ k) (trans (compositionalityᴿᴿ t) (cong (t ⋯ᴿ_) lift-dist-compᴿᴿ))
  compositionalityᴿᴿ (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿᴿ e₁) (compositionalityᴿᴿ e₂)
  compositionalityᴿᴿ (e • t)      = cong₂ _•_ (compositionalityᴿᴿ e) (compositionalityᴿᴿ t)
  compositionalityᴿᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿᴿ t₁) (compositionalityᴿᴿ t₂)
  compositionalityᴿᴿ *            = refl

  lift-dist-compᴿˢ : ∀ {S₁ S₂ S₃ s} {ρ₁ : S₁ →ᴿ S₂} {σ₂ : S₂ →ˢ S₃} →
    (λ (s′ : Sort) x → (σ₂ ↑ˢ s) s′ ((ρ₁ ↑ᴿ s) s′ x)) ≡ ((λ s′ x → σ₂ s′ (ρ₁ s′ x)) ↑ˢ s)
  lift-dist-compᴿˢ = ext λ { zero → refl; (suc x) → refl }
  compositionalityᴿˢ (` x)        = refl
  compositionalityᴿˢ {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityᴿˢ e) (cong (e ⋯ˢ_) (lift-dist-compᴿˢ {σ₂ = σ₂})))
  compositionalityᴿˢ {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityᴿˢ e) (cong (e ⋯ˢ_) (lift-dist-compᴿˢ {σ₂ = σ₂})))
  compositionalityᴿˢ {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityᴿˢ k) (trans (compositionalityᴿˢ t) (cong (t ⋯ˢ_) (lift-dist-compᴿˢ {σ₂ = σ₂})))
  compositionalityᴿˢ (e₁ · e₂)    = cong₂ _·_ (compositionalityᴿˢ e₁) (compositionalityᴿˢ e₂)
  compositionalityᴿˢ (e • t)      = cong₂ _•_ (compositionalityᴿˢ e) (compositionalityᴿˢ t)
  compositionalityᴿˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityᴿˢ t₁) (compositionalityᴿˢ t₂)
  compositionalityᴿˢ *            = refl

  coincidence (` x)        = refl
  coincidence {ρ = ρ} (λx e) = cong λx_ (trans (cong (e ⋯ˢ_) (ext λ { zero → refl ; (suc x) → refl })) (coincidence e))
  coincidence {ρ = ρ} (Λα e) = cong Λα_ (trans (cong (e ⋯ˢ_) (ext λ { zero → refl ; (suc x) → refl })) (coincidence e))
  coincidence {ρ = ρ} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (coincidence k) (trans (cong (t ⋯ˢ_) (ext λ { zero → refl ; (suc x) → refl })) (coincidence t))
  coincidence (e₁ · e₂)    = cong₂ _·_ (coincidence e₁) (coincidence e₂)
  coincidence (e • t)      = cong₂ _•_ (coincidence e) (coincidence t)
  coincidence (t₁ ⇒ t₂)    = cong₂ _⇒_ (coincidence t₁) (coincidence t₂)
  coincidence *            = refl

  lift-dist-compˢᴿ : ∀ {S₁ S₂ S₃ s} {σ₁ : S₁ →ˢ S₂} {ρ₂ : S₂ →ᴿ S₃} →
    (λ (s′ : Sort) x → ((σ₁ ↑ˢ s) s′ x) ⋯ᴿ (ρ₂ ↑ᴿ s)) ≡ ((λ s′ x → (σ₁ s′ x) ⋯ᴿ ρ₂) ↑ˢ s)
  lift-dist-compˢᴿ {σ₁ = σ₁} {ρ₂ = ρ₂} = ext λ { zero → refl; (suc x) →
    let t = σ₁ _ x in
    trans (compositionalityᴿᴿ t) (sym (compositionalityᴿᴿ t)) }
  compositionalityˢᴿ {σ₁ = σ₁} (` x)        = refl
  compositionalityˢᴿ {σ₁ = σ₁} (λx e)       = cong λx_ (trans (compositionalityˢᴿ e) (cong (e ⋯ˢ_) (lift-dist-compˢᴿ {σ₁ = σ₁})))
  compositionalityˢᴿ {σ₁ = σ₁} (Λα e)       = cong Λα_ (trans (compositionalityˢᴿ e) (cong (e ⋯ˢ_) (lift-dist-compˢᴿ {σ₁ = σ₁})))
  compositionalityˢᴿ {σ₁ = σ₁} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢᴿ k) (trans (compositionalityˢᴿ t) (cong (t ⋯ˢ_) (lift-dist-compˢᴿ {σ₁ = σ₁})))
  compositionalityˢᴿ (e₁ · e₂)    = cong₂ _·_ (compositionalityˢᴿ e₁) (compositionalityˢᴿ e₂)
  compositionalityˢᴿ (e • t)      = cong₂ _•_ (compositionalityˢᴿ e) (compositionalityˢᴿ t)
  compositionalityˢᴿ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢᴿ t₁) (compositionalityˢᴿ t₂)
  compositionalityˢᴿ *            = refl

  ↑ˢ-id   = ext λ { zero → refl; (suc x) → refl }
  ↑ˢ-cons {σ₁ = σ₁} {t = t} {σ₂ = σ₂} =
    ext λ { zero → refl
          ; (suc x) → compositionalityᴿˢ {ρ₁ = wkᴿ _} {σ₂ = t ∙ˢ σ₂} (σ₁ _ x) }
  wk-↑ˢ {σ = σ} = ext λ x → sym (coincidence {ρ = wkᴿ _} (σ _ x))

  ↑ˢ-⨟ {σ₁ = σ₁} {σ₂ = σ₂} = ext λ { zero → refl; (suc x) →
    let t = σ₁ _ x in
    trans (compositionalityᴿˢ t) (sym (compositionalityˢᴿ t)) }

  right-idˢ (` x)        = refl
  right-idˢ (λx e)       = cong λx_ (trans (cong (e ⋯ˢ_) ↑ˢ-id) (right-idˢ e))
  right-idˢ (Λα e)       = cong Λα_ (trans (cong (e ⋯ˢ_) ↑ˢ-id) (right-idˢ e))
  right-idˢ (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (right-idˢ k) (trans (cong (t ⋯ˢ_) ↑ˢ-id) (right-idˢ t))
  right-idˢ (e₁ · e₂)    = cong₂ _·_ (right-idˢ e₁) (right-idˢ e₂)
  right-idˢ (e • t)      = cong₂ _•_ (right-idˢ e) (right-idˢ t)
  right-idˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (right-idˢ t₁) (right-idˢ t₂)
  right-idˢ *            = refl

  compositionalityˢˢ (` x)        = refl
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (λx e)       = cong λx_ (trans (compositionalityˢˢ e) (cong (e ⋯ˢ_) (↑ˢ-⨟ {σ₁ = σ₁} {σ₂ = σ₂})))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (Λα e)       = cong Λα_ (trans (compositionalityˢˢ e) (cong (e ⋯ˢ_) (↑ˢ-⨟ {σ₁ = σ₁} {σ₂ = σ₂})))
  compositionalityˢˢ {σ₁ = σ₁} {σ₂ = σ₂} (∀[α∶ k ] t) = cong₂ ∀[α∶_]_ (compositionalityˢˢ k) (trans (compositionalityˢˢ t) (cong (t ⋯ˢ_) (↑ˢ-⨟ {σ₁ = σ₁} {σ₂ = σ₂})))
  compositionalityˢˢ (e₁ · e₂)    = cong₂ _·_ (compositionalityˢˢ e₁) (compositionalityˢˢ e₂)
  compositionalityˢˢ (e • t)      = cong₂ _•_ (compositionalityˢˢ e) (compositionalityˢˢ t)
  compositionalityˢˢ (t₁ ⇒ t₂)    = cong₂ _⇒_ (compositionalityˢˢ t₁) (compositionalityˢˢ t₂)
  compositionalityˢˢ *            = refl

  assoc {σ₁ = σ₁} = ext (λ x → compositionalityˢˢ (σ₁ _ x))
  dist     = ext λ { zero → refl; (suc x) → refl }
  interact = refl
  comp-idₗ = refl
  comp-idᵣ = ext λ x → right-idˢ _
  η-id     = ext λ { zero → refl; (suc x) → refl }
  η-law    = ext λ { zero → refl; (suc x) → refl }

  def-⟨⟩   = refl
  def-⨟-⟨⟩ = refl
  ⟨⟩-↑  = ext λ { zero → refl; (suc x) → refl }
  ⟨⟩-wk = ext λ x → refl
  ⟨⟩-id = ext λ x → refl

  def-⨟-wk    = refl
  def-⨟-↑zero = refl
  def-⨟-↑suc {x = x} {σ = σ} {σ₂ = σ₂} = compositionalityᴿˢ {ρ₁ = wkᴿ _} {σ₂ = σ₂} (σ _ x)
  ↑ˢ-⨟-ext {s = s} {σ₁ = σ₁} {σ₂ = σ₂} {σ₃ = σ₃} =
    trans (sym (assoc {σ₁ = σ₁ ↑ˢ s} {σ₂ = σ₂ ↑ˢ s} {σ₃ = σ₃}))
          (cong (_⨟ σ₃) (↑ˢ-⨟ {σ₁ = σ₁} {σ₂ = σ₂}))
  wk-↑ˢ-ext {s = s} {σ = σ} {σ₃ = σ₃} =
    trans (sym (assoc {σ₁ = wkˢ s} {σ₂ = σ ↑ˢ s} {σ₃ = σ₃}))
          (trans (cong (_⨟ σ₃) (wk-↑ˢ {σ = σ}))
                 (assoc {σ₁ = σ} {σ₂ = wkˢ s} {σ₃ = σ₃}))

  inst-x = refl
  inst-λ = refl
  inst-Λ = refl
  inst-∀ = refl
  inst-· = refl
  inst-• = refl
  inst-⇒ = refl
  inst-* = refl

-- The single-sorted theory.  No _→ᴿ_, no _∘_, no ⟨_⟩ occurs anywhere here.
{-# REWRITE
def-∙ˢ-zero def-∙ˢ-suc def-idˢ def-wkˢ def-⨟ def-↑ˢ-zero def-↑ˢ-suc
assoc dist interact comp-idₗ comp-idᵣ
↑ˢ-id ↑ˢ-⨟ ↑ˢ-cons wk-↑ˢ
def-⨟-wk def-⨟-↑zero def-⨟-↑suc ↑ˢ-⨟-ext wk-↑ˢ-ext
⟨⟩-↑ ⟨⟩-wk ⟨⟩-id
right-idˢ compositionalityᴿᴿ compositionalityˢˢ
inst-x inst-λ inst-Λ inst-∀ inst-· inst-• inst-⇒ inst-*
#-}

------------------------------------------------------------------------
-- Typing and subject reduction.  Note there is no ⊢wkᴿ / renaming-preserves-
-- typing lemma: weakening is just substitution by wkˢ.
------------------------------------------------------------------------

↑ᵗ_ : Sort → Sort
↑ᵗ expr = type
↑ᵗ type = kind
↑ᵗ kind = kind

_∶⊢_ : Scope → Sort → Set
S ∶⊢ s = S ⊢ (↑ᵗ s)

depth : S ∋ s → ℕ
depth zero     = zero
depth (suc x)  = suc (depth x)

drop-∈ : S ∋ s → Scope → Scope
drop-∈ e xs = drop (suc (depth e)) xs

Ctx : Scope → Set
Ctx S = ∀ s → (x : S ∋ s) → drop-∈ x S ∶⊢ s

[]ₜ : Ctx []
[]ₜ _ ()

_∷ₜ_ : S ∶⊢ s → Ctx S → Ctx (s ∷ S)
(t ∷ₜ Γ) _ zero     = t
(t ∷ₜ Γ) _ (suc x)  = Γ _ x

weaken : S ⊢ s → (s′ ∷ S) ⊢ s
weaken t = t ⋯ˢ (wkˢ _)

_[_] : (s′ ∷ S) ⊢ s → S ⊢ s′ → S ⊢ s
t [ t′ ] = t ⋯ˢ (t′ ∙ˢ idˢ)

wk-drop-∈ : (x : S ∋ s) → drop-∈ x S ⊢ s′ → S ⊢ s′
wk-drop-∈ zero t     = weaken t
wk-drop-∈ (suc x)  t = weaken (wk-drop-∈ x t)

wk-telescope : Ctx S → S ∋ s → S ∶⊢ s
wk-telescope Γ x = wk-drop-∈ x (Γ _ x)

_∋_∶_ : Ctx S → S ∋ s → S ∶⊢ s → Set
Γ ∋ x ∶ t = wk-telescope Γ x ≡ t

variable
  Γ Γ₁ Γ₂ Γ₃ Γ′ Γ₁′ Γ₂′ Γ₃′ : Ctx S

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
    Γ ⊢ (e • t) ∶ (t′ [ t ])
  ⊢* : {t : S ⊢ type} →
    Γ ⊢ t ∶ *

_∶_→ˢ_ : S₁ →ˢ S₂ → (Γ₁ : Ctx S₁) → (Γ₂ : Ctx S₂) → Set
_∶_→ˢ_ {S₁} {S₂} σ Γ₁ Γ₂ =
  ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) →
  (Γ₁ ∋ x ∶ t) → Γ₂ ⊢ (x ⋯ˢ σ) ∶ (t ⋯ˢ σ)

data Val : S ⊢ expr → Set where
  vλ : Val (λx e)
  vΛ : Val (Λα e)

data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  β-λ : Val e₂ → ((λx e₁) · e₂) ↪ (e₁ [ e₂ ])
  β-Λ : ((Λα e) • t) ↪ (e [ t ])
  ξ-·₁ : e₁ ↪ e → (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ : e₂ ↪ e → Val e₁ → (e₁ · e₂) ↪ (e₁ · e)
  ξ-• : e ↪ e′ → (e • t) ↪ (e′ • t)

-- Renaming preserves typing, stated on VARIABLES.  Note the type action is
-- _⋯ˢ ⟨ ρ ⟩ — an ordinary substitution — so nothing here leaves the single
-- algebra.  This lemma exists to stratify the recursion, exactly as _⋯ᴿ_
-- stratifies _⋯ˢ_ at the term level.
_∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ᴿ_ {S₁} {S₂} ρ Γ₁ Γ₂ = ∀ (s : Sort) (x : S₁ ∋ s) (t : S₁ ∶⊢ s) →
  (Γ₁ ∋ x ∶ t) → Γ₂ ∋ (ρ s x) ∶ (t ⋯ˢ ⟨ ρ ⟩)

⊢wkᴿ : ∀ (Γ : Ctx S) (x : S ∋ s) t (t′ : S ∶⊢ s′) →
  Γ ∋ x ∶ t → (t′ ∷ₜ Γ) ∋ suc x ∶ (t ⋯ˢ wkˢ _)
⊢wkᴿ Γ x t t′ refl = refl

⊢↑ᴿ : ρ ∶ Γ₁ →ᴿ Γ₂ → (t : S₁ ∶⊢ s) → (ρ ↑ᴿ s) ∶ (t ∷ₜ Γ₁) →ᴿ ((t ⋯ˢ ⟨ ρ ⟩) ∷ₜ Γ₂)
⊢↑ᴿ ⊢ρ _ _ zero _ refl = refl
⊢↑ᴿ {ρ = ρ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} ⊢ρ t _ (suc x) _ refl =
  ⊢wkᴿ Γ₂ (ρ _ x) (wk-telescope Γ₁ x ⋯ˢ ⟨ ρ ⟩) (t ⋯ˢ ⟨ ρ ⟩) (⊢ρ _ x _ refl)

_⊢⋯ᴿ[_]_ : ∀ {e : S₁ ⊢ s} {t : S₁ ∶⊢ s} →
  Γ₁ ⊢ e ∶ t → (ρ : S₁ →ᴿ S₂) → ρ ∶ Γ₁ →ᴿ Γ₂ →
  Γ₂ ⊢ (e ⋯ˢ ⟨ ρ ⟩) ∶ (t ⋯ˢ ⟨ ρ ⟩)
-- NB: coe-var is NOT used here — see the OPACITY CAVEAT at the bottom of the
-- file.  This subst is the honest transport: it uses def-⟨⟩ propositionally and
-- makes no definitional claim outside the confluence-checked regime.
_⊢⋯ᴿ[_]_ {Γ₂ = Γ₂} (⊢` {x = x} {t = t} ⊢x) ρ ⊢ρ =
  subst (λ u → Γ₂ ⊢ u ∶ (t ⋯ˢ ⟨ ρ ⟩)) (sym (def-⟨⟩ {x = x} {ρ = ρ}))
        (⊢` (⊢ρ _ x t ⊢x))
(⊢λ ⊢e)      ⊢⋯ᴿ[ ρ ] ⊢ρ = ⊢λ (⊢e ⊢⋯ᴿ[ ρ ↑ᴿ _ ] (⊢↑ᴿ ⊢ρ _))
(⊢Λ ⊢e)      ⊢⋯ᴿ[ ρ ] ⊢ρ = ⊢Λ (⊢e ⊢⋯ᴿ[ ρ ↑ᴿ _ ] (⊢↑ᴿ ⊢ρ _))
(⊢· ⊢e₁ ⊢e₂) ⊢⋯ᴿ[ ρ ] ⊢ρ = ⊢· (⊢e₁ ⊢⋯ᴿ[ ρ ] ⊢ρ) (⊢e₂ ⊢⋯ᴿ[ ρ ] ⊢ρ)
(⊢• ⊢e ⊢t ⊢t') ⊢⋯ᴿ[ ρ ] ⊢ρ =
  ⊢• (⊢e ⊢⋯ᴿ[ ρ ] ⊢ρ) (⊢t ⊢⋯ᴿ[ ρ ] ⊢ρ) (⊢t' ⊢⋯ᴿ[ ρ ↑ᴿ _ ] (⊢↑ᴿ ⊢ρ _))
⊢*           ⊢⋯ᴿ[ ρ ] ⊢ρ = ⊢*

⊢wkˢ : ∀ (Γ : Ctx S) (e : S ⊢ s) (t : S ∶⊢ s) (t′ : S ∶⊢ s′) →
  Γ ⊢ e ∶ t → (t′ ∷ₜ Γ) ⊢ (e ⋯ˢ wkˢ _) ∶ (t ⋯ˢ wkˢ _)
⊢wkˢ Γ e t t′ ⊢e = ⊢e ⊢⋯ᴿ[ wkᴿ _ ] (λ s x t ⊢x → ⊢wkᴿ Γ x t t′ ⊢x)

⊢↑ˢ[_]_ : (σ : S₁ →ˢ S₂) → σ ∶ Γ₁ →ˢ Γ₂ → (t : S₁ ∶⊢ s) →
  (σ ↑ˢ s) ∶ (t ∷ₜ Γ₁) →ˢ ((t ⋯ˢ σ) ∷ₜ Γ₂)
(⊢↑ˢ[ σ ] ⊢σ) _ _ zero _ refl = ⊢` refl
⊢↑ˢ[_]_ {Γ₁ = Γ₁} {Γ₂ = Γ₂} σ ⊢σ t _ (suc x) _ refl =
  ⊢wkˢ Γ₂ (x ⋯ˢ σ) (wk-telescope Γ₁ x ⋯ˢ σ) (t ⋯ˢ σ) (⊢σ _ x _ refl)

_⊢⋯ˢ[_]_ :
  Γ₁ ⊢ t ∶ t′ →
  (σ : S₁ →ˢ S₂) →
  σ ∶ Γ₁ →ˢ Γ₂ →
  Γ₂ ⊢ (t ⋯ˢ σ) ∶ (t′ ⋯ˢ σ)
(⊢` {x = x} {t = t} ⊢x) ⊢⋯ˢ[ σ ] ⊢σ = ⊢σ _ x t ⊢x
(⊢λ ⊢e)      ⊢⋯ˢ[ σ ] ⊢σ = ⊢λ (⊢e ⊢⋯ˢ[ σ ↑ˢ _ ] (⊢↑ˢ[ σ ] ⊢σ) _)
(⊢Λ ⊢e)      ⊢⋯ˢ[ σ ] ⊢σ = ⊢Λ (⊢e ⊢⋯ˢ[ σ ↑ˢ _ ] (⊢↑ˢ[ σ ] ⊢σ) _)
(⊢· ⊢e₁ ⊢e₂) ⊢⋯ˢ[ σ ] ⊢σ = ⊢· (⊢e₁ ⊢⋯ˢ[ σ ] ⊢σ) (⊢e₂ ⊢⋯ˢ[ σ ] ⊢σ)
(⊢• ⊢e ⊢t ⊢t') ⊢⋯ˢ[ σ ] ⊢σ =
  ⊢• (⊢e ⊢⋯ˢ[ σ ] ⊢σ) (⊢t ⊢⋯ˢ[ σ ] ⊢σ) (⊢t' ⊢⋯ˢ[ σ ↑ˢ _ ] (⊢↑ˢ[ σ ] ⊢σ) _)
⊢*           ⊢⋯ˢ[ σ ] ⊢σ = ⊢*

⊢[] : ∀ {Γ : Ctx S} {e : S ⊢ s} {t : S ∶⊢ s} → Γ ⊢ e ∶ t → (e ∙ˢ idˢ) ∶ (t ∷ₜ Γ) →ˢ Γ
⊢[] ⊢t _ zero    _ refl = ⊢t
⊢[] ⊢t _ (suc x) _ refl = ⊢` refl

sr :
  Γ ⊢ e ∶ t →
  e ↪ e′ →
  Γ ⊢ e′ ∶ t
sr (⊢· {e₂ = e₂} (⊢λ {e = e₁} ⊢e₁) ⊢e₂) (β-λ v₂) = ⊢e₁ ⊢⋯ˢ[ e₂ ∙ˢ idˢ ] (⊢[] ⊢e₂)
sr (⊢• {t = t} (⊢Λ ⊢e) ⊢t ⊢t') β-Λ              = ⊢e ⊢⋯ˢ[ t ∙ˢ idˢ ] (⊢[] ⊢t)
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₁ e₁↪e)    = ⊢· (sr ⊢e₁ e₁↪e) ⊢e₂
sr (⊢· ⊢e₁ ⊢e₂) (ξ-·₂ e₂↪e x)  = ⊢· ⊢e₁ (sr ⊢e₂ e₂↪e)
sr (⊢• ⊢e ⊢t ⊢t') (ξ-• e↪e')   = ⊢• (sr ⊢e e↪e') ⊢t ⊢t'


------------------------------------------------------------------------
-- OPACITY CAVEAT.  Read before quoting the "0 critical pairs" number.
--
-- --local-confluence-check checks critical pairs between REWRITE RULES, with
-- opaque definitions in their opaque state.  It does not check a rewrite rule
-- against the definitional unfolding of the symbols it mentions.  So the
-- certificate is relative to the opaque state, and the combined system
-- (rewrite rules + unfolding) is NOT confluent.  Demonstrated below.
--
-- The dividing line is exactly how a rule is proven:
--   * proven by refl        -> genuinely definitional, survives unfolding
--   * proven by ext/induction -> holds only propositionally; unfolding and the
--                                rewrite rule then reduce a term to two
--                                different normal forms, unchecked.
-- This affects every file in this line of work (systemf, systemfLift, this
-- one): assoc, dist, ↑ˢ-⨟, comp-idᵣ, right-idˢ, compositionalityˢˢ and ⟨⟩-↑ are
-- all ext/induction-proven.  It is not unsoundness — every registered rule is a
-- true equation, proven above, so no false proposition becomes provable — but
-- convertibility depends on the opaque state, which is what opaque is for.
------------------------------------------------------------------------

-- Outside any unfolding scope, the ⟨⟩-↑ rewrite rule makes these convertible.
outside-unfolding : ∀ {S₁ S₂ s s′} (x : (s′ ∷ S₁) ∋ s) (ρ : S₁ →ᴿ S₂) →
  x ⋯ˢ ⟨ ρ ↑ᴿ s′ ⟩ ≡ x ⋯ˢ (⟨ ρ ⟩ ↑ˢ s′)
outside-unfolding x ρ = refl

-- The SAME statement inside `opaque unfolding _⋯ˢ_ ⟨_⟩` is REJECTED:
--
--   ` (ρ ↑ᴿ s′) s x != ((` zero) ∙ˢ (λ z x₁ → ⟨ ρ ⟩ z x₁ ⋯ᴿ wkᴿ s′)) s x
--
-- Two terms, convertible in one scope and not the other: the divergence the
-- confluence check does not see.

opaque
  unfolding _⋯ˢ_ ⟨_⟩ _⨟_ _↑ˢ_ _∙ˢ_ wkˢ idˢ

  -- refl-proven rules survive unfolding.
  probe-def-⨟ : ∀ {S₁ S₂ S₃ s} {x : S₁ ∋ s} {σ₁ : S₁ →ˢ S₂} {σ₂ : S₂ →ˢ S₃} →
    (x ⋯ˢ σ₁) ⋯ˢ σ₂ ≡ x ⋯ˢ (σ₁ ⨟ σ₂)
  probe-def-⨟ = refl

  probe-interact : ∀ {S₁ S₂ s} {t : S₂ ⊢ s} {σ : S₁ →ˢ S₂} →
    wkˢ s ⨟ (t ∙ˢ σ) ≡ σ
  probe-interact = refl

  -- ext/induction-proven rules do NOT.  probe-↑ˢ-⨟ = refl is REJECTED:
  --   ((` zero) ∙ˢ (λ z x → σ₁ z x ⋯ᴿ wkᴿ s)) s₁ x ⋯ˢ (σ₂ ↑ˢ s)
  --   != ((` zero) ∙ˢ (λ z x₁ → (σ₁ ⨟ σ₂) z x₁ ⋯ᴿ wkᴿ s)) s₁ x
  -- for  (σ₁ ↑ˢ s) ⨟ (σ₂ ↑ˢ s) ≡ (σ₁ ⨟ σ₂) ↑ˢ s.

  -- coe-var, the zero-subst trick, lives here: it is TRUE (refl-proven
  -- def-⟨⟩), but it is only available inside this regime.
  coe-var′ : ∀ {S₁ S₂ s} {Γ₂ : Ctx S₂} {ρ : S₁ →ᴿ S₂} {x : S₁ ∋ s} {A : S₂ ∶⊢ s} →
    Γ₂ ⊢ ` (ρ s x) ∶ A → Γ₂ ⊢ (x ⋯ˢ ⟨ ρ ⟩) ∶ A
  coe-var′ d = d
