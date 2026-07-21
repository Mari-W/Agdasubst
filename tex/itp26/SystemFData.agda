{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- System F, plain de Bruijn (matchable zero/suc), but with substitution as
-- FIRST-ORDER DATA (a cons-vector of terms) instead of a function ℕ→Tm.
--
-- This is the clean fix for `systemf.agda`'s wall: its σ was a FUNCTION, so
-- `var x ⋯ σ = σ x` was a stuck neutral on abstract x and `dist`/`def-⨟` could
-- not be joined as rewrites.  With data substitutions, `lookup x (σ ⨟ τ)`
-- computes structurally (both x and σ⨟τ are matchable), so the critical pair
-- joins by construction and the σ-laws register confluently.
--
-- Renaming is an OPE `_⊑_` (order-preserving embedding: os/o'), whose
-- composition is the confluent thinning composition — this supplies weakening
-- and lifting without a general (functional) renaming sort.
-- ════════════════════════════════════════════════════════════════════════════
module SystemFData where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans)
open import Agda.Builtin.Equality.Rewrite
open import Data.List using (List; []; _∷_)

-- ── sorts / scopes / intrinsically-scoped terms (as in systemf.agda) ──
data Sort : Set where expr type kind : Sort
variable s s′ : Sort
Scope = List Sort
variable S S₁ S₂ S₃ S₄ : Scope

data Mode : Set where V T : Mode
variable m : Mode

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
  x x′ : S ∋ s
  t t₁ t₂ t′ : S ⊢ s

-- ════ renaming = order-preserving embedding (thinning) ════
data _⊑_ : Scope → Scope → Set where
  oz : [] ⊑ []
  os : S₁ ⊑ S₂ → (s ∷ S₁) ⊑ (s ∷ S₂)
  o' : S₁ ⊑ S₂ → S₁ ⊑ (s ∷ S₂)
variable ρ ρ₁ ρ₂ ρ₃ : S₁ ⊑ S₂

oi : S ⊑ S
oi {[]}    = oz
oi {s ∷ S} = os oi

-- OPE composition (the 4 elimination clauses are the confluent rewrite set)
opaque
  _⨾_ : S₁ ⊑ S₂ → S₂ ⊑ S₃ → S₁ ⊑ S₃
  ρ    ⨾ o' φ = o' (ρ ⨾ φ)
  os ρ ⨾ os φ = os (ρ ⨾ φ)
  o' ρ ⨾ os φ = o' (ρ ⨾ φ)
  oz   ⨾ oz   = oz
infixr 7 _⨾_

opaque
  unfolding _⨾_
  ⨾-o'  : ∀ {s}(ρ : S₁ ⊑ S₂)(φ : S₂ ⊑ S₃) → ρ    ⨾ o' {s = s} φ ≡ o' (ρ ⨾ φ)
  ⨾-o'  ρ φ = refl
  ⨾-osos : ∀ {s}(ρ : S₁ ⊑ S₂)(φ : S₂ ⊑ S₃) → os {s = s} ρ ⨾ os φ ≡ os (ρ ⨾ φ)
  ⨾-osos ρ φ = refl
  ⨾-o'os : ∀ {s}(ρ : S₁ ⊑ S₂)(φ : S₂ ⊑ S₃) → o' ρ ⨾ os {s = s} φ ≡ o' (ρ ⨾ φ)
  ⨾-o'os ρ φ = refl
  ⨾-ozoz : oz ⨾ oz ≡ oz
  ⨾-ozoz = refl
{-# REWRITE ⨾-o' ⨾-osos ⨾-o'os ⨾-ozoz #-}

oi⨾ : (ρ : S₁ ⊑ S₂) → oi ⨾ ρ ≡ ρ
oi⨾ oz     = refl
oi⨾ (os ρ) = cong os (oi⨾ ρ)
oi⨾ (o' ρ) = cong o' (oi⨾ ρ)
⨾oi : (ρ : S₁ ⊑ S₂) → ρ ⨾ oi ≡ ρ
⨾oi oz     = refl
⨾oi (os ρ) = cong os (⨾oi ρ)
⨾oi (o' ρ) = cong o' (⨾oi ρ)
⨾⨾ : (a : S₁ ⊑ S₂)(b : S₂ ⊑ S₃)(c : S₃ ⊑ S₄) → (a ⨾ b) ⨾ c ≡ a ⨾ (b ⨾ c)
⨾⨾ a      b      (o' c) = cong o' (⨾⨾ a b c)
⨾⨾ a      (o' b) (os c) = cong o' (⨾⨾ a b c)
⨾⨾ (os a) (os b) (os c) = cong os (⨾⨾ a b c)
⨾⨾ (o' a) (os b) (os c) = cong o' (⨾⨾ a b c)
⨾⨾ oz     oz     oz     = refl

-- rename a variable / a term along an OPE
renVar : S₁ ∋ s → S₁ ⊑ S₂ → S₂ ∋ s
renVar x      (o' ρ) = suc (renVar x ρ)
renVar zero   (os ρ) = zero
renVar (suc x)(os ρ) = suc (renVar x ρ)

_⋯ᴿ_ : S₁ ⊢[ m ] s → S₁ ⊑ S₂ → S₂ ⊢[ m ] s
_⋯ᴿ_ {m = V} x ρ = renVar x ρ
(` x)        ⋯ᴿ ρ = ` renVar x ρ
(λx e)       ⋯ᴿ ρ = λx (e ⋯ᴿ os ρ)
(Λα e)       ⋯ᴿ ρ = Λα (e ⋯ᴿ os ρ)
(∀[α∶ k ] t) ⋯ᴿ ρ = ∀[α∶ k ⋯ᴿ ρ ] (t ⋯ᴿ os ρ)
(e₁ · e₂)    ⋯ᴿ ρ = (e₁ ⋯ᴿ ρ) · (e₂ ⋯ᴿ ρ)
(e • t)      ⋯ᴿ ρ = (e ⋯ᴿ ρ) • (t ⋯ᴿ ρ)
(t₁ ⇒ t₂)    ⋯ᴿ ρ = (t₁ ⋯ᴿ ρ) ⇒ (t₂ ⋯ᴿ ρ)
*            ⋯ᴿ ρ = *
infixl 8 _⋯ᴿ_

-- ════ substitution = FIRST-ORDER DATA (cons-vector of terms) ════
data Sub (S₂ : Scope) : Scope → Set where
  []  : Sub S₂ []
  _∙_ : S₂ ⊢ s → Sub S₂ S₁ → Sub S₂ (s ∷ S₁)
infixr 5 _∙_
variable σ σ₁ σ₂ σ₃ : Sub S₂ S₁

lookupˢ : S₁ ∋ s → Sub S₂ S₁ → S₂ ⊢ s
lookupˢ zero    (t ∙ σ) = t
lookupˢ (suc x) (t ∙ σ) = lookupˢ x σ

-- rename the TARGET of a substitution along an OPE (weakening carrier)
mapᴿ : Sub S₂ S₁ → S₂ ⊑ S₃ → Sub S₃ S₁
mapᴿ []      r = []
mapᴿ (t ∙ σ) r = (t ⋯ᴿ r) ∙ mapᴿ σ r
wkSub : Sub S₂ S₁ → Sub (s ∷ S₂) S₁
wkSub σ = mapᴿ σ (o' oi)
liftˢ : Sub S₂ S₁ → Sub (s ∷ S₂) (s ∷ S₁)
liftˢ σ = (` zero) ∙ wkSub σ

_⋯ˢ_ : S₁ ⊢[ m ] s → Sub S₂ S₁ → S₂ ⊢ s
_⋯ˢ_ {m = V} x σ = lookupˢ x σ
(` x)        ⋯ˢ σ = lookupˢ x σ
(λx e)       ⋯ˢ σ = λx (e ⋯ˢ liftˢ σ)
(Λα e)       ⋯ˢ σ = Λα (e ⋯ˢ liftˢ σ)
(∀[α∶ k ] t) ⋯ˢ σ = ∀[α∶ k ⋯ˢ σ ] (t ⋯ˢ liftˢ σ)
(e₁ · e₂)    ⋯ˢ σ = (e₁ ⋯ˢ σ) · (e₂ ⋯ˢ σ)
(e • t)      ⋯ˢ σ = (e ⋯ˢ σ) • (t ⋯ˢ σ)
(t₁ ⇒ t₂)    ⋯ˢ σ = (t₁ ⋯ˢ σ) ⇒ (t₂ ⋯ˢ σ)
*            ⋯ˢ σ = *
infixl 8 _⋯ˢ_

_⨟_ : Sub S₂ S₁ → Sub S₃ S₂ → Sub S₃ S₁
[]      ⨟ τ = []
(t ∙ σ) ⨟ τ = (t ⋯ˢ τ) ∙ (σ ⨟ τ)
infixl 6 _⨟_

idˢ : Sub S S
idˢ {[]}    = []
idˢ {s ∷ S} = (` zero) ∙ wkSub idˢ

-- ════ the σ-law tower (all PROVEN by structural induction) ════
-- renaming fusion
renVar-⨾ : (x : S₁ ∋ s)(ρ₁ : S₁ ⊑ S₂)(ρ₂ : S₂ ⊑ S₃) → renVar (renVar x ρ₁) ρ₂ ≡ renVar x (ρ₁ ⨾ ρ₂)
renVar-⨾ x       ρ₁     (o' ρ₂) = cong suc (renVar-⨾ x ρ₁ ρ₂)
renVar-⨾ x       (o' ρ₁)(os ρ₂) = cong suc (renVar-⨾ x ρ₁ ρ₂)
renVar-⨾ zero    (os ρ₁)(os ρ₂) = refl
renVar-⨾ (suc x) (os ρ₁)(os ρ₂) = cong suc (renVar-⨾ x ρ₁ ρ₂)
renVar-⨾ ()      oz     oz
⋯ᴿ-⨾ : (t : S₁ ⊢[ m ] s)(ρ₁ : S₁ ⊑ S₂)(ρ₂ : S₂ ⊑ S₃) → (t ⋯ᴿ ρ₁) ⋯ᴿ ρ₂ ≡ t ⋯ᴿ (ρ₁ ⨾ ρ₂)
⋯ᴿ-⨾ {m = V} x ρ₁ ρ₂ = renVar-⨾ x ρ₁ ρ₂
⋯ᴿ-⨾ (` x)        ρ₁ ρ₂ = cong `_ (renVar-⨾ x ρ₁ ρ₂)
⋯ᴿ-⨾ (λx e)       ρ₁ ρ₂ = cong λx_ (⋯ᴿ-⨾ e (os ρ₁)(os ρ₂))
⋯ᴿ-⨾ (Λα e)       ρ₁ ρ₂ = cong Λα_ (⋯ᴿ-⨾ e (os ρ₁)(os ρ₂))
⋯ᴿ-⨾ (∀[α∶ k ] t) ρ₁ ρ₂ = cong₂ ∀[α∶_]_ (⋯ᴿ-⨾ k ρ₁ ρ₂) (⋯ᴿ-⨾ t (os ρ₁)(os ρ₂))
⋯ᴿ-⨾ (e₁ · e₂)    ρ₁ ρ₂ = cong₂ _·_ (⋯ᴿ-⨾ e₁ ρ₁ ρ₂) (⋯ᴿ-⨾ e₂ ρ₁ ρ₂)
⋯ᴿ-⨾ (e • t)      ρ₁ ρ₂ = cong₂ _•_ (⋯ᴿ-⨾ e ρ₁ ρ₂) (⋯ᴿ-⨾ t ρ₁ ρ₂)
⋯ᴿ-⨾ (t₁ ⇒ t₂)    ρ₁ ρ₂ = cong₂ _⇒_ (⋯ᴿ-⨾ t₁ ρ₁ ρ₂) (⋯ᴿ-⨾ t₂ ρ₁ ρ₂)
⋯ᴿ-⨾ *            ρ₁ ρ₂ = refl

renVar-oi : (x : S ∋ s) → renVar x oi ≡ x
renVar-oi zero    = refl
renVar-oi (suc x) = cong suc (renVar-oi x)

-- restriction: precompose a substitution by an OPE on its source
_↾_ : Sub S₂ S₁ → S₃ ⊑ S₁ → Sub S₂ S₃
[]      ↾ oz   = []
(t ∙ σ) ↾ os r = t ∙ (σ ↾ r)
(t ∙ σ) ↾ o' r = σ ↾ r
infixl 8 _↾_

mapᴿ-↾ : (σ : Sub S₂ S₁)(r : S₂ ⊑ S₃)(w : S₄ ⊑ S₁) → mapᴿ (σ ↾ w) r ≡ mapᴿ σ r ↾ w
mapᴿ-↾ []      r oz     = refl
mapᴿ-↾ (t ∙ σ) r (os w) = cong (_ ∙_) (mapᴿ-↾ σ r w)
mapᴿ-↾ (t ∙ σ) r (o' w) = mapᴿ-↾ σ r w

lookup-↾ : (x : S₃ ∋ s)(r : S₃ ⊑ S₁)(σ : Sub S₂ S₁) → lookupˢ (renVar x r) σ ≡ lookupˢ x (σ ↾ r)
lookup-↾ x       (o' r)(t ∙ σ) = lookup-↾ x r σ
lookup-↾ zero    (os r)(t ∙ σ) = refl
lookup-↾ (suc x) (os r)(t ∙ σ) = lookup-↾ x r σ

-- renaming-then-substituting = substituting by the restricted substitution
⋯ᴿ-⋯ˢ : (t : S₁ ⊢[ m ] s)(r : S₁ ⊑ S₃)(σ : Sub S₂ S₃) → (t ⋯ᴿ r) ⋯ˢ σ ≡ t ⋯ˢ (σ ↾ r)
⋯ᴿ-⋯ˢ {m = V} x r σ = lookup-↾ x r σ
⋯ᴿ-⋯ˢ (` x)        r σ = lookup-↾ x r σ
⋯ᴿ-⋯ˢ (λx e)       r σ = cong λx_ (trans (⋯ᴿ-⋯ˢ e (os r) (liftˢ σ)) (cong (λ z → e ⋯ˢ ((` zero) ∙ z)) (sym (mapᴿ-↾ σ (o' oi) r))))
⋯ᴿ-⋯ˢ (Λα e)       r σ = cong Λα_ (trans (⋯ᴿ-⋯ˢ e (os r) (liftˢ σ)) (cong (λ z → e ⋯ˢ ((` zero) ∙ z)) (sym (mapᴿ-↾ σ (o' oi) r))))
⋯ᴿ-⋯ˢ (∀[α∶ k ] t) r σ = cong₂ ∀[α∶_]_ (⋯ᴿ-⋯ˢ k r σ) (trans (⋯ᴿ-⋯ˢ t (os r) (liftˢ σ)) (cong (λ z → t ⋯ˢ ((` zero) ∙ z)) (sym (mapᴿ-↾ σ (o' oi) r))))
⋯ᴿ-⋯ˢ (e₁ · e₂)    r σ = cong₂ _·_ (⋯ᴿ-⋯ˢ e₁ r σ) (⋯ᴿ-⋯ˢ e₂ r σ)
⋯ᴿ-⋯ˢ (e • t)      r σ = cong₂ _•_ (⋯ᴿ-⋯ˢ e r σ) (⋯ᴿ-⋯ˢ t r σ)
⋯ᴿ-⋯ˢ (t₁ ⇒ t₂)    r σ = cong₂ _⇒_ (⋯ᴿ-⋯ˢ t₁ r σ) (⋯ᴿ-⋯ˢ t₂ r σ)
⋯ᴿ-⋯ˢ *            r σ = refl

-- weakening a cons drops the head under substitution:  (t ⋯ᴿ o' oi) ⋯ˢ (u ∙ σ) = t ⋯ˢ σ
wk-cancel : (t : S₁ ⊢ s)(u : S₂ ⊢ s′)(σ : Sub S₂ S₁) → (t ⋯ᴿ (o' oi)) ⋯ˢ (u ∙ σ) ≡ t ⋯ˢ σ
wk-cancel t u σ = trans (⋯ᴿ-⋯ˢ t (o' oi) (u ∙ σ)) (cong (t ⋯ˢ_) (idSub-↾ σ))
  where idSub-↾ : (σ : Sub S₂ S₁) → σ ↾ oi ≡ σ
        idSub-↾ []      = refl
        idSub-↾ (t ∙ σ) = cong (t ∙_) (idSub-↾ σ)

-- sub commutes with target-renaming
lookup-mapᴿ : (x : S₁ ∋ s)(τ : Sub S₂ S₁)(r : S₂ ⊑ S₃) → lookupˢ x (mapᴿ τ r) ≡ (lookupˢ x τ) ⋯ᴿ r
lookup-mapᴿ zero    (t ∙ τ) r = refl
lookup-mapᴿ (suc x) (t ∙ τ) r = lookup-mapᴿ x τ r
mapᴿ-fusion : (σ : Sub S₂ S₁)(r₁ : S₂ ⊑ S₃)(r₂ : S₃ ⊑ S₄) → mapᴿ (mapᴿ σ r₁) r₂ ≡ mapᴿ σ (r₁ ⨾ r₂)
mapᴿ-fusion []      r₁ r₂ = refl
mapᴿ-fusion (t ∙ σ) r₁ r₂ = cong₂ _∙_ (⋯ᴿ-⨾ t r₁ r₂) (mapᴿ-fusion σ r₁ r₂)
mapᴿ-lift : (σ : Sub S₂ S₁)(r : S₂ ⊑ S₃) → liftˢ {s = s} (mapᴿ σ r) ≡ mapᴿ (liftˢ σ) (os r)
mapᴿ-lift σ r = cong ((` zero) ∙_)
  (trans (mapᴿ-fusion σ r (o' oi))
    (trans (cong (λ z → mapᴿ σ (o' z)) (trans (⨾oi r) (sym (oi⨾ r))))
           (sym (mapᴿ-fusion σ (o' oi) (os r)))))
⋯ˢ-mapᴿ : (t : S₁ ⊢[ m ] s)(τ : Sub S₂ S₁)(r : S₂ ⊑ S₃) → t ⋯ˢ (mapᴿ τ r) ≡ (t ⋯ˢ τ) ⋯ᴿ r
⋯ˢ-mapᴿ {m = V} x τ r = lookup-mapᴿ x τ r
⋯ˢ-mapᴿ (` x)        τ r = lookup-mapᴿ x τ r
⋯ˢ-mapᴿ (λx e)       τ r = cong λx_ (trans (cong (e ⋯ˢ_) (mapᴿ-lift τ r)) (⋯ˢ-mapᴿ e (liftˢ τ) (os r)))
⋯ˢ-mapᴿ (Λα e)       τ r = cong Λα_ (trans (cong (e ⋯ˢ_) (mapᴿ-lift τ r)) (⋯ˢ-mapᴿ e (liftˢ τ) (os r)))
⋯ˢ-mapᴿ (∀[α∶ k ] t) τ r = cong₂ ∀[α∶_]_ (⋯ˢ-mapᴿ k τ r) (trans (cong (t ⋯ˢ_) (mapᴿ-lift τ r)) (⋯ˢ-mapᴿ t (liftˢ τ) (os r)))
⋯ˢ-mapᴿ (e₁ · e₂)    τ r = cong₂ _·_ (⋯ˢ-mapᴿ e₁ τ r) (⋯ˢ-mapᴿ e₂ τ r)
⋯ˢ-mapᴿ (e • t)      τ r = cong₂ _•_ (⋯ˢ-mapᴿ e τ r) (⋯ˢ-mapᴿ t τ r)
⋯ˢ-mapᴿ (t₁ ⇒ t₂)    τ r = cong₂ _⇒_ (⋯ˢ-mapᴿ t₁ τ r) (⋯ˢ-mapᴿ t₂ τ r)
⋯ˢ-mapᴿ *            τ r = refl

-- ShiftCons / interact, and lift/composition
wkSub-⨟ : (σ : Sub S₂ S₁)(u : S₃ ⊢ s)(τ : Sub S₃ S₂) → wkSub σ ⨟ (u ∙ τ) ≡ σ ⨟ τ
wkSub-⨟ []      u τ = refl
wkSub-⨟ (t ∙ σ) u τ = cong₂ _∙_ (wk-cancel t u τ) (wkSub-⨟ σ u τ)
⨟-wkSub : (σ : Sub S₂ S₁)(τ : Sub S₃ S₂) → σ ⨟ wkSub {s = s} τ ≡ wkSub (σ ⨟ τ)
⨟-wkSub []      τ = refl
⨟-wkSub (t ∙ σ) τ = cong₂ _∙_ (⋯ˢ-mapᴿ t τ (o' oi)) (⨟-wkSub σ τ)
lift-⨟ : (σ : Sub S₂ S₁)(τ : Sub S₃ S₂) → liftˢ {s = s} σ ⨟ liftˢ τ ≡ liftˢ (σ ⨟ τ)
lift-⨟ σ τ = cong ((` zero) ∙_) (trans (wkSub-⨟ σ (` zero) (wkSub τ)) (⨟-wkSub σ τ))
lookup-⨟ : (x : S₁ ∋ s)(σ : Sub S₂ S₁)(τ : Sub S₃ S₂) → lookupˢ x (σ ⨟ τ) ≡ (lookupˢ x σ) ⋯ˢ τ
lookup-⨟ zero    (t ∙ σ) τ = refl
lookup-⨟ (suc x) (t ∙ σ) τ = lookup-⨟ x σ τ

-- ★ Clos (compositionality) and assoc
Clos : (t : S₁ ⊢[ m ] s)(σ : Sub S₂ S₁)(τ : Sub S₃ S₂) → (t ⋯ˢ σ) ⋯ˢ τ ≡ t ⋯ˢ (σ ⨟ τ)
Clos {m = V} x σ τ = sym (lookup-⨟ x σ τ)
Clos (` x)        σ τ = sym (lookup-⨟ x σ τ)
Clos (λx e)       σ τ = cong λx_ (trans (Clos e (liftˢ σ) (liftˢ τ)) (cong (e ⋯ˢ_) (lift-⨟ σ τ)))
Clos (Λα e)       σ τ = cong Λα_ (trans (Clos e (liftˢ σ) (liftˢ τ)) (cong (e ⋯ˢ_) (lift-⨟ σ τ)))
Clos (∀[α∶ k ] t) σ τ = cong₂ ∀[α∶_]_ (Clos k σ τ) (trans (Clos t (liftˢ σ) (liftˢ τ)) (cong (t ⋯ˢ_) (lift-⨟ σ τ)))
Clos (e₁ · e₂)    σ τ = cong₂ _·_ (Clos e₁ σ τ) (Clos e₂ σ τ)
Clos (e • t)      σ τ = cong₂ _•_ (Clos e σ τ) (Clos t σ τ)
Clos (t₁ ⇒ t₂)    σ τ = cong₂ _⇒_ (Clos t₁ σ τ) (Clos t₂ σ τ)
Clos *            σ τ = refl
assoc : (σ₁ : Sub S₂ S₁)(σ₂ : Sub S₃ S₂)(σ₃ : Sub S₄ S₃) → (σ₁ ⨟ σ₂) ⨟ σ₃ ≡ σ₁ ⨟ (σ₂ ⨟ σ₃)
assoc []       σ₂ σ₃ = refl
assoc (t ∙ σ₁) σ₂ σ₃ = cong₂ _∙_ (Clos t σ₂ σ₃) (assoc σ₁ σ₂ σ₃)

-- ════════════════════════════════════════════════════════════════════════════
-- FINDING (verified): the σ-laws above are ALL PROVEN with NO funext / NO
-- postulates (systemf.agda needs `postulate fun-ext` for the functional σ).
-- BUT they still cannot be REGISTERED as confluent rewrites: registering
-- `lookup-⨟` (= def-⨟) races the `dist` clause of `_⨟_` on an ABSTRACT variable:
--
--   lookupˢ x ((t ∙ σ) ⨟ τ)  ──dist──►      lookupˢ x ((t ⋯ˢ τ) ∙ (σ ⨟ τ))
--                            ──lookup-⨟──►  (lookupˢ x (t ∙ σ)) ⋯ˢ τ
--
-- both stuck for abstract x — the SAME {def-⨟, dist} core as systemf.agda.
-- Data substitution removed the FUNCTIONAL stuckness (`σ x`), but plain
-- `zero`/`suc` keeps an ABSTRACT VARIABLE INDEX, and the composition law
-- quantifies over it.  Escaping THAT needs the variable index gone too:
-- co-de-Bruijn thinnings (FOp) or σ_SP explicit shifts.  See the git-tracked
-- confluence analysis.  So this file is the clean *propositional* σ-calculus
-- (no funext), not a confluent-definitional one.
-- ════════════════════════════════════════════════════════════════════════════
