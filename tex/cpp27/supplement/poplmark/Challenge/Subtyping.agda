{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLmark Challenge, parts 1A and 2A ════════════════════════════
--
--   1A  transitivity and narrowing of algorithmic F<: subtyping
--   2A  preservation and progress for F<:
--
-- built on the σ-calculus rewrite system of Languages/Fsub.agda.
--
-- THE MODE-MERGED, MULTI-SORTED DESIGN, PUSHED ONE STEP FURTHER.
-- F<: has two judgments -- subtyping between types and typing of terms.
-- Here they are ONE inductive family
--
--     _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set
--
-- indexed by the sort s of the subject.  At s = type it is
-- `Γ ⊢ A <: B`; at s = expr it is `Γ ⊢ e ∶ A`.  The payoff is that the
-- typed-map
-- machinery is written ONCE and simultaneously delivers
--
--   * weakening of subtyping AND of typing              (_⊢⋯ᴿ_)
--   * type substitution in subtyping AND in typing,
--     and term substitution in typing                   (_⊢⋯ˢ_)
--   * narrowing of subtyping AND of typing              (narrow)
--
-- and that a "typed substitution" σ ∶ Γ₁ →ˢ Γ₂ automatically means
-- "subtyping-respecting at type variables, typing-respecting at term
-- variables" -- the single condition F<: substitution lemmas need.

module Challenge.Subtyping where

open import Languages.Fsub
open import Data.Nat using (ℕ; zero; suc)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst) renaming (trans to ≡-trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; drop)

-- ─── the language-specific layer this metatheory sits on ────────────
-- Moved out of Languages.Fsub: none of it is σ-calculus.  It is contexts,
-- generalizable variables and congruences for THIS language, so it
-- belongs with the proofs and not in generated output.

-- ─── the generalizable variables the metatheory expects ─────────────

variable
  e e₁ e₂ e′              : S ⊢ expr
  A A₁ A₂ B B₁ B₂ C P Q U : S ⊢ type
  α                       : S ∋ s

-- ─── contexts ───────────────────────────────────────────────────────
-- The declaration of a variable of EITHER sort is a type: for a term
-- variable it is its type, for a type variable it is its upper bound.
-- CONSTANT, unlike System F's, so `S ∶⊢ s` reduces to `S ⊢ type` even
-- for an abstract sort `s` -- that is what makes the sort-generic
-- statements of Challenge/Subtyping.agda typecheck without a sort split.

↑ˢᵗ_ : Sort → Sort
↑ˢᵗ _ = type

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


-- ─── the one judgment ───────────────────────────────────────────────

infix 3 _⊢_∶_

data _⊢_∶_ : Ctx S → S ⊢ s → S ∶⊢ s → Set where
  -- ── algorithmic subtyping, i.e. the s = type fragment ──
  <:-top  : Γ ⊢ A ∶ Top
  <:-refl : ∀ {α : S ∋ type} {Γ : Ctx S} → Γ ⊢ (` α) ∶ (` α)
  <:-var  : ∀ {α : S ∋ type} {Γ : Ctx S} {U B} →
    Γ ∋ α ∶ U → Γ ⊢ U ∶ B → Γ ⊢ (` α) ∶ B
  <:-⇒    : Γ ⊢ B₁ ∶ A₁ → Γ ⊢ A₂ ∶ B₂ → Γ ⊢ (A₁ ⇒ A₂) ∶ (B₁ ⇒ B₂)
  <:-∀    : Γ ⊢ B₁ ∶ A₁ → (B₁ ∷ₜ Γ) ⊢ A₂ ∶ B₂ →
            Γ ⊢ (∀[<: A₁ ] A₂) ∶ (∀[<: B₁ ] B₂)
  -- ── typing, i.e. the s = expr fragment ──
  ⊢`      : ∀ {x : S ∋ expr} {Γ : Ctx S} {A} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢λ      : (A ∷ₜ Γ) ⊢ e ∶ weaken B → Γ ⊢ (λx[ A ] e) ∶ (A ⇒ B)
  ⊢Λ      : (A ∷ₜ Γ) ⊢ e ∶ B → Γ ⊢ (Λα[<: A ] e) ∶ (∀[<: A ] B)
  ⊢·      : Γ ⊢ e₁ ∶ (A ⇒ B) → Γ ⊢ e₂ ∶ A → Γ ⊢ (e₁ · e₂) ∶ B
  ⊢•      : Γ ⊢ e ∶ (∀[<: A ] B) → Γ ⊢ C ∶ A → Γ ⊢ (e • C) ∶ (B [ C ]₀)
  ⊢<:     : Γ ⊢ e ∶ A → Γ ⊢ A ∶ B → Γ ⊢ e ∶ B

-- the subtyping spelling of the same thing
infix 3 _⊢_<:_
_⊢_<:_ : Ctx S → S ⊢ type → S ⊢ type → Set
Γ ⊢ A <: B = Γ ⊢ A ∶ B

-- ─── reflexivity, and the sort-generic variable rule ────────────────

<:-reflexive : ∀ (A : S ⊢ type) {Γ : Ctx S} → Γ ⊢ A <: A
<:-reflexive Top          = <:-top
<:-reflexive (` α)        = <:-refl
<:-reflexive (A ⇒ B)      = <:-⇒ (<:-reflexive A) (<:-reflexive B)
<:-reflexive (∀[<: A ] B) = <:-∀ (<:-reflexive A) (<:-reflexive B)

-- ⊢` at both sorts: at s = expr it IS ⊢`, at s = type it is the
-- reflexive instance of <:-var
⊢var : ∀ {Γ : Ctx S} {x : S ∋ s} {A : S ∶⊢ s} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
⊢var {s = expr} eq = ⊢` eq
⊢var {s = type} eq = <:-var eq (<:-reflexive _)

-- ─── typed renamings: weakening for BOTH judgments at once ──────────

_∶_→ᴿ_ : S₁ →ᴿ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ᴿ_ {S₁} ξ Γ₁ Γ₂ = ∀ s (x : S₁ ∋ s) (A : S₁ ∶⊢ s) →
  Γ₁ ∋ x ∶ A → Γ₂ ∋ (x [ ξ ]ᴿ) ∶ (A [ ξ ]ᴿ)

⊢wkᴿ : (A : S ∶⊢ s′) → wkᴿ s′ ∶ Γ →ᴿ (A ∷ₜ Γ)
⊢wkᴿ A _ x _ refl = refl

⊢↑ᴿ : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} → ξ ∶ Γ₁ →ᴿ Γ₂ →
  (A : S₁ ∶⊢ s) → (ξ ↑ᴿ s) ∶ (A ∷ₜ Γ₁) →ᴿ ((A [ ξ ]ᴿ) ∷ₜ Γ₂)
⊢↑ᴿ ⊢ξ A _ zero    _ refl = refl
⊢↑ᴿ ⊢ξ A _ (suc x) _ refl = cong weaken (⊢ξ _ x _ refl)

infixl 5 _⊢⋯ᴿ_
_⊢⋯ᴿ_ : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {t : S₁ ⊢ s} {A : S₁ ∶⊢ s} →
  Γ₁ ⊢ t ∶ A → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (t [ ξ ]ᴿ) ∶ (A [ ξ ]ᴿ)
<:-top          ⊢⋯ᴿ ⊢ξ = <:-top
<:-refl         ⊢⋯ᴿ ⊢ξ = <:-refl
(<:-var ⊢α ⊢U)  ⊢⋯ᴿ ⊢ξ = <:-var (⊢ξ _ _ _ ⊢α) (⊢U ⊢⋯ᴿ ⊢ξ)
(<:-⇒ d₁ d₂)    ⊢⋯ᴿ ⊢ξ = <:-⇒ (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)
(<:-∀ d₁ d₂)    ⊢⋯ᴿ ⊢ξ = <:-∀ (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢↑ᴿ ⊢ξ _)
(⊢` ⊢x)         ⊢⋯ᴿ ⊢ξ = ⊢` (⊢ξ _ _ _ ⊢x)
(⊢λ d)          ⊢⋯ᴿ ⊢ξ = ⊢λ (d ⊢⋯ᴿ ⊢↑ᴿ ⊢ξ _)
(⊢Λ d)          ⊢⋯ᴿ ⊢ξ = ⊢Λ (d ⊢⋯ᴿ ⊢↑ᴿ ⊢ξ _)
(⊢· d₁ d₂)      ⊢⋯ᴿ ⊢ξ = ⊢· (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)
(⊢• d₁ d₂)      ⊢⋯ᴿ ⊢ξ = ⊢• (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)
(⊢<: d₁ d₂)     ⊢⋯ᴿ ⊢ξ = ⊢<: (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)

⊢weaken : ∀ {S s s′} {Γ : Ctx S} {t : S ⊢ s} {A : S ∶⊢ s} (P : S ∶⊢ s′) →
  Γ ⊢ t ∶ A → (_∷ₜ_ {s = s′} P Γ) ⊢ weaken t ∶ weaken A
⊢weaken P d = d ⊢⋯ᴿ ⊢wkᴿ P

-- ═══ PART 1A: transitivity and narrowing ════════════════════════════
--
-- Narrowing replaces ONE context entry by a subtype of it.  As a
-- relation between two contexts over the same scope:

Narrowing : ∀ {S} → Ctx S → S ⊢ type → Ctx S → Set
Narrowing {S} Γ₂ Q Γ₁ = ∀ s (x : S ∋ s) →
    (wk-telescope Γ₂ x ≡ wk-telescope Γ₁ x)
  ⊎ (wk-telescope Γ₁ x ≡ Q  ×  Γ₂ ⊢ wk-telescope Γ₂ x <: Q)

-- the narrowing at the top of the context, and its propagation under a
-- binder.  Both need only weakening, not transitivity.
-- NOTE the explicit sort annotations: since `S ∶⊢ s` is constantly
-- `S ⊢ type`, a context entry no longer determines the sort it was
-- pushed at, so `_∷ₜ_`'s index has to be pinned by hand.
narrow-here : ∀ {S} {Γ : Ctx S} {P Q : S ⊢ type} →
  Γ ⊢ P <: Q → Narrowing {type ∷ S} (P ∷ₜ Γ) (weaken Q) (Q ∷ₜ Γ)
narrow-here d _ zero    = inj₂ (refl , ⊢weaken _ d)
narrow-here d _ (suc y) = inj₁ refl

narrow-ext : ∀ {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} → Narrowing Γ₂ Q Γ₁ →
  ∀ s (P : S ∶⊢ s) → Narrowing {s ∷ S} (P ∷ₜ Γ₂) (weaken Q) (P ∷ₜ Γ₁)
narrow-ext nr s P _ zero = inj₁ refl
narrow-ext nr s P _ (suc y) with nr _ y
... | inj₁ eq        = inj₁ (cong weaken eq)
... | inj₂ (eq , d)  = inj₂ (cong weaken eq , ⊢weaken P d)

-- ─── the induction measure: the SHAPE of the cut type ───────────────
-- Transitivity is an induction on the cut type Q, narrowing an
-- induction on the derivation with transitivity at Q available.  Under
-- a binder Q gets WEAKENED, so plain structural induction on Q is out;
-- what is invariant is its shape.

data Shape : Set where
  ⊤ˢ   : Shape
  varˢ : Shape
  _⇒ˢ_ : Shape → Shape → Shape
  ∀ˢ   : Shape → Shape → Shape

shape : S ⊢ type → Shape
shape Top          = ⊤ˢ
shape (` α)        = varˢ
shape (A ⇒ B)      = shape A ⇒ˢ shape B
shape (∀[<: A ] B) = ∀ˢ (shape A) (shape B)

-- The one substitution fact in this file that the rewrite system does
-- NOT give for free: `shape` recurses on a type, and `A [ ξ ]ᴿ` with A
-- abstract is neutral, so this needs its own induction.
shape-ren : ∀ (A : S₁ ⊢ type) (ξ : S₁ →ᴿ S₂) → shape (A [ ξ ]ᴿ) ≡ shape A
shape-ren Top ξ          = refl
shape-ren (` α) ξ        = refl
shape-ren (A ⇒ B) ξ      = cong₂ _⇒ˢ_ (shape-ren A ξ) (shape-ren B ξ)
shape-ren (∀[<: A ] B) ξ = cong₂ ∀ˢ (shape-ren A ξ) (shape-ren B (ξ ↑ᴿ type))

⇒ˢ-injₗ : ∀ {a b c d} → (a ⇒ˢ b) ≡ (c ⇒ˢ d) → a ≡ c
⇒ˢ-injₗ refl = refl
⇒ˢ-injᵣ : ∀ {a b c d} → (a ⇒ˢ b) ≡ (c ⇒ˢ d) → b ≡ d
⇒ˢ-injᵣ refl = refl
∀ˢ-injₗ : ∀ {a b c d} → ∀ˢ a b ≡ ∀ˢ c d → a ≡ c
∀ˢ-injₗ refl = refl
∀ˢ-injᵣ : ∀ {a b c d} → ∀ˢ a b ≡ ∀ˢ c d → b ≡ d
∀ˢ-injᵣ refl = refl

-- The mutual pair.  Both recurse structurally on the SHAPE argument;
-- the cut type Q itself stays a variable, so the derivations can be
-- matched freely (matching a derivation refines Q).  NOTE: an earlier
-- version indexed the recursion by `Q [ ξ ]ᴿ` instead, to make the
-- induction structural in Q.  That version typechecks in the ordinary
-- sense but is REJECTED by --local-confluence-check: pattern matching
-- on Q puts `(∀[<: A ] B) [ ξ ]ᴿ` into the clause's left-hand side, which
-- overlaps instᴿ-∀ unjoinably.  Living under a rewrite system therefore
-- constrains what may be matched, not just what may be proved.

<:-trans : ∀ (sh : Shape) {S} {Γ : Ctx S} {A Q B : S ⊢ type} →
  shape Q ≡ sh → Γ ⊢ A <: Q → Γ ⊢ Q <: B → Γ ⊢ A <: B

narrow : ∀ (sh : Shape) {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type}
  {t : S ⊢ s} {A : S ∶⊢ s} →
  shape Q ≡ sh → Narrowing Γ₂ Q Γ₁ → Γ₁ ⊢ t ∶ A → Γ₂ ⊢ t ∶ A

<:-trans sh eq d₁            <:-top = <:-top
<:-trans sh eq <:-refl       d₂     = d₂
<:-trans sh eq (<:-var e u)  d₂     = <:-var e (<:-trans sh eq u d₂)
<:-trans (sh₁ ⇒ˢ sh₂) eq (<:-⇒ a₁ a₂) (<:-⇒ b₁ b₂) =
  <:-⇒ (<:-trans sh₁ (⇒ˢ-injₗ eq) b₁ a₁) (<:-trans sh₂ (⇒ˢ-injᵣ eq) a₂ b₂)
<:-trans (∀ˢ sh₁ sh₂) eq (<:-∀ a₁ a₂) (<:-∀ b₁ b₂) =
  <:-∀ (<:-trans sh₁ (∀ˢ-injₗ eq) b₁ a₁)
       (<:-trans sh₂ (∀ˢ-injᵣ eq)
         (narrow sh₁ (≡-trans (shape-ren _ _) (∀ˢ-injₗ eq))
                 (narrow-here b₁) a₂)
         b₂)
<:-trans ⊤ˢ       () (<:-⇒ _ _) (<:-⇒ _ _)
<:-trans varˢ     () (<:-⇒ _ _) (<:-⇒ _ _)
<:-trans (∀ˢ _ _) () (<:-⇒ _ _) (<:-⇒ _ _)
<:-trans ⊤ˢ       () (<:-∀ _ _) (<:-∀ _ _)
<:-trans varˢ     () (<:-∀ _ _) (<:-∀ _ _)
<:-trans (_ ⇒ˢ _) () (<:-∀ _ _) (<:-∀ _ _)

narrow sh eq nr <:-top  = <:-top
narrow sh eq nr <:-refl = <:-refl
narrow sh eq nr (<:-var {α = α} e u) with nr _ α
... | inj₁ eq₂       = <:-var (≡-trans eq₂ e) (narrow sh eq nr u)
... | inj₂ (eqQ , d) = <:-var refl
      (<:-trans sh eq d
        (subst (λ z → _ ⊢ z ∶ _) (≡-trans (sym e) eqQ) (narrow sh eq nr u)))
narrow sh eq nr (<:-⇒ d₁ d₂) = <:-⇒ (narrow sh eq nr d₁) (narrow sh eq nr d₂)
narrow sh eq nr (<:-∀ d₁ d₂) =
  <:-∀ (narrow sh eq nr d₁)
       (narrow sh (≡-trans (shape-ren _ _) eq) (narrow-ext nr type _) d₂)
narrow sh eq nr (⊢` {x = x} e) with nr _ x
... | inj₁ eq₂       = ⊢` (≡-trans eq₂ e)
... | inj₂ (eqQ , d) = ⊢<: (⊢` refl)
      (subst (λ z → _ ⊢ _ ∶ z) (sym (≡-trans (sym e) eqQ)) d)
narrow sh eq nr (⊢λ d) =
  ⊢λ (narrow sh (≡-trans (shape-ren _ _) eq) (narrow-ext nr expr _) d)
narrow sh eq nr (⊢Λ d) =
  ⊢Λ (narrow sh (≡-trans (shape-ren _ _) eq) (narrow-ext nr type _) d)
narrow sh eq nr (⊢· d₁ d₂)  = ⊢· (narrow sh eq nr d₁) (narrow sh eq nr d₂)
narrow sh eq nr (⊢• d₁ d₂)  = ⊢• (narrow sh eq nr d₁) (narrow sh eq nr d₂)
narrow sh eq nr (⊢<: d₁ d₂) = ⊢<: (narrow sh eq nr d₁) (narrow sh eq nr d₂)

-- ═══ 1A, as stated in the challenge ═════════════════════════════════

-- Transitivity:  Γ ⊢ S <: Q  →  Γ ⊢ Q <: T  →  Γ ⊢ S <: T
transitivity : ∀ {Γ : Ctx S} {A Q B : S ⊢ type} →
  Γ ⊢ A <: Q → Γ ⊢ Q <: B → Γ ⊢ A <: B
transitivity {Q = Q} d₁ d₂ = <:-trans (shape Q) refl d₁ d₂

-- Narrowing:  Γ,α<:Q ⊢ M <: N  →  Γ ⊢ P <: Q  →  Γ,α<:P ⊢ M <: N
-- (sort-generic: the same statement narrows a TYPING derivation)
narrowing : ∀ {Γ : Ctx S} {P Q : S ⊢ type} {t : (type ∷ S) ⊢ s} {A} →
  Γ ⊢ P <: Q → (Q ∷ₜ Γ) ⊢ t ∶ A → (P ∷ₜ Γ) ⊢ t ∶ A
narrowing {Q = Q} d = narrow (shape Q) (shape-ren Q (wkᴿ type)) (narrow-here d)

-- ─── typed substitutions ────────────────────────────────────────────
-- ONE definition: at a type variable it demands a SUBTYPING fact, at a
-- term variable a TYPING fact.  This is exactly F<:'s notion of a
-- well-typed simultaneous type-and-term substitution.

_∶_→ˢ_ : S₁ →ˢ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ˢ_ {S₁} σ Γ₁ Γ₂ = ∀ s (x : S₁ ∋ s) (A : S₁ ∶⊢ s) →
  Γ₁ ∋ x ∶ A → Γ₂ ⊢ (x [ σ ]ˢ) ∶ (A [ σ ]ˢ)

⊢↑ˢ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} → σ ∶ Γ₁ →ˢ Γ₂ →
  (A : S₁ ∶⊢ s) → (σ ↑ˢ s) ∶ (A ∷ₜ Γ₁) →ˢ ((A [ σ ]ˢ) ∷ₜ Γ₂)
⊢↑ˢ ⊢σ A _ zero    _ refl = ⊢var refl
⊢↑ˢ {σ = σ} ⊢σ A _ (suc x) _ refl = ⊢weaken (A [ σ ]ˢ) (⊢σ _ x _ refl)

infixl 5 _⊢⋯ˢ_
_⊢⋯ˢ_ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂}
  {t : S₁ ⊢ s} {A : S₁ ∶⊢ s} →
  Γ₁ ⊢ t ∶ A → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (t [ σ ]ˢ) ∶ (A [ σ ]ˢ)
_⊢⋯ˢ_ <:-top  ⊢σ = <:-top
_⊢⋯ˢ_ <:-refl ⊢σ = <:-reflexive _
_⊢⋯ˢ_ {σ = σ} (<:-var {α = α} e u) ⊢σ =
  transitivity (⊢σ _ α _ e) (_⊢⋯ˢ_ {σ = σ} u ⊢σ)
_⊢⋯ˢ_ {σ = σ} (<:-⇒ d₁ d₂) ⊢σ =
  <:-⇒ (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} (<:-∀ d₁ d₂) ⊢σ =
  <:-∀ (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ ↑ˢ _} d₂ (⊢↑ˢ {σ = σ} ⊢σ _))
_⊢⋯ˢ_ (⊢` e) ⊢σ = ⊢σ _ _ _ e
_⊢⋯ˢ_ {σ = σ} (⊢λ d) ⊢σ = ⊢λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} d (⊢↑ˢ {σ = σ} ⊢σ _))
_⊢⋯ˢ_ {σ = σ} (⊢Λ d) ⊢σ = ⊢Λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} d (⊢↑ˢ {σ = σ} ⊢σ _))
_⊢⋯ˢ_ {σ = σ} (⊢· d₁ d₂) ⊢σ =
  ⊢· (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} (⊢• d₁ d₂) ⊢σ =
  ⊢• (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} (⊢<: d₁ d₂) ⊢σ =
  ⊢<: (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)

-- the single-point substitution, again sort-generic: at s = expr this
-- is the term substitution lemma, at s = type the type substitution
-- lemma (whose premise is a SUBTYPING derivation Γ ⊢ C <: A)
⊢[] : ∀ {Γ : Ctx S} {t : S ⊢ s} {A : S ∶⊢ s} →
  Γ ⊢ t ∶ A → (t ∙ˢ idˢ) ∶ (A ∷ₜ Γ) →ˢ Γ
⊢[] d _ zero    _ refl = d
⊢[] d _ (suc x) _ refl = ⊢var refl

-- ═══ PART 2A: preservation and progress ═════════════════════════════

data Val : S ⊢ expr → Set where
  vλ : Val (λx[ A ] e)
  vΛ : Val (Λα[<: A ] e)

infix 3 _↪_
data _↪_ : S ⊢ expr → S ⊢ expr → Set where
  β-λ  : Val e₂ → ((λx[ A ] e₁) · e₂) ↪ (e₁ [ e₂ ]₀)
  β-Λ  : ((Λα[<: A ] e) • C) ↪ (e [ C ]₀)
  ξ-·₁ : e₁ ↪ e → (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂ : Val e₁ → e₂ ↪ e → (e₁ · e₂) ↪ (e₁ · e)
  ξ-•  : e ↪ e′ → (e • C) ↪ (e′ • C)

-- ─── inversion ──────────────────────────────────────────────────────
-- Stated with the subtyping step built in, as in TAPL 28.  This is
-- where transitivity (⊢<: case) and narrowing (⊢Λ case) are cashed in.

inv-λ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (λx[ A ] e) ∶ C → Γ ⊢ C <: (B₁ ⇒ B₂) →
  (Γ ⊢ B₁ <: A) × ((A ∷ₜ Γ) ⊢ e ∶ weaken B₂)
inv-λ (⊢λ d)     (<:-⇒ s₁ s₂) = s₁ , ⊢<: d (⊢weaken _ s₂)
inv-λ (⊢<: d s)  sub          = inv-λ d (transitivity s sub)

inv-Λ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (Λα[<: A ] e) ∶ C → Γ ⊢ C <: (∀[<: B₁ ] B₂) →
  (Γ ⊢ B₁ <: A) × ((B₁ ∷ₜ Γ) ⊢ e ∶ B₂)
inv-Λ (⊢Λ d)    (<:-∀ s₁ s₂) = s₁ , ⊢<: (narrowing s₁ d) s₂
inv-Λ (⊢<: d s) sub          = inv-Λ d (transitivity s sub)

-- a Λ never has an arrow type, and a λ never has a ∀ type
not-Λ-⇒ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (Λα[<: A ] e) ∶ C → Γ ⊢ C <: (B₁ ⇒ B₂) → ⊥
not-Λ-⇒ (⊢Λ d)    ()
not-Λ-⇒ (⊢<: d s) sub = not-Λ-⇒ d (transitivity s sub)

not-λ-∀ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (λx[ A ] e) ∶ C → Γ ⊢ C <: (∀[<: B₁ ] B₂) → ⊥
not-λ-∀ (⊢λ d)    ()
not-λ-∀ (⊢<: d s) sub = not-λ-∀ d (transitivity s sub)

-- ─── preservation ───────────────────────────────────────────────────

preservation : ∀ {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ↪ e′ → Γ ⊢ e′ ∶ A
preservation (⊢` _)  ()
preservation (⊢λ _)  ()
preservation (⊢Λ _)  ()
preservation (⊢· {e₂ = e₂} d₁ d₂) (β-λ v) with inv-λ d₁ (<:-reflexive _)
... | (sub , body) = _⊢⋯ˢ_ {σ = e₂ ∙ˢ idˢ} body (⊢[] (⊢<: d₂ sub))
preservation (⊢· d₁ d₂) (ξ-·₁ st)   = ⊢· (preservation d₁ st) d₂
preservation (⊢· d₁ d₂) (ξ-·₂ v st) = ⊢· d₁ (preservation d₂ st)
preservation (⊢• {C = C} d₁ d₂) β-Λ with inv-Λ d₁ (<:-reflexive _)
... | (sub , body) = _⊢⋯ˢ_ {σ = C ∙ˢ idˢ} body (⊢[] d₂)
preservation (⊢• d₁ d₂) (ξ-• st) = ⊢• (preservation d₁ st) d₂
preservation (⊢<: d s)  st       = ⊢<: (preservation d st) s

-- ─── progress ───────────────────────────────────────────────────────

data Progress {S} (e : S ⊢ expr) : Set where
  step : ∀ {e′ : S ⊢ expr} → e ↪ e′ → Progress e
  done : Val e → Progress e

-- canonical forms, by matching on the value rather than on an equation
app-step : ∀ {Γ : Ctx S} {e₁ e₂ : S ⊢ expr} {A B} →
  Γ ⊢ e₁ ∶ (A ⇒ B) → Val e₁ → Val e₂ → Progress (e₁ · e₂)
app-step d vλ v₂ = step (β-λ v₂)
app-step d vΛ v₂ = ⊥-elim (not-Λ-⇒ d (<:-reflexive _))

tapp-step : ∀ {Γ : Ctx S} {e : S ⊢ expr} {A B C} →
  Γ ⊢ e ∶ (∀[<: A ] B) → Val e → Progress (e • C)
tapp-step d vλ = ⊥-elim (not-λ-∀ d (<:-reflexive _))
tapp-step d vΛ = step β-Λ

progress : ∀ {Γ : Ctx []} {e : [] ⊢ expr} {A} → Γ ⊢ e ∶ A → Progress e
progress (⊢` {x = ()} _)
progress (⊢λ _) = done vλ
progress (⊢Λ _) = done vΛ
progress (⊢· d₁ d₂) with progress d₁
... | step st = step (ξ-·₁ st)
... | done v₁ with progress d₂
...   | step st = step (ξ-·₂ v₁ st)
...   | done v₂ = app-step d₁ v₁ v₂
progress (⊢• d₁ d₂) with progress d₁
... | step st = step (ξ-• st)
... | done v  = tapp-step d₁ v
progress (⊢<: d _) = progress d

-- ─── sanity: the encoding is not vacuous ────────────────────────────

Γ₀ : Ctx []
Γ₀ _ ()

-- Λα<:Top. λx:α. x   :   ∀α<:Top. α → α
polyId : [] ⊢ expr
polyId = Λα[<: Top ] (λx[ ` zero ] (` zero))

⊢polyId : Γ₀ ⊢ polyId ∶ (∀[<: Top ] ((` zero) ⇒ (` zero)))
⊢polyId = ⊢Λ (⊢λ (⊢` refl))

-- the type application computes:  (α→α)[Top] ≡ Top → Top, definitionally
⊢polyId·Top : Γ₀ ⊢ (polyId • Top) ∶ (Top ⇒ Top)
⊢polyId·Top = ⊢• ⊢polyId <:-top

-- preservation, run on a concrete redex:  (Λα<:Top.λx:α.x) [Top] ↪ λx:Top.x
⊢reduct : Γ₀ ⊢ (λx[ Top ] (` zero)) ∶ (Top ⇒ Top)
⊢reduct = preservation ⊢polyId·Top β-Λ

-- progress, run on the same term
progress-test : Progress (polyId • Top)
progress-test = progress ⊢polyId·Top

-- a non-reflexive subtyping fact through a context bound, and a use of
-- transitivity and of narrowing at the top-level statements
Γᵗ : Ctx (type ∷ [])
Γᵗ = Top ∷ₜ Γ₀

α<:Top : Γᵗ ⊢ (` zero) <: Top
α<:Top = <:-var refl <:-top

trans-test : Γᵗ ⊢ (` zero) <: Top
trans-test = transitivity α<:Top <:-top

-- narrowing the bound of α from Top down to Top→Top
narrowing-test : ((Top ⇒ Top) ∷ₜ Γ₀) ⊢ (` zero) <: Top
narrowing-test = narrowing {P = Top ⇒ Top} {Q = Top} <:-top α<:Top

-- ═══ NARROWING WITH A TRAILING ∆ — challenge Lemma 3.2 in full ══════
-- A telescope of binders extending S to S′, i.e. the challenge's ∆.

data Tele (S : Scope) : Scope → Set where
  []  : Tele S S
  _◂_ : ∀ {S′ s} (A : S′ ∶⊢ s) → Tele S S′ → Tele S (s ∷ S′)

infixr 5 _◂_

_▸_ : ∀ {S S′} → Tele S S′ → Ctx S → Ctx S′
[]      ▸ Γ = Γ
(A ◂ Δ) ▸ Γ = A ∷ₜ (Δ ▸ Γ)

wk-tele : ∀ {S S′} → Tele S S′ → S ⊢ type → S′ ⊢ type
wk-tele []      A = A
wk-tele (B ◂ Δ) A = weaken (wk-tele Δ A)

narrow-tele : ∀ {S S′} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} (Δ : Tele S S′) →
  Narrowing Γ₂ Q Γ₁ → Narrowing (Δ ▸ Γ₂) (wk-tele Δ Q) (Δ ▸ Γ₁)
narrow-tele []                nr = nr
narrow-tele (_◂_ {s = s} A Δ) nr = narrow-ext (narrow-tele Δ nr) s A

shape-wk-tele : ∀ {S S′} (Δ : Tele S S′) (A : S ⊢ type) →
  shape (wk-tele Δ A) ≡ shape A
shape-wk-tele []      A = refl
shape-wk-tele (B ◂ Δ) A =
  ≡-trans (shape-ren (wk-tele Δ A) (wkᴿ _)) (shape-wk-tele Δ A)

-- 3.2 Lemma [Narrowing]: If Γ, X<:Q, ∆ ⊢ M <: N and Γ ⊢ P <: Q
--                        then Γ, X<:P, ∆ ⊢ M <: N.
narrowing∆ : ∀ {S S′} {Γ : Ctx S} {P Q : S ⊢ type} (Δ : Tele (type ∷ S) S′)
  {t : S′ ⊢ s} {A : S′ ∶⊢ s} →
  Γ ⊢ P <: Q → (Δ ▸ (Q ∷ₜ Γ)) ⊢ t ∶ A → (Δ ▸ (P ∷ₜ Γ)) ⊢ t ∶ A
narrowing∆ {Q = Q} Δ d =
  narrow (shape Q)
    (≡-trans (shape-wk-tele Δ (weaken Q)) (shape-ren Q (wkᴿ type)))
    (narrow-tele Δ (narrow-here d))

-- the ∆ = ∅ instance is the old statement
narrowing′ : ∀ {Γ : Ctx S} {P Q : S ⊢ type} {t : (type ∷ S) ⊢ s} {A} →
  Γ ⊢ P <: Q → (Q ∷ₜ Γ) ⊢ t ∶ A → (P ∷ₜ Γ) ⊢ t ∶ A
narrowing′ = narrowing∆ []

-- ═══ EVALUATION CONTEXTS, AND THE EQUIVALENCE ═══════════════════════
-- The challenge presents evaluation as two immediate reduction rules
-- (E-AppAbs, E-TappTabs) plus E-Ctx over
--     E ::= [−] | E t | v E | E [T]
-- Footnote 5 sanctions the congruence-rule presentation used above, but
-- does not excuse leaving the two unrelated.  Here they are related.

data ECtx (S : Scope) : Set where
  □    : ECtx S
  appl : ECtx S → S ⊢ expr → ECtx S                 -- E t
  appr : (v : S ⊢ expr) → Val v → ECtx S → ECtx S   -- v E
  tapp : ECtx S → S ⊢ type → ECtx S                 -- E [T]

plug : ECtx S → S ⊢ expr → S ⊢ expr
plug □            e = e
plug (appl E t)   e = (plug E e) · t
plug (appr v _ E) e = v · (plug E e)
plug (tapp E C)   e = (plug E e) • C

-- the immediate reduction rules, exactly as displayed in the challenge
infix 3 _↦_
data _↦_ : S ⊢ expr → S ⊢ expr → Set where
  E-AppAbs   : Val e₂ → ((λx[ A ] e₁) · e₂) ↦ (e₁ [ e₂ ]₀)
  E-TappTabs : ((Λα[<: A ] e) • C) ↦ (e [ C ]₀)

-- E-Ctx
infix 3 _⟶_
data _⟶_ : S ⊢ expr → S ⊢ expr → Set where
  E-Ctx : ∀ (E : ECtx S) {e e′} → e ↦ e′ → (plug E e) ⟶ (plug E e′)

-- the two presentations coincide
↪→⟶ : ∀ {e e′ : S ⊢ expr} → e ↪ e′ → e ⟶ e′
↪→⟶ (β-λ v)     = E-Ctx □ (E-AppAbs v)
↪→⟶ β-Λ         = E-Ctx □ E-TappTabs
↪→⟶ (ξ-·₁ {e₂ = e₂} st) with ↪→⟶ st
... | E-Ctx E st₀ = E-Ctx (appl E e₂) st₀
↪→⟶ (ξ-·₂ {e₁ = e₁} v st) with ↪→⟶ st
... | E-Ctx E st₀ = E-Ctx (appr e₁ v E) st₀
↪→⟶ (ξ-• {C = C} st) with ↪→⟶ st
... | E-Ctx E st₀ = E-Ctx (tapp E C) st₀

plug-↪ : ∀ (E : ECtx S) {e e′ : S ⊢ expr} → e ↦ e′ → (plug E e) ↪ (plug E e′)
plug-↪ □            (E-AppAbs v) = β-λ v
plug-↪ □            E-TappTabs   = β-Λ
plug-↪ (appl E t)   st = ξ-·₁ (plug-↪ E st)
plug-↪ (appr v p E) st = ξ-·₂ p (plug-↪ E st)
plug-↪ (tapp E C)   st = ξ-• (plug-↪ E st)

⟶→↪ : ∀ {e e′ : S ⊢ expr} → e ⟶ e′ → e ↪ e′
⟶→↪ (E-Ctx E st) = plug-↪ E st

-- therefore preservation and progress hold verbatim for the challenge's
-- evaluation-context relation as well
preservation⟶ : ∀ {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ⟶ e′ → Γ ⊢ e′ ∶ A
preservation⟶ d st = preservation d (⟶→↪ st)

data Progress⟶ {S} (e : S ⊢ expr) : Set where
  step⟶ : ∀ {e′ : S ⊢ expr} → e ⟶ e′ → Progress⟶ e
  done⟶ : Val e → Progress⟶ e

progress⟶ : ∀ {Γ : Ctx []} {e : [] ⊢ expr} {A} → Γ ⊢ e ∶ A → Progress⟶ e
progress⟶ d with progress d
... | step st = step⟶ (↪→⟶ st)
... | done v  = done⟶ v

-- ═══ DECLARATIVE SUBTYPING, AND THE EQUIVALENCE ═════════════════════
-- The challenge (§3): "The declarative rules differ from these by
-- explicitly stating that subtyping is reflexive and transitive."
-- Here is that system, and its equivalence with the algorithmic one.

infix 3 _⊢_<:ᵈ_
data _⊢_<:ᵈ_ {S} (Γ : Ctx S) : S ⊢ type → S ⊢ type → Set where
  S-Top   : ∀ {A} → Γ ⊢ A <:ᵈ Top
  S-TVar  : ∀ {α : S ∋ type} {U} → Γ ∋ α ∶ U → Γ ⊢ (` α) <:ᵈ U
  S-Refl  : ∀ {A} → Γ ⊢ A <:ᵈ A
  S-Trans : ∀ {A U B} → Γ ⊢ A <:ᵈ U → Γ ⊢ U <:ᵈ B → Γ ⊢ A <:ᵈ B
  S-Arrow : ∀ {A₁ A₂ B₁ B₂} → Γ ⊢ B₁ <:ᵈ A₁ → Γ ⊢ A₂ <:ᵈ B₂ →
            Γ ⊢ (A₁ ⇒ A₂) <:ᵈ (B₁ ⇒ B₂)
  S-All   : ∀ {A₁ A₂ B₁ B₂} → Γ ⊢ B₁ <:ᵈ A₁ → (B₁ ∷ₜ Γ) ⊢ A₂ <:ᵈ B₂ →
            Γ ⊢ (∀[<: A₁ ] A₂) <:ᵈ (∀[<: B₁ ] B₂)

-- soundness of the algorithmic system
alg→decl : ∀ {Γ : Ctx S} {A B : S ⊢ type} → Γ ⊢ A <: B → Γ ⊢ A <:ᵈ B
alg→decl <:-top        = S-Top
alg→decl <:-refl       = S-Refl
alg→decl (<:-var eq u) = S-Trans (S-TVar eq) (alg→decl u)
alg→decl (<:-⇒ d₁ d₂)  = S-Arrow (alg→decl d₁) (alg→decl d₂)
alg→decl (<:-∀ d₁ d₂)  = S-All (alg→decl d₁) (alg→decl d₂)

-- completeness: this is where transitivity (3.1) and reflexivity are
-- cashed in — exactly the two rules the declarative system adds
decl→alg : ∀ {Γ : Ctx S} {A B : S ⊢ type} → Γ ⊢ A <:ᵈ B → Γ ⊢ A <: B
decl→alg S-Top           = <:-top
decl→alg (S-TVar eq)     = <:-var eq (<:-reflexive _)
decl→alg S-Refl          = <:-reflexive _
decl→alg (S-Trans d₁ d₂) = transitivity (decl→alg d₁) (decl→alg d₂)
decl→alg (S-Arrow d₁ d₂) = <:-⇒ (decl→alg d₁) (decl→alg d₂)
decl→alg (S-All d₁ d₂)   = <:-∀ (decl→alg d₁) (decl→alg d₂)

-- the two systems derive exactly the same judgments
algorithmic≡declarative : ∀ {Γ : Ctx S} {A B : S ⊢ type} →
  (Γ ⊢ A <: B → Γ ⊢ A <:ᵈ B) × (Γ ⊢ A <:ᵈ B → Γ ⊢ A <: B)
algorithmic≡declarative = alg→decl , decl→alg

-- ═══ CHALLENGE-REFERENCING NAMES ════════════════════════════════════
-- The names below are the ones a reader should match against the
-- challenge document; the short names above are kept because the
-- internal proofs read better with them.

-- 3.1 Lemma [Transitivity of Algorithmic Subtyping]
lemma-3-1-transitivity : ∀ {Γ : Ctx S} {A Q B : S ⊢ type} →
  Γ ⊢ A <: Q → Γ ⊢ Q <: B → Γ ⊢ A <: B
lemma-3-1-transitivity = transitivity

-- 3.2 Lemma [Narrowing], with the trailing ∆
lemma-3-2-narrowing : ∀ {S S′} {Γ : Ctx S} {P Q : S ⊢ type}
  (Δ : Tele (type ∷ S) S′) {t : S′ ⊢ s} {A : S′ ∶⊢ s} →
  Γ ⊢ P <: Q → (Δ ▸ (Q ∷ₜ Γ)) ⊢ t ∶ A → (Δ ▸ (P ∷ₜ Γ)) ⊢ t ∶ A
lemma-3-2-narrowing = narrowing∆

-- 3.3 Theorem [Preservation], for the challenge's E-Ctx relation
theorem-3-3-preservation : ∀ {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ⟶ e′ → Γ ⊢ e′ ∶ A
theorem-3-3-preservation = preservation⟶

-- 3.4 Theorem [Progress], for the challenge's E-Ctx relation
theorem-3-4-progress : ∀ {Γ : Ctx []} {e : [] ⊢ expr} {A} →
  Γ ⊢ e ∶ A → Progress⟶ e
theorem-3-4-progress = progress⟶
