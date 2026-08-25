{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLmark Challenge, Part 1B (and the record half of 2B) ════════
--
--   1B  transitivity of subtyping with records  (+ narrowing)
--   2B  preservation and progress for F<: with records and projection
--       (the `let`/pattern half of 2B is in Challenge/Patterns.agda)
--
-- Record types and record terms are terms of the sorts `rtype`/`rexpr`
-- of the core, so the typed-map machinery of Challenge/Subtyping.agda
-- carries over unchanged -- there is no record traversal and no record
-- substitution lemma anywhere in this file.

module Challenge.Records where

open import Languages.FsubRecords

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; subst) renaming (trans to ≡-trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; drop)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; n≤1+n)

-- ─── the language-specific layer this metatheory sits on ────────────
-- Moved out of Languages.FsubRecords: none of it is σ-calculus.  It is contexts,
-- generalizable variables and congruences for this language, so it
-- belongs with the proofs and not in generated output.

-- ─── the generalizable variables the metatheory expects ─────────────

variable
  e e₁ e₂ e′              : S ⊢ expr
  A A₁ A₂ B B₁ B₂ C P Q U : S ⊢ type
  rt rt₁ rt₂              : S ⊢ rtype
  re re₁ re₂              : S ⊢ rexpr
  α                       : S ∋ s
  n n₁ n₂                 : ℕ
  l l′                    : Label

-- ─── contexts ───────────────────────────────────────────────────────

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


-- ─── field membership ───────────────────────────────────────────────
-- The challenge's  lᵢ ∈ {kⱼ}, together with the selection of the
-- corresponding type.
-- NOTE this is membership, not lookup-by-label.  With a lookup function,
-- reflexivity of record subtyping would need the challenge's
-- pairwise-distinctness side condition to be carried as a
-- well-formedness judgment; with membership it does not, and the two
-- formulations agree exactly on the distinct-label records that the
-- challenge's syntax admits.

-- `Has rt l A` = "l is a field of rt, at its first occurrence, with
-- type A".  On the distinct-label records the challenge's syntax admits
-- this is the same as plain membership; making it first-occurrence is
-- what makes field selection functional, which E-ProjRcd needs.
data Has {S} : S ⊢ rtype → Label → S ⊢ type → Set where
  here  : ∀ {l A rt} → Has (consT l A rt) l A
  there : ∀ {l A l′ A′ rt} → l ≢ l′ → Has rt l A → Has (consT l′ A′ rt) l A

data HasE {S} : S ⊢ rexpr → Label → S ⊢ expr → Set where
  hereE  : ∀ {l e re} → HasE (consE l e re) l e
  thereE : ∀ {l e l′ e′ re} → l ≢ l′ → HasE re l e → HasE (consE l′ e′ re) l e

HasE-unique : ∀ {S} {re : S ⊢ rexpr} {l e e′} → HasE re l e → HasE re l e′ → e ≡ e′
HasE-unique hereE          hereE          = refl
HasE-unique hereE          (thereE ne _)  = ⊥-elim (ne refl)
HasE-unique (thereE ne _)  hereE          = ⊥-elim (ne refl)
HasE-unique (thereE _ a)   (thereE _ b)   = HasE-unique a b

-- membership is stable under both kinds of map, definitionally
Has-ren : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} {l A} {ξ : S₁ →ᴿ S₂} →
  Has rt l A → Has (rt [ ξ ]ᴿ) l (A [ ξ ]ᴿ)
Has-ren here            = here
Has-ren {ξ = ξ} (there ne h) = there ne (Has-ren {ξ = ξ} h)

Has-sub : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} {l A} {σ : S₁ →ˢ S₂} →
  Has rt l A → Has (rt [ σ ]ˢ) l (A [ σ ]ˢ)
Has-sub here            = here
Has-sub {σ = σ} (there ne h) = there ne (Has-sub {σ = σ} h)

-- ─── the judgments ──────────────────────────────────────────────────
-- `_⊢_∶_` is still one family carrying subtyping (sort type) and typing
-- (sort expr).  Record subtyping and record-term typing need their own
-- judgments: their two sides live at sort `rtype`/`rexpr`, not at
-- `type`, so they do not fit the `Γ ⊢ t ∶ (t : S ∶⊢ s)` shape.

infix 3 _⊢_∶_ _⊢_<:ᴿ_ _⊢_∶ᴿ_

data _⊢_∶_   : Ctx S → S ⊢ s → S ∶⊢ s → Set
data _⊢_<:ᴿ_ : Ctx S → S ⊢ rtype → S ⊢ rtype → Set
data _⊢_∶ᴿ_  : Ctx S → S ⊢ rexpr → S ⊢ rtype → Set

data _⊢_∶_ where
  -- algorithmic subtyping
  <:-top  : Γ ⊢ A ∶ Top
  <:-refl : ∀ {α : S ∋ type} {Γ : Ctx S} → Γ ⊢ (` α) ∶ (` α)
  <:-var  : ∀ {α : S ∋ type} {Γ : Ctx S} {U B} →
    Γ ∋ α ∶ U → Γ ⊢ U ∶ B → Γ ⊢ (` α) ∶ B
  <:-⇒    : Γ ⊢ B₁ ∶ A₁ → Γ ⊢ A₂ ∶ B₂ → Γ ⊢ (A₁ ⇒ A₂) ∶ (B₁ ⇒ B₂)
  <:-∀    : Γ ⊢ B₁ ∶ A₁ → (B₁ ∷ₜ Γ) ⊢ A₂ ∶ B₂ →
            Γ ⊢ (∀[<: A₁ ] A₂) ∶ (∀[<: B₁ ] B₂)
  <:-rcd  : Γ ⊢ rt₁ <:ᴿ rt₂ → Γ ⊢ (RcdT rt₁) ∶ (RcdT rt₂)
  -- typing
  ⊢`      : ∀ {x : S ∋ expr} {Γ : Ctx S} {A} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  -- vacuous on the challenge's language: F<: has no variables at the
  -- record-body sorts, but the mode-merged family `_⊢[_]_` admits a
  -- variable at every sort, so the judgment has to be total there.
  ⊢`ᴿ     : ∀ {x : S ∋ rtype} {Γ : Ctx S} {A} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢`ᴱ     : ∀ {x : S ∋ rexpr} {Γ : Ctx S} {A} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
  ⊢λ      : (A ∷ₜ Γ) ⊢ e ∶ weaken B → Γ ⊢ (λx[ A ] e) ∶ (A ⇒ B)
  ⊢Λ      : (A ∷ₜ Γ) ⊢ e ∶ B → Γ ⊢ (Λα[<: A ] e) ∶ (∀[<: A ] B)
  ⊢·      : Γ ⊢ e₁ ∶ (A ⇒ B) → Γ ⊢ e₂ ∶ A → Γ ⊢ (e₁ · e₂) ∶ B
  ⊢•      : Γ ⊢ e ∶ (∀[<: A ] B) → Γ ⊢ C ∶ A → Γ ⊢ (e • C) ∶ (B [ C ]₀)
  ⊢rcd    : Γ ⊢ re ∶ᴿ rt → Γ ⊢ (RcdE re) ∶ (RcdT rt)
  ⊢#      : ∀ {Γ : Ctx S} {e rt l A} →
            Γ ⊢ e ∶ (RcdT rt) → Has rt l A → Γ ⊢ (e # l) ∶ A
  ⊢<:     : Γ ⊢ e ∶ A → Γ ⊢ A ∶ B → Γ ⊢ e ∶ B

-- sa-Rcd, read as an induction over the right-hand record:
-- every field of the supertype must be present in the subtype, with a
-- subtype-related field type.  Width, depth and permutation at once.
data _⊢_<:ᴿ_ where
  <:ᴿ-nil  : ∀ {Γ : Ctx S} {rt} → Γ ⊢ rt <:ᴿ nilT
  -- explicit reflexivity.  In the challenge this rule is admissible
  -- (sa-Rcd + distinct labels derives it); here it is a primitive rule,
  -- because the multi-sorted syntax admits a record body that is a
  -- variable, for which the structural proof of reflexivity has no
  -- case.  `<:ᴿ-var-forces-refl` below proves the rule cannot simply be
  -- dropped; `_⊢_<:ᴿᶜ_` further down eliminates it under a
  -- well-formedness hypothesis.
  <:ᴿ-refl : ∀ {Γ : Ctx S} {rt} → Γ ⊢ rt <:ᴿ rt
  <:ᴿ-cons : ∀ {Γ : Ctx S} {rt₁ rt₂ l A B} →
    Has rt₁ l A → Γ ⊢ A ∶ B → Γ ⊢ rt₁ <:ᴿ rt₂ → Γ ⊢ rt₁ <:ᴿ (consT l B rt₂)

-- T-Rcd
data _⊢_∶ᴿ_ where
  ⊢ᴿ-nil  : ∀ {Γ : Ctx S} → Γ ⊢ nilE ∶ᴿ nilT
  ⊢ᴿ-cons : ∀ {Γ : Ctx S} {l e re A rt} →
    Γ ⊢ e ∶ A → Γ ⊢ re ∶ᴿ rt → Γ ⊢ (consE l e re) ∶ᴿ (consT l A rt)

infix 3 _⊢_<:_
_⊢_<:_ : Ctx S → S ⊢ type → S ⊢ type → Set
Γ ⊢ A <: B = Γ ⊢ A ∶ B

-- ─── reflexivity ────────────────────────────────────────────────────

<:-reflexive : ∀ (A : S ⊢ type) {Γ : Ctx S} → Γ ⊢ A <: A
<:-reflexive Top          = <:-top
<:-reflexive (` α)        = <:-refl
<:-reflexive (A ⇒ B)      = <:-⇒ (<:-reflexive A) (<:-reflexive B)
<:-reflexive (∀[<: A ] B) = <:-∀ (<:-reflexive A) (<:-reflexive B)
<:-reflexive (RcdT rt)    = <:-rcd <:ᴿ-refl

⊢var : ∀ {Γ : Ctx S} {x : S ∋ s} {A : S ∶⊢ s} → Γ ∋ x ∶ A → Γ ⊢ (` x) ∶ A
⊢var {s = expr}  eq = ⊢` eq
⊢var {s = type}  eq = <:-var eq (<:-reflexive _)
⊢var {s = rtype} eq = ⊢`ᴿ eq
⊢var {s = rexpr} eq = ⊢`ᴱ eq

-- ─── typed renamings ────────────────────────────────────────────────

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
_⊢⋯ᴿ_  : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {t : S₁ ⊢ s} {A : S₁ ∶⊢ s} →
  Γ₁ ⊢ t ∶ A → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (t [ ξ ]ᴿ) ∶ (A [ ξ ]ᴿ)
_⊢⋯ᴿᴿ_ : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {rt₁ rt₂ : S₁ ⊢ rtype} →
  Γ₁ ⊢ rt₁ <:ᴿ rt₂ → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (rt₁ [ ξ ]ᴿ) <:ᴿ (rt₂ [ ξ ]ᴿ)
_⊢⋯ᴿᴱ_ : ∀ {ξ : S₁ →ᴿ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {re : S₁ ⊢ rexpr} {rt : S₁ ⊢ rtype} →
  Γ₁ ⊢ re ∶ᴿ rt → ξ ∶ Γ₁ →ᴿ Γ₂ → Γ₂ ⊢ (re [ ξ ]ᴿ) ∶ᴿ (rt [ ξ ]ᴿ)

<:-top          ⊢⋯ᴿ ⊢ξ = <:-top
<:-refl         ⊢⋯ᴿ ⊢ξ = <:-refl
(<:-var ⊢α ⊢U)  ⊢⋯ᴿ ⊢ξ = <:-var (⊢ξ _ _ _ ⊢α) (⊢U ⊢⋯ᴿ ⊢ξ)
(<:-⇒ d₁ d₂)    ⊢⋯ᴿ ⊢ξ = <:-⇒ (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)
(<:-∀ d₁ d₂)    ⊢⋯ᴿ ⊢ξ = <:-∀ (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢↑ᴿ ⊢ξ _)
(<:-rcd r)      ⊢⋯ᴿ ⊢ξ = <:-rcd (r ⊢⋯ᴿᴿ ⊢ξ)
(⊢` ⊢x)         ⊢⋯ᴿ ⊢ξ = ⊢` (⊢ξ _ _ _ ⊢x)
(⊢`ᴿ ⊢x)        ⊢⋯ᴿ ⊢ξ = ⊢`ᴿ (⊢ξ _ _ _ ⊢x)
(⊢`ᴱ ⊢x)        ⊢⋯ᴿ ⊢ξ = ⊢`ᴱ (⊢ξ _ _ _ ⊢x)
(⊢λ d)          ⊢⋯ᴿ ⊢ξ = ⊢λ (d ⊢⋯ᴿ ⊢↑ᴿ ⊢ξ _)
(⊢Λ d)          ⊢⋯ᴿ ⊢ξ = ⊢Λ (d ⊢⋯ᴿ ⊢↑ᴿ ⊢ξ _)
(⊢· d₁ d₂)      ⊢⋯ᴿ ⊢ξ = ⊢· (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)
(⊢• d₁ d₂)      ⊢⋯ᴿ ⊢ξ = ⊢• (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)
(⊢rcd d)        ⊢⋯ᴿ ⊢ξ = ⊢rcd (d ⊢⋯ᴿᴱ ⊢ξ)
(⊢# d h)        ⊢⋯ᴿ ⊢ξ = ⊢# (d ⊢⋯ᴿ ⊢ξ) (Has-ren h)
(⊢<: d₁ d₂)     ⊢⋯ᴿ ⊢ξ = ⊢<: (d₁ ⊢⋯ᴿ ⊢ξ) (d₂ ⊢⋯ᴿ ⊢ξ)

<:ᴿ-nil            ⊢⋯ᴿᴿ ⊢ξ = <:ᴿ-nil
<:ᴿ-refl           ⊢⋯ᴿᴿ ⊢ξ = <:ᴿ-refl
(<:ᴿ-cons h d r)   ⊢⋯ᴿᴿ ⊢ξ = <:ᴿ-cons (Has-ren h) (d ⊢⋯ᴿ ⊢ξ) (r ⊢⋯ᴿᴿ ⊢ξ)

⊢ᴿ-nil          ⊢⋯ᴿᴱ ⊢ξ = ⊢ᴿ-nil
(⊢ᴿ-cons d ds)  ⊢⋯ᴿᴱ ⊢ξ = ⊢ᴿ-cons (d ⊢⋯ᴿ ⊢ξ) (ds ⊢⋯ᴿᴱ ⊢ξ)

⊢weaken : ∀ {S s s′} {Γ : Ctx S} {t : S ⊢ s} {A : S ∶⊢ s} (P : S ∶⊢ s′) →
  Γ ⊢ t ∶ A → (_∷ₜ_ {s = s′} P Γ) ⊢ weaken t ∶ weaken A
⊢weaken P d = d ⊢⋯ᴿ ⊢wkᴿ P

-- ═══ part 1B: transitivity and narrowing, with records ══════════════

-- The induction measure.  Records force a numeric measure: the cut type
-- of a record step is a field of the record, reached through a `Has`
-- proof, and Agda's termination checker cannot see a field selected by
-- a proof as a structural subterm.  (Challenge/Subtyping.agda's `Shape`
-- measure works precisely because F<: without records has only
-- structural subterms.)

size  : S ⊢ type  → ℕ
sizeR : S ⊢ rtype → ℕ
size Top          = 1
size (` α)        = 1
size (A ⇒ B)      = suc (size A + size B)
size (∀[<: A ] B) = suc (size A + size B)
size (RcdT rt)    = suc (sizeR rt)
sizeR (` x)          = 0    -- vacuous: no record-body variables in F<:
sizeR nilT           = 0
sizeR (consT l A rt) = suc (size A + sizeR rt)

size-ren  : ∀ (A : S₁ ⊢ type)  (ξ : S₁ →ᴿ S₂) → size (A [ ξ ]ᴿ) ≡ size A
sizeR-ren : ∀ (rt : S₁ ⊢ rtype) (ξ : S₁ →ᴿ S₂) → sizeR (rt [ ξ ]ᴿ) ≡ sizeR rt
size-ren Top ξ          = refl
size-ren (` α) ξ        = refl
size-ren (A ⇒ B) ξ      = cong₂ (λ a b → suc (a + b)) (size-ren A ξ) (size-ren B ξ)
size-ren (∀[<: A ] B) ξ = cong₂ (λ a b → suc (a + b)) (size-ren A ξ) (size-ren B (ξ ↑ᴿ type))
size-ren (RcdT rt) ξ    = cong suc (sizeR-ren rt ξ)
sizeR-ren (` x) ξ          = refl
sizeR-ren nilT ξ           = refl
sizeR-ren (consT l A rt) ξ = cong₂ (λ a b → suc (a + b)) (size-ren A ξ) (sizeR-ren rt ξ)

Has-size : ∀ {rt : S ⊢ rtype} {l A} → Has rt l A → size A ≤ sizeR rt
Has-size {A = A} (here {rt = rt})  = ≤-trans (m≤m+n (size A) (sizeR rt)) (n≤1+n _)
Has-size (there {A′ = A′} {rt = rt} ne h) =
  ≤-trans (Has-size h) (≤-trans (m≤n+m (sizeR rt) (size A′)) (n≤1+n _))

-- narrowing, as in Challenge/Subtyping.agda
Narrowing : ∀ {S} → Ctx S → S ⊢ type → Ctx S → Set
-- the `s ≡ type` component records that the entry being narrowed is a
-- type binding X<:Q -- which is what the challenge's narrowing lemma
-- narrows.  It also makes the vacuous record sorts fall out.
Narrowing {S} Γ₂ Q Γ₁ = ∀ s (x : S ∋ s) →
    (wk-telescope Γ₂ x ≡ wk-telescope Γ₁ x)
  ⊎ ((s ≡ type) × (wk-telescope Γ₁ x ≡ Q) × (Γ₂ ⊢ wk-telescope Γ₂ x <: Q))

narrow-here : ∀ {S} {Γ : Ctx S} {P Q : S ⊢ type} →
  Γ ⊢ P <: Q → Narrowing {type ∷ S} (P ∷ₜ Γ) (weaken Q) (Q ∷ₜ Γ)
narrow-here d _ zero    = inj₂ (refl , refl , ⊢weaken _ d)
narrow-here d _ (suc y) = inj₁ refl

narrow-ext : ∀ {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} → Narrowing Γ₂ Q Γ₁ →
  ∀ s (P : S ∶⊢ s) → Narrowing {s ∷ S} (P ∷ₜ Γ₂) (weaken Q) (P ∷ₜ Γ₁)
narrow-ext nr s P _ zero = inj₁ refl
narrow-ext nr s P _ (suc y) with nr _ y
... | inj₁ eq             = inj₁ (cong weaken eq)
... | inj₂ (st , eq , d)  = inj₂ (st , cong weaken eq , ⊢weaken P d)

-- The mutual pair, plus their record companions.  Recursion is
-- structural on the fuel `n` bounding `size Q`; the `<:-var` clause
-- keeps `n` and shrinks the derivation.

<:-trans  : ∀ (n : ℕ) {S} {Γ : Ctx S} {A Q B : S ⊢ type} →
  size Q ≤ n → Γ ⊢ A <: Q → Γ ⊢ Q <: B → Γ ⊢ A <: B
<:-transᴿ : ∀ (n : ℕ) {S} {Γ : Ctx S} {rs rq rt : S ⊢ rtype} →
  sizeR rq ≤ n → Γ ⊢ rs <:ᴿ rq → Γ ⊢ rq <:ᴿ rt → Γ ⊢ rs <:ᴿ rt
narrow  : ∀ (n : ℕ) {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} {t : S ⊢ s} {A : S ∶⊢ s} →
  size Q ≤ n → Narrowing Γ₂ Q Γ₁ → Γ₁ ⊢ t ∶ A → Γ₂ ⊢ t ∶ A
narrowᴿ : ∀ (n : ℕ) {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} {rt₁ rt₂ : S ⊢ rtype} →
  size Q ≤ n → Narrowing Γ₂ Q Γ₁ → Γ₁ ⊢ rt₁ <:ᴿ rt₂ → Γ₂ ⊢ rt₁ <:ᴿ rt₂
narrowᴱ : ∀ (n : ℕ) {S} {Γ₁ Γ₂ : Ctx S} {Q : S ⊢ type} {re : S ⊢ rexpr} {rt : S ⊢ rtype} →
  size Q ≤ n → Narrowing Γ₂ Q Γ₁ → Γ₁ ⊢ re ∶ᴿ rt → Γ₂ ⊢ re ∶ᴿ rt

-- inversion of record subtyping at a field: the join used by <:-transᴿ
<:ᴿ-inv : ∀ {Γ : Ctx S} {rs rq : S ⊢ rtype} {l C} →
  Γ ⊢ rs <:ᴿ rq → Has rq l C → Σ[ A ∈ S ⊢ type ] (Has rs l A × Γ ⊢ A <: C)
<:ᴿ-inv <:ᴿ-refl h = _ , h , <:-reflexive _
<:ᴿ-inv (<:ᴿ-cons h d r) here      = _ , h , d
<:ᴿ-inv (<:ᴿ-cons h d r) (there ne m) = <:ᴿ-inv r m

<:-trans n le d₁ <:-top = <:-top
<:-trans n le <:-refl d₂ = d₂
<:-trans n le (<:-var e u) d₂ = <:-var e (<:-trans n le u d₂)
<:-trans (suc n) (s≤s le) (<:-⇒ a₁ a₂) (<:-⇒ b₁ b₂) =
  <:-⇒ (<:-trans n (≤-trans (m≤m+n _ _) le) b₁ a₁)
       (<:-trans n (≤-trans (m≤n+m _ _) le) a₂ b₂)
<:-trans (suc n) (s≤s le) (<:-∀ {B₁ = Q₁} {B₂ = Q₂} a₁ a₂) (<:-∀ b₁ b₂) =
  <:-∀ (<:-trans n (≤-trans (m≤m+n (size Q₁) (size Q₂)) le) b₁ a₁)
       (<:-trans n (≤-trans (m≤n+m (size Q₂) (size Q₁)) le)
         (narrow n (subst (_≤ n) (sym (size-ren Q₁ (wkᴿ type)))
                          (≤-trans (m≤m+n (size Q₁) (size Q₂)) le))
            (narrow-here b₁) a₂)
         b₂)
<:-trans (suc n) (s≤s le) (<:-rcd r₁) (<:-rcd r₂) = <:-rcd (<:-transᴿ n le r₁ r₂)

<:-transᴿ n le r₁ <:ᴿ-nil = <:ᴿ-nil
<:-transᴿ n le r₁ <:ᴿ-refl = r₁
<:-transᴿ n le r₁ (<:ᴿ-cons h d r₂) with <:ᴿ-inv r₁ h
... | (A , h′ , d′) =
  <:ᴿ-cons h′ (<:-trans n (≤-trans (Has-size h) le) d′ d) (<:-transᴿ n le r₁ r₂)

narrow n le nr <:-top  = <:-top
narrow n le nr <:-refl = <:-refl
narrow n le nr (<:-var {α = α} e u) with nr _ α
... | inj₁ eq₂              = <:-var (≡-trans eq₂ e) (narrow n le nr u)
... | inj₂ (refl , eqQ , d) = <:-var refl
      (<:-trans n le d
        (subst (λ z → _ ⊢ z ∶ _) (≡-trans (sym e) eqQ) (narrow n le nr u)))
narrow n le nr (<:-⇒ d₁ d₂) = <:-⇒ (narrow n le nr d₁) (narrow n le nr d₂)
narrow n le nr (<:-∀ d₁ d₂) =
  <:-∀ (narrow n le nr d₁)
       (narrow n (subst (_≤ n) (sym (size-ren _ (wkᴿ type))) le)
               (narrow-ext nr type _) d₂)
narrow n le nr (<:-rcd r) = <:-rcd (narrowᴿ n le nr r)
narrow n le nr (⊢`ᴿ {x = x} e) with nr _ x
... | inj₁ eq₂         = ⊢`ᴿ (≡-trans eq₂ e)
... | inj₂ (() , _ , _)
narrow n le nr (⊢`ᴱ {x = x} e) with nr _ x
... | inj₁ eq₂         = ⊢`ᴱ (≡-trans eq₂ e)
... | inj₂ (() , _ , _)
narrow n le nr (⊢` {x = x} e) with nr _ x
... | inj₁ eq₂         = ⊢` (≡-trans eq₂ e)
... | inj₂ (() , _ , _)
narrow n le nr (⊢λ d) =
  ⊢λ (narrow n (subst (_≤ n) (sym (size-ren _ (wkᴿ expr))) le) (narrow-ext nr expr _) d)
narrow n le nr (⊢Λ d) =
  ⊢Λ (narrow n (subst (_≤ n) (sym (size-ren _ (wkᴿ type))) le) (narrow-ext nr type _) d)
narrow n le nr (⊢· d₁ d₂)  = ⊢· (narrow n le nr d₁) (narrow n le nr d₂)
narrow n le nr (⊢• d₁ d₂)  = ⊢• (narrow n le nr d₁) (narrow n le nr d₂)
narrow n le nr (⊢rcd d)    = ⊢rcd (narrowᴱ n le nr d)
narrow n le nr (⊢# d h)    = ⊢# (narrow n le nr d) h
narrow n le nr (⊢<: d₁ d₂) = ⊢<: (narrow n le nr d₁) (narrow n le nr d₂)

narrowᴿ n le nr <:ᴿ-nil = <:ᴿ-nil
narrowᴿ n le nr <:ᴿ-refl = <:ᴿ-refl
narrowᴿ n le nr (<:ᴿ-cons h d r) = <:ᴿ-cons h (narrow n le nr d) (narrowᴿ n le nr r)

narrowᴱ n le nr ⊢ᴿ-nil = ⊢ᴿ-nil
narrowᴱ n le nr (⊢ᴿ-cons d ds) = ⊢ᴿ-cons (narrow n le nr d) (narrowᴱ n le nr ds)

-- ═══ 1B, as the challenge states it ═════════════════════════════════

-- 3.1 Lemma [Transitivity]: If Γ ⊢ S <: Q and Γ ⊢ Q <: T then Γ ⊢ S <: T
transitivity : ∀ {Γ : Ctx S} {A Q B : S ⊢ type} →
  Γ ⊢ A <: Q → Γ ⊢ Q <: B → Γ ⊢ A <: B
transitivity {Q = Q} = <:-trans (size Q) ≤-refl

-- 3.2 Lemma [Narrowing]: If Γ, X<:Q, ∆ ⊢ M <: N and Γ ⊢ P <: Q
--                        then Γ, X<:P, ∆ ⊢ M <: N
-- (∆ = ∅ here; the general ∆ follows by iterating narrow-ext, and the
--  sort-generic statement narrows a typing derivation as well)
narrowing : ∀ {Γ : Ctx S} {P Q : S ⊢ type} {t : (type ∷ S) ⊢ s} {A} →
  Γ ⊢ P <: Q → (Q ∷ₜ Γ) ⊢ t ∶ A → (P ∷ₜ Γ) ⊢ t ∶ A
narrowing {Q = Q} d =
  narrow (size Q) (subst (_≤ size Q) (sym (size-ren Q (wkᴿ type))) ≤-refl)
         (narrow-here d)

-- ─── typed substitutions ────────────────────────────────────────────

_∶_→ˢ_ : S₁ →ˢ S₂ → Ctx S₁ → Ctx S₂ → Set
_∶_→ˢ_ {S₁} σ Γ₁ Γ₂ = ∀ s (x : S₁ ∋ s) (A : S₁ ∶⊢ s) →
  Γ₁ ∋ x ∶ A → Γ₂ ⊢ (x [ σ ]ˢ) ∶ (A [ σ ]ˢ)

⊢↑ˢ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} → σ ∶ Γ₁ →ˢ Γ₂ →
  (A : S₁ ∶⊢ s) → (σ ↑ˢ s) ∶ (A ∷ₜ Γ₁) →ˢ ((A [ σ ]ˢ) ∷ₜ Γ₂)
⊢↑ˢ ⊢σ A _ zero    _ refl = ⊢var refl
⊢↑ˢ {σ = σ} ⊢σ A _ (suc x) _ refl = ⊢weaken (A [ σ ]ˢ) (⊢σ _ x _ refl)

infixl 5 _⊢⋯ˢ_
_⊢⋯ˢ_  : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {t : S₁ ⊢ s} {A : S₁ ∶⊢ s} →
  Γ₁ ⊢ t ∶ A → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (t [ σ ]ˢ) ∶ (A [ σ ]ˢ)
_⊢⋯ˢᴿ_ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {rt₁ rt₂ : S₁ ⊢ rtype} →
  Γ₁ ⊢ rt₁ <:ᴿ rt₂ → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (rt₁ [ σ ]ˢ) <:ᴿ (rt₂ [ σ ]ˢ)
_⊢⋯ˢᴱ_ : ∀ {σ : S₁ →ˢ S₂} {Γ₁ : Ctx S₁} {Γ₂ : Ctx S₂} {re : S₁ ⊢ rexpr} {rt : S₁ ⊢ rtype} →
  Γ₁ ⊢ re ∶ᴿ rt → σ ∶ Γ₁ →ˢ Γ₂ → Γ₂ ⊢ (re [ σ ]ˢ) ∶ᴿ (rt [ σ ]ˢ)

_⊢⋯ˢ_ {σ = σ} <:-top  ⊢σ = <:-top
_⊢⋯ˢ_ {σ = σ} <:-refl ⊢σ = <:-reflexive _
_⊢⋯ˢ_ {σ = σ} (<:-var {α = α} e u) ⊢σ =
  transitivity (⊢σ _ α _ e) (_⊢⋯ˢ_ {σ = σ} u ⊢σ)
_⊢⋯ˢ_ {σ = σ} (<:-⇒ d₁ d₂) ⊢σ =
  <:-⇒ (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} (<:-∀ d₁ d₂) ⊢σ =
  <:-∀ (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ ↑ˢ _} d₂ (⊢↑ˢ {σ = σ} ⊢σ _))
_⊢⋯ˢ_ {σ = σ} (<:-rcd r) ⊢σ = <:-rcd (_⊢⋯ˢᴿ_ {σ = σ} r ⊢σ)
_⊢⋯ˢ_ (⊢` e) ⊢σ = ⊢σ _ _ _ e
_⊢⋯ˢ_ (⊢`ᴿ e) ⊢σ = ⊢σ _ _ _ e
_⊢⋯ˢ_ (⊢`ᴱ e) ⊢σ = ⊢σ _ _ _ e
_⊢⋯ˢ_ {σ = σ} (⊢λ d) ⊢σ = ⊢λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} d (⊢↑ˢ {σ = σ} ⊢σ _))
_⊢⋯ˢ_ {σ = σ} (⊢Λ d) ⊢σ = ⊢Λ (_⊢⋯ˢ_ {σ = σ ↑ˢ _} d (⊢↑ˢ {σ = σ} ⊢σ _))
_⊢⋯ˢ_ {σ = σ} (⊢· d₁ d₂) ⊢σ =
  ⊢· (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} (⊢• d₁ d₂) ⊢σ =
  ⊢• (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)
_⊢⋯ˢ_ {σ = σ} (⊢rcd d) ⊢σ = ⊢rcd (_⊢⋯ˢᴱ_ {σ = σ} d ⊢σ)
_⊢⋯ˢ_ {σ = σ} (⊢# d h) ⊢σ = ⊢# (_⊢⋯ˢ_ {σ = σ} d ⊢σ) (Has-sub {σ = σ} h)
_⊢⋯ˢ_ {σ = σ} (⊢<: d₁ d₂) ⊢σ =
  ⊢<: (_⊢⋯ˢ_ {σ = σ} d₁ ⊢σ) (_⊢⋯ˢ_ {σ = σ} d₂ ⊢σ)

_⊢⋯ˢᴿ_ {σ = σ} <:ᴿ-nil  ⊢σ = <:ᴿ-nil
_⊢⋯ˢᴿ_ {σ = σ} <:ᴿ-refl ⊢σ = <:ᴿ-refl
_⊢⋯ˢᴿ_ {σ = σ} (<:ᴿ-cons h d r) ⊢σ =
  <:ᴿ-cons (Has-sub {σ = σ} h) (_⊢⋯ˢ_ {σ = σ} d ⊢σ) (_⊢⋯ˢᴿ_ {σ = σ} r ⊢σ)

_⊢⋯ˢᴱ_ {σ = σ} ⊢ᴿ-nil ⊢σ = ⊢ᴿ-nil
_⊢⋯ˢᴱ_ {σ = σ} (⊢ᴿ-cons d ds) ⊢σ =
  ⊢ᴿ-cons (_⊢⋯ˢ_ {σ = σ} d ⊢σ) (_⊢⋯ˢᴱ_ {σ = σ} ds ⊢σ)

⊢[] : ∀ {Γ : Ctx S} {t : S ⊢ s} {A : S ∶⊢ s} →
  Γ ⊢ t ∶ A → (t ∙ˢ idˢ) ∶ (A ∷ₜ Γ) →ˢ Γ
⊢[] d _ zero    _ refl = d
⊢[] d _ (suc x) _ refl = ⊢var refl

-- ═══ part 2B (record fragment): preservation and progress ═══════════

data Val    : S ⊢ expr → Set
data ValsᴿE : S ⊢ rexpr → Set

data Val where
  vλ   : Val (λx[ A ] e)
  vΛ   : Val (Λα[<: A ] e)
  vrcd : ValsᴿE re → Val (RcdE re)

data ValsᴿE where
  vnil  : ValsᴿE (nilE {S = S})
  vcons : Val e → ValsᴿE re → ValsᴿE (consE l e re)

infix 3 _↪_ _↪ᴿ_
data _↪_  : S ⊢ expr → S ⊢ expr → Set
data _↪ᴿ_ : S ⊢ rexpr → S ⊢ rexpr → Set

data _↪_ where
  β-λ    : Val e₂ → ((λx[ A ] e₁) · e₂) ↪ (e₁ [ e₂ ]₀)
  β-Λ    : ((Λα[<: A ] e) • C) ↪ (e [ C ]₀)
  β-#    : ∀ {re : S ⊢ rexpr} {l e} → ValsᴿE re → HasE re l e → ((RcdE re) # l) ↪ e
  ξ-·₁   : e₁ ↪ e → (e₁ · e₂) ↪ (e · e₂)
  ξ-·₂   : Val e₁ → e₂ ↪ e → (e₁ · e₂) ↪ (e₁ · e)
  ξ-•    : e ↪ e′ → (e • C) ↪ (e′ • C)
  ξ-#    : e ↪ e′ → (e # l) ↪ (e′ # l)
  ξ-rcd  : re₁ ↪ᴿ re₂ → (RcdE re₁) ↪ (RcdE re₂)

-- E-Ctx for the record context {lᵢ=vᵢ, lⱼ=E, lₖ=tₖ}: the fields before
-- the hole must already be values
data _↪ᴿ_ where
  ξ-here : e ↪ e′ → (consE l e re) ↪ᴿ (consE l e′ re)
  ξ-tail : Val e → re₁ ↪ᴿ re₂ → (consE l e re₁) ↪ᴿ (consE l e re₂)

-- inversion, with the subtyping step built in
inv-λ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (λx[ A ] e) ∶ C → Γ ⊢ C <: (B₁ ⇒ B₂) →
  (Γ ⊢ B₁ <: A) × ((A ∷ₜ Γ) ⊢ e ∶ weaken B₂)
inv-λ (⊢λ d)    (<:-⇒ s₁ s₂) = s₁ , ⊢<: d (⊢weaken _ s₂)
inv-λ (⊢<: d s) sub          = inv-λ d (transitivity s sub)

inv-Λ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (Λα[<: A ] e) ∶ C → Γ ⊢ C <: (∀[<: B₁ ] B₂) →
  (Γ ⊢ B₁ <: A) × ((B₁ ∷ₜ Γ) ⊢ e ∶ B₂)
inv-Λ (⊢Λ d)    (<:-∀ s₁ s₂) = s₁ , ⊢<: (narrowing s₁ d) s₂
inv-Λ (⊢<: d s) sub          = inv-Λ d (transitivity s sub)

-- inversion for records: if a record value has a record type, then for
-- every field of that type there is a correspondingly-typed field in
-- the term
inv-rcd : ∀ {Γ : Ctx S} {re C rt l B} →
  Γ ⊢ (RcdE re) ∶ C → Γ ⊢ C <: (RcdT rt) → Has rt l B →
  Σ[ e ∈ S ⊢ expr ] (HasE re l e × Γ ⊢ e ∶ B)
inv-rcdᴱ : ∀ {Γ : Ctx S} {re rt l B} →
  Γ ⊢ re ∶ᴿ rt → Has rt l B → Σ[ e ∈ S ⊢ expr ] (HasE re l e × Γ ⊢ e ∶ B)
inv-rcdᴱ (⊢ᴿ-cons d ds) here      = _ , hereE , d
inv-rcdᴱ (⊢ᴿ-cons d ds) (there ne h) with inv-rcdᴱ ds h
... | (e , m , de) = e , thereE ne m , de
inv-rcd (⊢rcd d) (<:-rcd r) h with <:ᴿ-inv r h
... | (A , h′ , sub) with inv-rcdᴱ d h′
...   | (e , m , de) = e , m , ⊢<: de sub
inv-rcd (⊢<: d s) sub h = inv-rcd d (transitivity s sub) h

-- ─── preservation ───────────────────────────────────────────────────

preservation  : ∀ {Γ : Ctx S} {e e′ : S ⊢ expr} {A} →
  Γ ⊢ e ∶ A → e ↪ e′ → Γ ⊢ e′ ∶ A
preservationᴿ : ∀ {Γ : Ctx S} {re re′ : S ⊢ rexpr} {rt} →
  Γ ⊢ re ∶ᴿ rt → re ↪ᴿ re′ → Γ ⊢ re′ ∶ᴿ rt

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
preservation (⊢rcd d) (ξ-rcd st) = ⊢rcd (preservationᴿ d st)
preservation (⊢# d h) (β-# vs m) with inv-rcd d (<:-reflexive _) h
... | (e , m′ , de) = subst (λ z → _ ⊢ z ∶ _) (HasE-unique m′ m) de
preservation (⊢# d h) (ξ-# st) = ⊢# (preservation d st) h
preservation (⊢<: d s) st      = ⊢<: (preservation d st) s

preservationᴿ (⊢ᴿ-cons d ds) (ξ-here st)   = ⊢ᴿ-cons (preservation d st) ds
preservationᴿ (⊢ᴿ-cons d ds) (ξ-tail v st) = ⊢ᴿ-cons d (preservationᴿ ds st)

-- ─── progress ───────────────────────────────────────────────────────

data Progress {S} (e : S ⊢ expr) : Set where
  step : ∀ {e′ : S ⊢ expr} → e ↪ e′ → Progress e
  done : Val e → Progress e

data ProgressᴿE {S} (re : S ⊢ rexpr) : Set where
  stepᴿ : ∀ {re′ : S ⊢ rexpr} → re ↪ᴿ re′ → ProgressᴿE re
  doneᴿ : ValsᴿE re → ProgressᴿE re

-- canonical forms, by matching on the value
not-Λ-⇒ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (Λα[<: A ] e) ∶ C → Γ ⊢ C <: (B₁ ⇒ B₂) → ⊥
not-Λ-⇒ (⊢Λ d)    ()
not-Λ-⇒ (⊢<: d s) sub = not-Λ-⇒ d (transitivity s sub)

not-rcd-⇒ : ∀ {Γ : Ctx S} {re C B₁ B₂} →
  Γ ⊢ (RcdE re) ∶ C → Γ ⊢ C <: (B₁ ⇒ B₂) → ⊥
not-rcd-⇒ (⊢rcd d)  ()
not-rcd-⇒ (⊢<: d s) sub = not-rcd-⇒ d (transitivity s sub)

not-λ-∀ : ∀ {Γ : Ctx S} {A e C B₁ B₂} →
  Γ ⊢ (λx[ A ] e) ∶ C → Γ ⊢ C <: (∀[<: B₁ ] B₂) → ⊥
not-λ-∀ (⊢λ d)    ()
not-λ-∀ (⊢<: d s) sub = not-λ-∀ d (transitivity s sub)

not-rcd-∀ : ∀ {Γ : Ctx S} {re C B₁ B₂} →
  Γ ⊢ (RcdE re) ∶ C → Γ ⊢ C <: (∀[<: B₁ ] B₂) → ⊥
not-rcd-∀ (⊢rcd d)  ()
not-rcd-∀ (⊢<: d s) sub = not-rcd-∀ d (transitivity s sub)

not-λ-rcd : ∀ {Γ : Ctx S} {A e C rt} →
  Γ ⊢ (λx[ A ] e) ∶ C → Γ ⊢ C <: (RcdT rt) → ⊥
not-λ-rcd (⊢λ d)    ()
not-λ-rcd (⊢<: d s) sub = not-λ-rcd d (transitivity s sub)

not-Λ-rcd : ∀ {Γ : Ctx S} {A e C rt} →
  Γ ⊢ (Λα[<: A ] e) ∶ C → Γ ⊢ C <: (RcdT rt) → ⊥
not-Λ-rcd (⊢Λ d)    ()
not-Λ-rcd (⊢<: d s) sub = not-Λ-rcd d (transitivity s sub)

app-step : ∀ {Γ : Ctx S} {e₁ e₂ : S ⊢ expr} {A B} →
  Γ ⊢ e₁ ∶ (A ⇒ B) → Val e₁ → Val e₂ → Progress (e₁ · e₂)
app-step d vλ       v₂ = step (β-λ v₂)
app-step d vΛ       v₂ = ⊥-elim (not-Λ-⇒ d (<:-reflexive _))
app-step d (vrcd _) v₂ = ⊥-elim (not-rcd-⇒ d (<:-reflexive _))

tapp-step : ∀ {Γ : Ctx S} {e : S ⊢ expr} {A B C} →
  Γ ⊢ e ∶ (∀[<: A ] B) → Val e → Progress (e • C)
tapp-step d vλ       = ⊥-elim (not-λ-∀ d (<:-reflexive _))
tapp-step d vΛ       = step β-Λ
tapp-step d (vrcd _) = ⊥-elim (not-rcd-∀ d (<:-reflexive _))

proj-step : ∀ {Γ : Ctx S} {e : S ⊢ expr} {rt l A} →
  Γ ⊢ e ∶ (RcdT rt) → Has rt l A → Val e → Progress (e # l)
proj-step d h vλ       = ⊥-elim (not-λ-rcd d (<:-reflexive _))
proj-step d h vΛ       = ⊥-elim (not-Λ-rcd d (<:-reflexive _))
proj-step d h (vrcd vs) with inv-rcd d (<:-reflexive _) h
... | (e , m , de) = step (β-# vs m)

progress  : ∀ {Γ : Ctx []} {e : [] ⊢ expr} {A} → Γ ⊢ e ∶ A → Progress e
progressᴿ : ∀ {Γ : Ctx []} {re : [] ⊢ rexpr} {rt} → Γ ⊢ re ∶ᴿ rt → ProgressᴿE re

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
progress (⊢rcd d) with progressᴿ d
... | stepᴿ st = step (ξ-rcd st)
... | doneᴿ vs = done (vrcd vs)
progress (⊢# d h) with progress d
... | step st = step (ξ-# st)
... | done v  = proj-step d h v
progress (⊢<: d _) = progress d

progressᴿ ⊢ᴿ-nil = doneᴿ vnil
progressᴿ (⊢ᴿ-cons d ds) with progress d
... | step st = stepᴿ (ξ-here st)
... | done v with progressᴿ ds
...   | stepᴿ st = stepᴿ (ξ-tail v st)
...   | doneᴿ vs = doneᴿ (vcons v vs)

-- ═══ narrowing with A trailing ∆, challenge Lemma 3.2 in full ══════

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

size-wk-tele : ∀ {S S′} (Δ : Tele S S′) (A : S ⊢ type) →
  size (wk-tele Δ A) ≡ size A
size-wk-tele []      A = refl
size-wk-tele (B ◂ Δ) A =
  ≡-trans (size-ren (wk-tele Δ A) (wkᴿ _)) (size-wk-tele Δ A)

-- 3.2 Lemma [Narrowing], with records
narrowing∆ : ∀ {S S′} {Γ : Ctx S} {P Q : S ⊢ type} (Δ : Tele (type ∷ S) S′)
  {t : S′ ⊢ s} {A : S′ ∶⊢ s} →
  Γ ⊢ P <: Q → (Δ ▸ (Q ∷ₜ Γ)) ⊢ t ∶ A → (Δ ▸ (P ∷ₜ Γ)) ⊢ t ∶ A
narrowing∆ {Q = Q} Δ d =
  narrow (size Q)
    (subst (_≤ size Q)
      (sym (≡-trans (size-wk-tele Δ (weaken Q)) (size-ren Q (wkᴿ type))))
      ≤-refl)
    (narrow-tele Δ (narrow-here d))

narrowing′ : ∀ {Γ : Ctx S} {P Q : S ⊢ type} {t : (type ∷ S) ⊢ s} {A} →
  Γ ⊢ P <: Q → (Q ∷ₜ Γ) ⊢ t ∶ A → (P ∷ₜ Γ) ⊢ t ∶ A
narrowing′ = narrowing∆ []

-- ═══ eliminating the primitive reflexivity rule ═════════════════════
-- `_⊢_<:ᴿ°_` is sa-Rcd exactly: the two rules of the challenge, with no
-- reflexivity rule.  Below: (i) `<:ᴿ-refl` is not admissible in
-- general, and the mode-merged family is what forces that; (ii) it is
-- eliminable at every well-formed record body, literal and
-- distinct-labelled, i.e. every record type the challenge's syntax
-- denotes; (iii) hence transitivity transfers to sa-Rcd proper.

infix 3 _⊢_<:ᴿ°_
data _⊢_<:ᴿ°_ {S} (Γ : Ctx S) : S ⊢ rtype → S ⊢ rtype → Set where
  °nil  : ∀ {rt} → Γ ⊢ rt <:ᴿ° nilT
  °cons : ∀ {rt₁ rt₂ l A B} →
    Has rt₁ l A → Γ ⊢ A ∶ B → Γ ⊢ rt₁ <:ᴿ° rt₂ → Γ ⊢ rt₁ <:ᴿ° (consT l B rt₂)

-- (i) non-admissibility.  At a record body that is a variable, a form
-- F<: does not have, but the mode-merged family `_⊢[_]_` admits at
-- every sort, the only derivation is `<:ᴿ-refl`.  So the rule cannot
-- be dropped outright; it can only be eliminated where the record body
-- is literal, which is (ii).
<:ᴿ-var-forces-refl : ∀ {Γ : Ctx S} {rt} {x : S ∋ rtype} →
  Γ ⊢ rt <:ᴿ (` x) → rt ≡ (` x)
<:ᴿ-var-forces-refl <:ᴿ-refl = refl

-- well-formedness of a record body: nil-terminated with distinct labels
data NotIn {S} (l : Label) : S ⊢ rtype → Set where
  ni-nil  : NotIn l nilT
  ni-cons : ∀ {l′ A rt} → l ≢ l′ → NotIn l rt → NotIn l (consT l′ A rt)

data WfR {S} : S ⊢ rtype → Set where
  wf-nil  : WfR nilT
  wf-cons : ∀ {l A rt} → NotIn l rt → WfR rt → WfR (consT l A rt)

notin-≢ : ∀ {S} {rt : S ⊢ rtype} {l l′ A} → NotIn l rt → Has rt l′ A → l′ ≢ l
notin-≢ (ni-cons ne ni) here        = λ eq → ne (sym eq)
notin-≢ (ni-cons ne ni) (there _ h) = notin-≢ ni h

-- (ii) reflexivity is derivable in sa-Rcd proper, for well-formed bodies
refl° : ∀ {Γ : Ctx S} (rt : S ⊢ rtype) {rs : S ⊢ rtype} →
  (∀ {l A} → Has rt l A → Has rs l A) → WfR rt → Γ ⊢ rs <:ᴿ° rt
refl° nilT           inc wf-nil          = °nil
refl° (consT l A rt) inc (wf-cons ni w)  =
  °cons (inc here) (<:-reflexive A)
        (refl° rt (λ h → inc (there (notin-≢ ni h) h)) w)

°→ : ∀ {Γ : Ctx S} {rt₁ rt₂} → Γ ⊢ rt₁ <:ᴿ° rt₂ → Γ ⊢ rt₁ <:ᴿ rt₂
°→ °nil          = <:ᴿ-nil
°→ (°cons h d r) = <:ᴿ-cons h d (°→ r)

-- the elimination: every derivation of my relation at a well-formed
-- record body is matched by an sa-Rcd derivation
→° : ∀ {Γ : Ctx S} {rt₁ rt₂} → WfR rt₂ → Γ ⊢ rt₁ <:ᴿ rt₂ → Γ ⊢ rt₁ <:ᴿ° rt₂
→° w              <:ᴿ-nil          = °nil
→° (wf-cons ni w) (<:ᴿ-cons h d r) = °cons h d (→° w r)
→° w              <:ᴿ-refl         = refl° _ (λ h → h) w

-- (iii) transitivity for sa-Rcd proper, no reflexivity rule involved
-- in the statement, at either end
transitivityᴿ° : ∀ {Γ : Ctx S} {rs rq rt : S ⊢ rtype} → WfR rt →
  Γ ⊢ rs <:ᴿ° rq → Γ ⊢ rq <:ᴿ° rt → Γ ⊢ rs <:ᴿ° rt
transitivityᴿ° {rq = rq} w d₁ d₂ =
  →° w (<:-transᴿ (sizeR rq) ≤-refl (°→ d₁) (°→ d₂))

-- ═══ A fully reflexivity-free subtyping system ══════════════════════
-- `_⊢_<:ᶜ_` is the challenge's algorithmic subtyping with records,
-- verbatim: sa-Top, sa-Refl-TVar, sa-Trans-TVar, sa-Arrow, sa-All,
-- sa-Rcd.  There is no reflexivity rule anywhere in it -- neither at
-- the record level (which `<:ᴿ-refl` supplied) nor nested inside the
-- type-level premises.  Below: it embeds into `_⊢_<:_`, and on
-- well-formed types the embedding is surjective, so transitivity
-- transfers to the challenge's relation exactly.

-- type-level well-formedness: no record-body variables, distinct labels
data Wf   {S} : S ⊢ type  → Set
data WfRᶠ {S} : S ⊢ rtype → Set
data Wf {S} where
  wf-top : Wf (Top {S = S})
  wf-var : ∀ {α : S ∋ type} → Wf (` α)
  wf-⇒   : ∀ {A B} → Wf A → Wf B → Wf (A ⇒ B)
  wf-∀   : ∀ {A B} → Wf A → Wf B → Wf (∀[<: A ] B)
  wf-rcd : ∀ {rt} → WfRᶠ rt → Wf (RcdT rt)
data WfRᶠ {S} where
  wfr-nil  : WfRᶠ (nilT {S = S})
  wfr-cons : ∀ {l A rt} → NotIn l rt → Wf A → WfRᶠ rt → WfRᶠ (consT l A rt)

WfRᶠ→WfR : ∀ {S} {rt : S ⊢ rtype} → WfRᶠ rt → WfR rt
WfRᶠ→WfR wfr-nil            = wf-nil
WfRᶠ→WfR (wfr-cons ni w ws) = wf-cons ni (WfRᶠ→WfR ws)

Wf-Has : ∀ {S} {rt : S ⊢ rtype} {l A} → WfRᶠ rt → Has rt l A → Wf A
Wf-Has (wfr-cons ni w ws) here          = w
Wf-Has (wfr-cons ni w ws) (there ne h)  = Wf-Has ws h

NotIn-renᶠ : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} {l} (ξ : S₁ →ᴿ S₂) →
  NotIn l rt → NotIn l (rt [ ξ ]ᴿ)
NotIn-renᶠ ξ ni-nil          = ni-nil
NotIn-renᶠ ξ (ni-cons ne ni) = ni-cons ne (NotIn-renᶠ ξ ni)

Wf-ren   : ∀ {S₁ S₂} {A : S₁ ⊢ type} (ξ : S₁ →ᴿ S₂) → Wf A → Wf (A [ ξ ]ᴿ)
WfRᶠ-ren : ∀ {S₁ S₂} {rt : S₁ ⊢ rtype} (ξ : S₁ →ᴿ S₂) → WfRᶠ rt → WfRᶠ (rt [ ξ ]ᴿ)
Wf-ren ξ wf-top        = wf-top
Wf-ren ξ wf-var        = wf-var
Wf-ren ξ (wf-⇒ v w)    = wf-⇒ (Wf-ren ξ v) (Wf-ren ξ w)
Wf-ren ξ (wf-∀ v w)    = wf-∀ (Wf-ren ξ v) (Wf-ren (ξ ↑ᴿ type) w)
Wf-ren ξ (wf-rcd ws)   = wf-rcd (WfRᶠ-ren ξ ws)
WfRᶠ-ren ξ wfr-nil            = wfr-nil
WfRᶠ-ren ξ (wfr-cons ni w ws) =
  wfr-cons (NotIn-renᶠ ξ ni) (Wf-ren ξ w) (WfRᶠ-ren ξ ws)

WfCtx : ∀ {S} → Ctx S → Set
WfCtx {S} Γ = ∀ s (x : S ∋ s) → Wf (wk-telescope Γ x)

WfCtx-ext : ∀ {S s} {Γ : Ctx S} {A : S ∶⊢ s} →
  WfCtx Γ → Wf A → WfCtx (_∷ₜ_ {s = s} A Γ)
WfCtx-ext wfΓ w _ zero    = Wf-ren (wkᴿ _) w
WfCtx-ext wfΓ w _ (suc x) = Wf-ren (wkᴿ _) (wfΓ _ x)

-- ─── the challenge's system, with no reflexivity rule ───────────────
infix 3 _⊢_<:ᶜ_ _⊢_<:ᴿᶜ_
data _⊢_<:ᶜ_  {S} (Γ : Ctx S) : S ⊢ type  → S ⊢ type  → Set
data _⊢_<:ᴿᶜ_ {S} (Γ : Ctx S) : S ⊢ rtype → S ⊢ rtype → Set

data _⊢_<:ᶜ_ {S} Γ where
  c-top  : ∀ {A} → Γ ⊢ A <:ᶜ Top                              -- sa-Top
  c-refl : ∀ {α : S ∋ type} → Γ ⊢ (` α) <:ᶜ (` α)             -- sa-Refl-TVar
  c-var  : ∀ {α : S ∋ type} {U B} →                           -- sa-Trans-TVar
           Γ ∋ α ∶ U → Γ ⊢ U <:ᶜ B → Γ ⊢ (` α) <:ᶜ B
  c-⇒    : ∀ {A₁ A₂ B₁ B₂} → Γ ⊢ B₁ <:ᶜ A₁ → Γ ⊢ A₂ <:ᶜ B₂ →  -- sa-Arrow
           Γ ⊢ (A₁ ⇒ A₂) <:ᶜ (B₁ ⇒ B₂)
  c-∀    : ∀ {A₁ A₂ B₁ B₂} → Γ ⊢ B₁ <:ᶜ A₁ →                  -- sa-All
           (B₁ ∷ₜ Γ) ⊢ A₂ <:ᶜ B₂ → Γ ⊢ (∀[<: A₁ ] A₂) <:ᶜ (∀[<: B₁ ] B₂)
  c-rcd  : ∀ {rt₁ rt₂} → Γ ⊢ rt₁ <:ᴿᶜ rt₂ →                   -- sa-Rcd
           Γ ⊢ (RcdT rt₁) <:ᶜ (RcdT rt₂)

data _⊢_<:ᴿᶜ_ {S} Γ where
  cᴿ-nil  : ∀ {rt} → Γ ⊢ rt <:ᴿᶜ nilT
  cᴿ-cons : ∀ {rt₁ rt₂ l A B} → Has rt₁ l A → Γ ⊢ A <:ᶜ B →
            Γ ⊢ rt₁ <:ᴿᶜ rt₂ → Γ ⊢ rt₁ <:ᴿᶜ (consT l B rt₂)

-- reflexivity is derivable in it, for well-formed types
reflᶜ  : ∀ {S} {Γ : Ctx S} {A : S ⊢ type} → Wf A → Γ ⊢ A <:ᶜ A
reflᴿᶜ : ∀ {S} {Γ : Ctx S} (rt : S ⊢ rtype) {rs : S ⊢ rtype} →
  (∀ {l A} → Has rt l A → Has rs l A) → WfRᶠ rt → Γ ⊢ rs <:ᴿᶜ rt
reflᶜ wf-top      = c-top
reflᶜ wf-var      = c-refl
reflᶜ (wf-⇒ v w)  = c-⇒ (reflᶜ v) (reflᶜ w)
reflᶜ (wf-∀ v w)  = c-∀ (reflᶜ v) (reflᶜ w)
reflᶜ (wf-rcd ws) = c-rcd (reflᴿᶜ _ (λ h → h) ws)
reflᴿᶜ nilT           inc wfr-nil            = cᴿ-nil
reflᴿᶜ (consT l A rt) inc (wfr-cons ni w ws) =
  cᴿ-cons (inc here) (reflᶜ w)
          (reflᴿᶜ rt (λ h → inc (there (notin-≢ ni h) h)) ws)

-- ─── the two directions ─────────────────────────────────────────────
ᶜ→  : ∀ {S} {Γ : Ctx S} {A B : S ⊢ type} → Γ ⊢ A <:ᶜ B → Γ ⊢ A <: B
ᶜᴿ→ : ∀ {S} {Γ : Ctx S} {rt₁ rt₂ : S ⊢ rtype} → Γ ⊢ rt₁ <:ᴿᶜ rt₂ → Γ ⊢ rt₁ <:ᴿ rt₂
ᶜ→ c-top          = <:-top
ᶜ→ c-refl         = <:-refl
ᶜ→ (c-var eq u)   = <:-var eq (ᶜ→ u)
ᶜ→ (c-⇒ d₁ d₂)    = <:-⇒ (ᶜ→ d₁) (ᶜ→ d₂)
ᶜ→ (c-∀ d₁ d₂)    = <:-∀ (ᶜ→ d₁) (ᶜ→ d₂)
ᶜ→ (c-rcd r)      = <:-rcd (ᶜᴿ→ r)
ᶜᴿ→ cᴿ-nil            = <:ᴿ-nil
ᶜᴿ→ (cᴿ-cons h d r)   = <:ᴿ-cons h (ᶜ→ d) (ᶜᴿ→ r)

→ᶜ  : ∀ {S} {Γ : Ctx S} {A B : S ⊢ type} →
  WfCtx Γ → Wf A → Wf B → Γ ⊢ A <: B → Γ ⊢ A <:ᶜ B
→ᴿᶜ : ∀ {S} {Γ : Ctx S} {rt₁ rt₂ : S ⊢ rtype} →
  WfCtx Γ → WfRᶠ rt₁ → WfRᶠ rt₂ → Γ ⊢ rt₁ <:ᴿ rt₂ → Γ ⊢ rt₁ <:ᴿᶜ rt₂
→ᶜ wfΓ v w <:-top           = c-top
→ᶜ wfΓ v w <:-refl          = c-refl
→ᶜ wfΓ v w (<:-var {α = α} eq u) =
  c-var eq (→ᶜ wfΓ (subst Wf eq (wfΓ _ α)) w u)
→ᶜ wfΓ (wf-⇒ v₁ v₂) (wf-⇒ w₁ w₂) (<:-⇒ d₁ d₂) =
  c-⇒ (→ᶜ wfΓ w₁ v₁ d₁) (→ᶜ wfΓ v₂ w₂ d₂)
→ᶜ wfΓ (wf-∀ v₁ v₂) (wf-∀ w₁ w₂) (<:-∀ d₁ d₂) =
  c-∀ (→ᶜ wfΓ w₁ v₁ d₁) (→ᶜ (WfCtx-ext wfΓ w₁) v₂ w₂ d₂)
→ᶜ wfΓ (wf-rcd vs) (wf-rcd ws) (<:-rcd r) = c-rcd (→ᴿᶜ wfΓ vs ws r)
→ᴿᶜ wfΓ vs ws <:ᴿ-nil  = cᴿ-nil
→ᴿᶜ wfΓ vs ws <:ᴿ-refl = reflᴿᶜ _ (λ h → h) ws
→ᴿᶜ wfΓ vs (wfr-cons ni w ws) (<:ᴿ-cons h d r) =
  cᴿ-cons h (→ᶜ wfΓ (Wf-Has vs h) w d) (→ᴿᶜ wfΓ vs ws r)

-- ─── 3.1 for the challenge's relation, no reflexivity rule at all ───
lemma-3-1-transitivity-challenge : ∀ {S} {Γ : Ctx S} {A Q B : S ⊢ type} →
  WfCtx Γ → Wf A → Wf Q → Wf B →
  Γ ⊢ A <:ᶜ Q → Γ ⊢ Q <:ᶜ B → Γ ⊢ A <:ᶜ B
lemma-3-1-transitivity-challenge wfΓ v u w d₁ d₂ =
  →ᶜ wfΓ v w (transitivity (ᶜ→ d₁) (ᶜ→ d₂))

-- ═══ challenge-referencing names (Part 1B) ══════════════════════════

-- 3.1 Lemma [Transitivity], with record types
lemma-3-1-transitivity : ∀ {Γ : Ctx S} {A Q B : S ⊢ type} →
  Γ ⊢ A <: Q → Γ ⊢ Q <: B → Γ ⊢ A <: B
lemma-3-1-transitivity = transitivity

-- 3.1 again, for sa-Rcd proper (no reflexivity rule in the statement)
lemma-3-1-transitivity-SA-Rcd : ∀ {Γ : Ctx S} {rs rq rt : S ⊢ rtype} →
  WfR rt → Γ ⊢ rs <:ᴿ° rq → Γ ⊢ rq <:ᴿ° rt → Γ ⊢ rs <:ᴿ° rt
lemma-3-1-transitivity-SA-Rcd = transitivityᴿ°

-- 3.2 Lemma [Narrowing], with record types and the trailing ∆
lemma-3-2-narrowing : ∀ {S S′} {Γ : Ctx S} {P Q : S ⊢ type}
  (Δ : Tele (type ∷ S) S′) {t : S′ ⊢ s} {A : S′ ∶⊢ s} →
  Γ ⊢ P <: Q → (Δ ▸ (Q ∷ₜ Γ)) ⊢ t ∶ A → (Δ ▸ (P ∷ₜ Γ)) ⊢ t ∶ A
lemma-3-2-narrowing = narrowing∆
