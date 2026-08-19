{-# OPTIONS --rewriting --local-confluence-check #-}

-- ═══ POPLmark Challenge, Part 3 ═════════════════════════════════════
--   "Testing and Animating with Respect to the Semantics"
--
--   1. Given F<: terms t and t′, decide whether t ⟶ t′.
--   2. Given t and t′, decide whether t ⟶* t′ ↛.
--   3. Given t, find t′ such that t ⟶ t′.
--
-- Task 3 is `reduct`.  Task 1 is `_↪?_`, a REAL decision procedure:
-- `Dec (e ↪ e′)` for arbitrary e, e′.  Task 2 is `evalDec`, decidable
-- up to a fuel bound.
--
-- The three ingredients, in order of depth:
--
--   * `stp⁺ : (e : S ⊢ expr) → Dec (Σ[ e′ ] (e ↪ e′))` — a step function
--     that is sound AND complete by construction: its `no` branch is a
--     proof that NOTHING steps.
--   * `_≟_ : (t u : S ⊢ s) → Dec (t ≡ u)` — decidable equality on the
--     intrinsically scoped, multi-sorted syntax, 89 clauses.
--   * `determinism : e ↪ e₁ → e ↪ e₂ → e₁ ≡ e₂`.
--
-- Decidable equality alone is *necessary but not sufficient*: without
-- determinism, `stp⁺ e = yes (e″ , _)` and `e″ ≢ e′` would not refute
-- `e ↪ e′`.  Determinism is what makes `stp⁺` complete for the whole
-- relation rather than for one reduction strategy.
--
-- The other question Part 3 asks is whether a term can COMPUTE at all:
-- `_[_]₀` unfolds to `_[ _ ∙ˢ idˢ ]ˢ` whose symbols are all `opaque`, so
-- no β-contraction can happen by unfolding — every one is performed by
-- the REWRITE SYSTEM.  Each `refl` below is Agda running the semantics.

module Challenge.Animation where

open import Languages.FsubRecords
open import Challenge.Records

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

-- Bool views of a decision, used by the test suite
isYes : ∀ {P : Set} → Dec P → Bool
isYes (yes _) = true
isYes (no  _) = false

isJustYes : ∀ {P : Set} → Maybe (Dec P) → Bool
isJustYes (just d) = isYes d
isJustYes nothing  = false

f≢t : false ≡ true → ⊥
f≢t ()

-- ─── decidable equality on variables ────────────────────────────────

infix 4 _≟∋_ _≟_

_≟∋_ : ∀ {S s} (x y : S ∋ s) → Dec (x ≡ y)
zero  ≟∋ zero  = yes refl
zero  ≟∋ suc y = no λ ()
suc x ≟∋ zero  = no λ ()
suc x ≟∋ suc y with x ≟∋ y
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }

-- ─── decidable equality on terms, all four sorts at once ────────────
-- 89 clauses.  The O(n²) off-diagonal is `no λ ()` throughout: two
-- constructors of different sorts never even form a clause, because the
-- sort index rules the split out.

_≟_ : ∀ {S s} (t u : S ⊢ s) → Dec (t ≡ u)
(` x) ≟ (` y) with x ≟∋ y
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
Top ≟ (` y) = no λ ()
(` x) ≟ Top = no λ ()
(A ⇒ B) ≟ (` y) = no λ ()
(` x) ≟ (A′ ⇒ B′) = no λ ()
(∀[<: A ] B) ≟ (` y) = no λ ()
(` x) ≟ (∀[<: A′ ] B′) = no λ ()
(RcdT rt) ≟ (` y) = no λ ()
(` x) ≟ (RcdT rt′) = no λ ()
Top ≟ Top = yes refl
Top ≟ (A′ ⇒ B′) = no λ ()
Top ≟ (∀[<: A′ ] B′) = no λ ()
Top ≟ (RcdT rt′) = no λ ()
(A ⇒ B) ≟ Top = no λ ()
(A ⇒ B) ≟ (A′ ⇒ B′) with A ≟ A′ | B ≟ B′
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
(A ⇒ B) ≟ (∀[<: A′ ] B′) = no λ ()
(A ⇒ B) ≟ (RcdT rt′) = no λ ()
(∀[<: A ] B) ≟ Top = no λ ()
(∀[<: A ] B) ≟ (A′ ⇒ B′) = no λ ()
(∀[<: A ] B) ≟ (∀[<: A′ ] B′) with A ≟ A′ | B ≟ B′
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
(∀[<: A ] B) ≟ (RcdT rt′) = no λ ()
(RcdT rt) ≟ Top = no λ ()
(RcdT rt) ≟ (A′ ⇒ B′) = no λ ()
(RcdT rt) ≟ (∀[<: A′ ] B′) = no λ ()
(RcdT rt) ≟ (RcdT rt′) with rt ≟ rt′
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
nilT ≟ (` y) = no λ ()
(` x) ≟ nilT = no λ ()
(consT l A rt) ≟ (` y) = no λ ()
(` x) ≟ (consT l′ A′ rt′) = no λ ()
nilT ≟ nilT = yes refl
nilT ≟ (consT l′ A′ rt′) = no λ ()
(consT l A rt) ≟ nilT = no λ ()
(consT l A rt) ≟ (consT l′ A′ rt′) with l ≟ℕ l′ | A ≟ A′ | rt ≟ rt′
... | yes refl | yes refl | yes refl = yes refl
... | no ¬p | _ | _ = no λ { refl → ¬p refl }
... | _ | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | _ | no ¬p = no λ { refl → ¬p refl }
(λx[ A ] e) ≟ (` y) = no λ ()
(` x) ≟ (λx[ A′ ] e′) = no λ ()
(Λα[<: A ] e) ≟ (` y) = no λ ()
(` x) ≟ (Λα[<: A′ ] e′) = no λ ()
(e · f) ≟ (` y) = no λ ()
(` x) ≟ (e′ · f′) = no λ ()
(e • C) ≟ (` y) = no λ ()
(` x) ≟ (e′ • C′) = no λ ()
(RcdE re) ≟ (` y) = no λ ()
(` x) ≟ (RcdE re′) = no λ ()
(e # l) ≟ (` y) = no λ ()
(` x) ≟ (e′ # l′) = no λ ()
(λx[ A ] e) ≟ (λx[ A′ ] e′) with A ≟ A′ | e ≟ e′
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
(λx[ A ] e) ≟ (Λα[<: A′ ] e′) = no λ ()
(λx[ A ] e) ≟ (e′ · f′) = no λ ()
(λx[ A ] e) ≟ (e′ • C′) = no λ ()
(λx[ A ] e) ≟ (RcdE re′) = no λ ()
(λx[ A ] e) ≟ (e′ # l′) = no λ ()
(Λα[<: A ] e) ≟ (λx[ A′ ] e′) = no λ ()
(Λα[<: A ] e) ≟ (Λα[<: A′ ] e′) with A ≟ A′ | e ≟ e′
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
(Λα[<: A ] e) ≟ (e′ · f′) = no λ ()
(Λα[<: A ] e) ≟ (e′ • C′) = no λ ()
(Λα[<: A ] e) ≟ (RcdE re′) = no λ ()
(Λα[<: A ] e) ≟ (e′ # l′) = no λ ()
(e · f) ≟ (λx[ A′ ] e′) = no λ ()
(e · f) ≟ (Λα[<: A′ ] e′) = no λ ()
(e · f) ≟ (e′ · f′) with e ≟ e′ | f ≟ f′
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
(e · f) ≟ (e′ • C′) = no λ ()
(e · f) ≟ (RcdE re′) = no λ ()
(e · f) ≟ (e′ # l′) = no λ ()
(e • C) ≟ (λx[ A′ ] e′) = no λ ()
(e • C) ≟ (Λα[<: A′ ] e′) = no λ ()
(e • C) ≟ (e′ · f′) = no λ ()
(e • C) ≟ (e′ • C′) with e ≟ e′ | C ≟ C′
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
(e • C) ≟ (RcdE re′) = no λ ()
(e • C) ≟ (e′ # l′) = no λ ()
(RcdE re) ≟ (λx[ A′ ] e′) = no λ ()
(RcdE re) ≟ (Λα[<: A′ ] e′) = no λ ()
(RcdE re) ≟ (e′ · f′) = no λ ()
(RcdE re) ≟ (e′ • C′) = no λ ()
(RcdE re) ≟ (RcdE re′) with re ≟ re′
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
(RcdE re) ≟ (e′ # l′) = no λ ()
(e # l) ≟ (λx[ A′ ] e′) = no λ ()
(e # l) ≟ (Λα[<: A′ ] e′) = no λ ()
(e # l) ≟ (e′ · f′) = no λ ()
(e # l) ≟ (e′ • C′) = no λ ()
(e # l) ≟ (RcdE re′) = no λ ()
(e # l) ≟ (e′ # l′) with e ≟ e′ | l ≟ℕ l′
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
nilE ≟ (` y) = no λ ()
(` x) ≟ nilE = no λ ()
(consE l e re) ≟ (` y) = no λ ()
(` x) ≟ (consE l′ e′ re′) = no λ ()
nilE ≟ nilE = yes refl
nilE ≟ (consE l′ e′ re′) = no λ ()
(consE l e re) ≟ nilE = no λ ()
(consE l e re) ≟ (consE l′ e′ re′) with l ≟ℕ l′ | e ≟ e′ | re ≟ re′
... | yes refl | yes refl | yes refl = yes refl
... | no ¬p | _ | _ = no λ { refl → ¬p refl }
... | _ | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | _ | no ¬p = no λ { refl → ¬p refl }


-- ─── the value test, as a decision ──────────────────────────────────

Val?  : (e  : S ⊢ expr)  → Dec (Val e)
Vals? : (re : S ⊢ rexpr) → Dec (ValsᴿE re)

Val? (` x)         = no λ ()
Val? (λx[ A ] e)   = yes vλ
Val? (Λα[<: A ] e) = yes vΛ
Val? (e₁ · e₂)     = no λ ()
Val? (e • C)       = no λ ()
Val? (e # l)       = no λ ()
Val? (RcdE re) with Vals? re
... | yes vs = yes (vrcd vs)
... | no ¬vs = no λ { (vrcd vs) → ¬vs vs }

Vals? (` x) = no λ ()
Vals? nilE  = yes vnil
Vals? (consE l e re) with Val? e | Vals? re
... | yes v | yes vs = yes (vcons v vs)
... | no ¬v | _      = no λ { (vcons v _)  → ¬v v }
... | _     | no ¬vs = no λ { (vcons _ vs) → ¬vs vs }

-- the Bool version kept, and shown to agree
val? : S ⊢ expr → Bool
val? e = isYes (Val? e)

val?-sound : ∀ (e : S ⊢ expr) → val? e ≡ true → Val e
val?-sound e eq with Val? e
... | yes v  = v
... | no  ¬v = ⊥-elim (f≢t eq)

-- ─── field lookup, as a decision ────────────────────────────────────

HasSome : ∀ {S} → S ⊢ rexpr → Label → Set
HasSome {S} re l = Σ[ e ∈ S ⊢ expr ] HasE re l e

lookupE? : ∀ {S} (l : Label) (re : S ⊢ rexpr) → Dec (HasSome re l)
lookupE? l (` x) = no λ { (_ , ()) }
lookupE? l nilE  = no λ { (_ , ()) }
lookupE? l (consE l′ e re) with l ≟ℕ l′
... | yes refl = yes (e , hereE)
... | no  ne with lookupE? l re
...   | yes (e′ , h) = yes (e′ , thereE ne h)
...   | no ¬h = no λ { (_ , hereE)       → ne refl
                     ; (_ , thereE _ h)  → ¬h (_ , h) }

-- the Maybe version, kept (`toMaybe` is defined below)

-- ─── the certified, COMPLETE step function ──────────────────────────
-- `Steps e` is the challenge's "t reduces"; `¬ Steps e` is "t is a
-- normal form".  `stp⁺` decides it.

Steps : ∀ {S} → S ⊢ expr → Set
Steps {S} e = Σ[ e′ ∈ S ⊢ expr ] (e ↪ e′)

Stepsᴿ : ∀ {S} → S ⊢ rexpr → Set
Stepsᴿ {S} re = Σ[ re′ ∈ S ⊢ rexpr ] (re ↪ᴿ re′)

NF : ∀ {S} → S ⊢ expr → Set
NF e = ¬ (Steps e)

-- one helper per elimination form, so that no `with` nests more than
-- two deep

app? : (e₁ e₂ : S ⊢ expr) → Dec (Steps e₁) → Dec (Steps e₂) → Dec (Steps (e₁ · e₂))
app? e₁ e₂ (yes (e₁′ , st)) _ = yes (e₁′ · e₂ , ξ-·₁ st)
app? e₁ e₂ (no ¬p) (yes (e₂′ , st)) with Val? e₁
... | yes v = yes (e₁ · e₂′ , ξ-·₂ v st)
... | no ¬v = no λ { (_ , β-λ _)      → ¬v vλ
                   ; (_ , ξ-·₁ st′)   → ¬p (_ , st′)
                   ; (_ , ξ-·₂ v _)   → ¬v v }
app? (λx[ A ] e₁) e₂ (no ¬p) (no ¬q) with Val? e₂
... | yes v = yes (e₁ [ e₂ ]₀ , β-λ v)
... | no ¬v = no λ { (_ , β-λ v)      → ¬v v
                   ; (_ , ξ-·₁ st)    → ¬p (_ , st)
                   ; (_ , ξ-·₂ _ st)  → ¬q (_ , st) }
app? (` x)         e₂ (no ¬p) (no ¬q) = no λ { (_ , ξ-·₁ st) → ¬p (_ , st) ; (_ , ξ-·₂ _ st) → ¬q (_ , st) }
app? (Λα[<: A ] e) e₂ (no ¬p) (no ¬q) = no λ { (_ , ξ-·₁ st) → ¬p (_ , st) ; (_ , ξ-·₂ _ st) → ¬q (_ , st) }
app? (e · e′)      e₂ (no ¬p) (no ¬q) = no λ { (_ , ξ-·₁ st) → ¬p (_ , st) ; (_ , ξ-·₂ _ st) → ¬q (_ , st) }
app? (e • C)       e₂ (no ¬p) (no ¬q) = no λ { (_ , ξ-·₁ st) → ¬p (_ , st) ; (_ , ξ-·₂ _ st) → ¬q (_ , st) }
app? (RcdE re)     e₂ (no ¬p) (no ¬q) = no λ { (_ , ξ-·₁ st) → ¬p (_ , st) ; (_ , ξ-·₂ _ st) → ¬q (_ , st) }
app? (e # l)       e₂ (no ¬p) (no ¬q) = no λ { (_ , ξ-·₁ st) → ¬p (_ , st) ; (_ , ξ-·₂ _ st) → ¬q (_ , st) }

tapp? : (e : S ⊢ expr) (C : S ⊢ type) → Dec (Steps e) → Dec (Steps (e • C))
tapp? e C (yes (e′ , st)) = yes (e′ • C , ξ-• st)
tapp? (Λα[<: A ] e) C (no ¬p) = yes (e [ C ]₀ , β-Λ)
tapp? (` x)        C (no ¬p) = no λ { (_ , ξ-• st) → ¬p (_ , st) }
tapp? (λx[ A ] e)  C (no ¬p) = no λ { (_ , ξ-• st) → ¬p (_ , st) }
tapp? (e · e′)     C (no ¬p) = no λ { (_ , ξ-• st) → ¬p (_ , st) }
tapp? (e • C′)     C (no ¬p) = no λ { (_ , ξ-• st) → ¬p (_ , st) }
tapp? (RcdE re)    C (no ¬p) = no λ { (_ , ξ-• st) → ¬p (_ , st) }
tapp? (e # l)      C (no ¬p) = no λ { (_ , ξ-• st) → ¬p (_ , st) }

proj? : (e : S ⊢ expr) (l : Label) → Dec (Steps e) → Dec (Steps (e # l))
proj? e l (yes (e′ , st)) = yes (e′ # l , ξ-# st)
proj? (RcdE re) l (no ¬p) with Vals? re
... | no ¬vs = no λ { (_ , β-# vs _) → ¬vs vs ; (_ , ξ-# st) → ¬p (_ , st) }
... | yes vs with lookupE? l re
...   | yes (e , h) = yes (e , β-# vs h)
...   | no ¬h = no λ { (_ , β-# _ h) → ¬h (_ , h) ; (_ , ξ-# st) → ¬p (_ , st) }
proj? (` x)         l (no ¬p) = no λ { (_ , ξ-# st) → ¬p (_ , st) }
proj? (λx[ A ] e)   l (no ¬p) = no λ { (_ , ξ-# st) → ¬p (_ , st) }
proj? (Λα[<: A ] e) l (no ¬p) = no λ { (_ , ξ-# st) → ¬p (_ , st) }
proj? (e · e′)      l (no ¬p) = no λ { (_ , ξ-# st) → ¬p (_ , st) }
proj? (e • C)       l (no ¬p) = no λ { (_ , ξ-# st) → ¬p (_ , st) }
proj? (e # l′)      l (no ¬p) = no λ { (_ , ξ-# st) → ¬p (_ , st) }

rcd? : (re : S ⊢ rexpr) → Dec (Stepsᴿ re) → Dec (Steps (RcdE re))
rcd? re (yes (re′ , st)) = yes (RcdE re′ , ξ-rcd st)
rcd? re (no ¬p)          = no λ { (_ , ξ-rcd st) → ¬p (_ , st) }

cons? : (l : Label) (e : S ⊢ expr) (re : S ⊢ rexpr) →
        Dec (Steps e) → Dec (Stepsᴿ re) → Dec (Stepsᴿ (consE l e re))
cons? l e re (yes (e′ , st)) _ = yes (consE l e′ re , ξ-here st)
cons? l e re (no ¬p) (yes (re′ , st)) with Val? e
... | yes v = yes (consE l e re′ , ξ-tail v st)
... | no ¬v = no λ { (_ , ξ-here st) → ¬p (_ , st) ; (_ , ξ-tail v _) → ¬v v }
cons? l e re (no ¬p) (no ¬q) =
  no λ { (_ , ξ-here st) → ¬p (_ , st) ; (_ , ξ-tail _ st) → ¬q (_ , st) }

stp⁺  : (e  : S ⊢ expr)  → Dec (Steps e)
stpᴿ⁺ : (re : S ⊢ rexpr) → Dec (Stepsᴿ re)

stp⁺ (` x)         = no λ { (_ , ()) }
stp⁺ (λx[ A ] e)   = no λ { (_ , ()) }
stp⁺ (Λα[<: A ] e) = no λ { (_ , ()) }
stp⁺ (e₁ · e₂)     = app?  e₁ e₂ (stp⁺ e₁) (stp⁺ e₂)
stp⁺ (e • C)       = tapp? e C   (stp⁺ e)
stp⁺ (e # l)       = proj? e l   (stp⁺ e)
stp⁺ (RcdE re)     = rcd?  re    (stpᴿ⁺ re)

stpᴿ⁺ (` x) = no λ { (_ , ()) }
stpᴿ⁺ nilE  = no λ { (_ , ()) }
stpᴿ⁺ (consE l e re) = cons? l e re (stp⁺ e) (stpᴿ⁺ re)

-- SOUNDNESS is BY CONSTRUCTION (the `yes` carries a derivation) and so
-- is COMPLETENESS (the `no` carries a refutation).  There is nothing
-- left to prove; the following is just that type, named.
Certified-animator : Set
Certified-animator = ∀ {S} (e : S ⊢ expr) → Dec (Σ[ e′ ∈ S ⊢ expr ] (e ↪ e′))

stp-is-certified : Certified-animator
stp-is-certified = stp⁺

-- the partial-function interface, derived from the decision
toMaybe : ∀ {P : Set} → Dec P → Maybe P
toMaybe (yes p) = just p
toMaybe (no  _) = nothing

stp : (e : S ⊢ expr) → Maybe (Σ[ e′ ∈ S ⊢ expr ] (e ↪ e′))
stp e = toMaybe (stp⁺ e)

-- …and it is complete: if anything steps, `stp` finds something.
stp-complete : ∀ {S} {e e′ : S ⊢ expr} → e ↪ e′ →
               Σ[ e″ ∈ S ⊢ expr ] Σ[ st ∈ (e ↪ e″) ] (stp e ≡ just (e″ , st))
stp-complete {e = e} {e′} r with stp⁺ e
... | yes (e″ , st) = e″ , st , refl
... | no ¬p         = ⊥-elim (¬p (e′ , r))

-- ─── determinism ────────────────────────────────────────────────────
-- This is the real content of Part 3 task 1.  `_≟_` decides equality of
-- REDUCTS; determinism is what turns "stp⁺ found a different reduct"
-- into "e ↪ e′ is false".

val-no-step  : Val e → e ↪ e′ → ⊥
vals-no-step : ValsᴿE re → re ↪ᴿ re₂ → ⊥

val-no-step vλ ()
val-no-step vΛ ()
val-no-step (vrcd vs) (ξ-rcd st) = vals-no-step vs st

vals-no-step vnil ()
vals-no-step (vcons v vs) (ξ-here st)   = val-no-step v st
vals-no-step (vcons v vs) (ξ-tail _ st) = vals-no-step vs st

determinism  : ∀ {S} {e e₁ e₂ : S ⊢ expr}    → e  ↪  e₁ → e  ↪  e₂ → e₁ ≡ e₂
determinismᴿ : ∀ {S} {re r₁ r₂ : S ⊢ rexpr} → re ↪ᴿ r₁ → re ↪ᴿ r₂ → r₁ ≡ r₂

determinism (β-λ _)     (β-λ _)      = refl
determinism (β-λ _)     (ξ-·₁ ())
determinism (β-λ v)     (ξ-·₂ _ st)  = ⊥-elim (val-no-step v st)
determinism (ξ-·₁ ())   (β-λ _)
determinism (ξ-·₁ st)   (ξ-·₁ st′)   = cong (_· _) (determinism st st′)
determinism (ξ-·₁ st)   (ξ-·₂ v _)   = ⊥-elim (val-no-step v st)
determinism (ξ-·₂ v st) (β-λ v′)     = ⊥-elim (val-no-step v′ st)
determinism (ξ-·₂ v st) (ξ-·₁ st′)   = ⊥-elim (val-no-step v st′)
determinism (ξ-·₂ _ st) (ξ-·₂ _ st′) = cong (_ ·_) (determinism st st′)
determinism β-Λ         β-Λ          = refl
determinism β-Λ         (ξ-• ())
determinism (ξ-• ())    β-Λ
determinism (ξ-• st)    (ξ-• st′)    = cong (_• _) (determinism st st′)
determinism (β-# _ h)   (β-# _ h′)   = HasE-unique h h′
determinism (β-# vs _)  (ξ-# (ξ-rcd st)) = ⊥-elim (vals-no-step vs st)
determinism (ξ-# (ξ-rcd st)) (β-# vs _)  = ⊥-elim (vals-no-step vs st)
determinism (ξ-# st)    (ξ-# st′)    = cong (_# _) (determinism st st′)
determinism (ξ-rcd st)  (ξ-rcd st′)  = cong RcdE (determinismᴿ st st′)

determinismᴿ (ξ-here st)   (ξ-here st′)   = cong (λ z → consE _ z _) (determinism st st′)
determinismᴿ (ξ-here st)   (ξ-tail v _)   = ⊥-elim (val-no-step v st)
determinismᴿ (ξ-tail v _)  (ξ-here st′)   = ⊥-elim (val-no-step v st′)
determinismᴿ (ξ-tail _ st) (ξ-tail _ st′) = cong (consE _ _) (determinismᴿ st st′)

-- ─── the CHALLENGE'S relation: evaluation contexts ──────────────────
-- The challenge states reduction as E-Ctx over
--   E ::= [−] | E t | v E | E [T] | E.l | {lᵢ=vᵢ, lⱼ=E, lₖ=tₖ}
-- `_↪_` above is the congruence-rule presentation.  The two are proved
-- equivalent here, so the decision procedure below decides the
-- challenge's relation and not a variant of it.

data ECtx  (S : Scope) : Set
data ECtxᴿ (S : Scope) : Set

data ECtx S where
  □    : ECtx S
  appl : ECtx S → S ⊢ expr → ECtx S                 -- E t
  appr : (v : S ⊢ expr) → Val v → ECtx S → ECtx S   -- v E
  tapp : ECtx S → S ⊢ type → ECtx S                 -- E [T]
  prj  : ECtx S → Label → ECtx S                    -- E.l
  rcd  : ECtxᴿ S → ECtx S                           -- {…, lⱼ=E, …}

data ECtxᴿ S where
  hd : Label → ECtx S → S ⊢ rexpr → ECtxᴿ S               -- {l=E, tₖ…}
  tl : Label → (v : S ⊢ expr) → Val v → ECtxᴿ S → ECtxᴿ S -- {l=v, …}

plug  : ECtx S  → S ⊢ expr → S ⊢ expr
plugᴿ : ECtxᴿ S → S ⊢ expr → S ⊢ rexpr
plug □            e = e
plug (appl E t)   e = (plug E e) · t
plug (appr v _ E) e = v · (plug E e)
plug (tapp E C)   e = (plug E e) • C
plug (prj E l)    e = (plug E e) # l
plug (rcd R)      e = RcdE (plugᴿ R e)
plugᴿ (hd l E re)   e = consE l (plug E e) re
plugᴿ (tl l v _ R)  e = consE l v (plugᴿ R e)

-- the immediate reduction rules, exactly as displayed in the challenge
infix 3 _↦_
data _↦_ : S ⊢ expr → S ⊢ expr → Set where
  E-AppAbs   : Val e₂ → ((λx[ A ] e₁) · e₂) ↦ (e₁ [ e₂ ]₀)
  E-TappTabs : ((Λα[<: A ] e) • C) ↦ (e [ C ]₀)
  E-ProjRcd  : ∀ {re : S ⊢ rexpr} {l e} → ValsᴿE re → HasE re l e →
               ((RcdE re) # l) ↦ e

infix 3 _⟶_ _⟶ᴿ_
data _⟶_  : S ⊢ expr  → S ⊢ expr  → Set where
  E-Ctx  : ∀ (E : ECtx S)  {e e′} → e ↦ e′ → (plug E e)  ⟶  (plug E e′)
data _⟶ᴿ_ : S ⊢ rexpr → S ⊢ rexpr → Set where
  E-Ctxᴿ : ∀ (R : ECtxᴿ S) {e e′} → e ↦ e′ → (plugᴿ R e) ⟶ᴿ (plugᴿ R e′)

↪→⟶   : ∀ {e e′ : S ⊢ expr}   → e  ↪  e′ → e  ⟶  e′
↪ᴿ→⟶ᴿ : ∀ {re re′ : S ⊢ rexpr} → re ↪ᴿ re′ → re ⟶ᴿ re′

↪→⟶ (β-λ v)  = E-Ctx □ (E-AppAbs v)
↪→⟶ β-Λ      = E-Ctx □ E-TappTabs
↪→⟶ (β-# vs h) = E-Ctx □ (E-ProjRcd vs h)
↪→⟶ (ξ-·₁ {e₂ = e₂} st) with ↪→⟶ st
... | E-Ctx E st₀ = E-Ctx (appl E e₂) st₀
↪→⟶ (ξ-·₂ {e₁ = e₁} v st) with ↪→⟶ st
... | E-Ctx E st₀ = E-Ctx (appr e₁ v E) st₀
↪→⟶ (ξ-• {C = C} st) with ↪→⟶ st
... | E-Ctx E st₀ = E-Ctx (tapp E C) st₀
↪→⟶ (ξ-# {l = l} st) with ↪→⟶ st
... | E-Ctx E st₀ = E-Ctx (prj E l) st₀
↪→⟶ (ξ-rcd st) with ↪ᴿ→⟶ᴿ st
... | E-Ctxᴿ R st₀ = E-Ctx (rcd R) st₀

↪ᴿ→⟶ᴿ (ξ-here {l = l} {re = re} st) with ↪→⟶ st
... | E-Ctx E st₀ = E-Ctxᴿ (hd l E re) st₀
↪ᴿ→⟶ᴿ (ξ-tail {e = e} {l = l} v st) with ↪ᴿ→⟶ᴿ st
... | E-Ctxᴿ R st₀ = E-Ctxᴿ (tl l e v R) st₀

plug-↪  : ∀ (E : ECtx S)  {e e′ : S ⊢ expr} → e ↦ e′ → (plug E e)  ↪  (plug E e′)
plugᴿ-↪ : ∀ (R : ECtxᴿ S) {e e′ : S ⊢ expr} → e ↦ e′ → (plugᴿ R e) ↪ᴿ (plugᴿ R e′)
plug-↪ □            (E-AppAbs v)     = β-λ v
plug-↪ □            E-TappTabs       = β-Λ
plug-↪ □            (E-ProjRcd vs h) = β-# vs h
plug-↪ (appl E t)   st = ξ-·₁ (plug-↪ E st)
plug-↪ (appr v p E) st = ξ-·₂ p (plug-↪ E st)
plug-↪ (tapp E C)   st = ξ-• (plug-↪ E st)
plug-↪ (prj E l)    st = ξ-# (plug-↪ E st)
plug-↪ (rcd R)      st = ξ-rcd (plugᴿ-↪ R st)
plugᴿ-↪ (hd l E re)  st = ξ-here (plug-↪ E st)
plugᴿ-↪ (tl l v p R) st = ξ-tail p (plugᴿ-↪ R st)

⟶→↪ : ∀ {e e′ : S ⊢ expr} → e ⟶ e′ → e ↪ e′
⟶→↪ (E-Ctx E st) = plug-↪ E st

-- ═══ TASK 1: decide  t ⟶ t′  ════════════════════════════════════════
-- For ARBITRARY t and t′.  Not "for concrete pairs, by conversion".

infix 4 _↪?_

_↪?_ : ∀ {S} (e e′ : S ⊢ expr) → Dec (e ↪ e′)
_↪?_ {S} e e′ with stp⁺ e
... | no ¬p = no λ st → ¬p (e′ , st)
... | yes (e″ , st) with e″ ≟ e′
...   | yes refl = yes st
...   | no ¬q    = no λ st′ → ¬q (determinism st st′)

-- …and the same decision for the challenge's own relation, through the
-- equivalence just proved.  THIS is what Part 3 task 1 asks for.
infix 4 _⟶?_

_⟶?_ : ∀ {S} (e e′ : S ⊢ expr) → Dec (e ⟶ e′)
e ⟶? e′ with e ↪? e′
... | yes st = yes (↪→⟶ st)
... | no ¬st = no λ r → ¬st (⟶→↪ r)

-- ─── Task 3: find a t′ with t ⟶ t′ ──────────────────────────────────

reduct : S ⊢ expr → Maybe (S ⊢ expr)
reduct e with stp⁺ e
... | yes (e′ , _) = just e′
... | no  _        = nothing

-- ═══ TASK 2: decide  t ⟶* t′ ↛  ═════════════════════════════════════

infix  3 _↪*_
infixr 5 _◅_

data _↪*_ {S} : S ⊢ expr → S ⊢ expr → Set where
  done : ∀ {e}       → e ↪* e
  _◅_  : ∀ {e e′ e″} → e ↪ e′ → e′ ↪* e″ → e ↪* e″

-- normal forms are unique, by determinism
nf-unique : ∀ {S} {e e₁ e₂ : S ⊢ expr} → e ↪* e₁ → NF e₁ → e ↪* e₂ → NF e₂ → e₁ ≡ e₂
nf-unique done       _   done         _   = refl
nf-unique done       nf₁ (st ◅ _)     _   = ⊥-elim (nf₁ (_ , st))
nf-unique (st ◅ _)   _   done         nf₂ = ⊥-elim (nf₂ (_ , st))
nf-unique (st ◅ rs)  nf₁ (st′ ◅ rs′)  nf₂ with determinism st st′
... | refl = nf-unique rs nf₁ rs′ nf₂

-- a certified evaluator: it returns the normal form together with the
-- reduction sequence reaching it AND the proof that it is normal
eval! : ∀ {S} → ℕ → (e : S ⊢ expr) → Maybe (Σ[ e′ ∈ S ⊢ expr ] ((e ↪* e′) × NF e′))
eval! zero    e = nothing
eval! (suc n) e with stp⁺ e
... | no ¬p = just (e , done , ¬p)
... | yes (e′ , st) with eval! n e′
...   | just (e″ , rs , nf) = just (e″ , st ◅ rs , nf)
...   | nothing             = nothing

-- and the decision, up to the fuel bound: `nothing` means "not decided
-- within n steps", never "false"
evalDec : ∀ {S} → ℕ → (e e′ : S ⊢ expr) → Maybe (Dec ((e ↪* e′) × NF e′))
evalDec n e e′ with eval! n e
... | nothing = nothing
... | just (e″ , rs , nf) with e″ ≟ e′
...   | yes refl = just (yes (rs , nf))
...   | no ¬q    = just (no λ { (rs′ , nf′) → ¬q (nf-unique rs nf rs′ nf′) })

-- the plain evaluator: iterate `stp⁺` up to a fuel bound
eval : ℕ → S ⊢ expr → S ⊢ expr
eval zero    e = e
eval (suc n) e with stp⁺ e
... | yes (e′ , _) = eval n e′
... | no  _        = e

-- ═══ RUNNING IT ═════════════════════════════════════════════════════
-- The development's own examples.  The CHALLENGE's own example suite is
-- in Challenge/Suite.agda.

la lb : Label
la = 0
lb = 1

idTop : [] ⊢ expr                                   -- λx:Top. x
idTop = λx[ Top ] (` zero)

polyId : [] ⊢ expr                                  -- Λα<:Top. λx:α. x
polyId = Λα[<: Top ] (λx[ ` zero ] (` zero))

-- {a = λx:Top.x, b = Λα<:Top.λx:α.x}
rec : [] ⊢ expr
rec = RcdE (consE la idTop (consE lb polyId nilE))

-- ─── (1) deciding  t ⟶ t′ ───────────────────────────────────────────
-- by the DECISION PROCEDURE, not by conversion: `_↪?_` is total.
dec₁ : Dec ((polyId • Top) ↪ (λx[ Top ] (` zero)))
dec₁ = (polyId • Top) ↪? (λx[ Top ] (` zero))

-- it says yes …
dec₁-yes : isYes ((polyId • Top) ↪? (λx[ Top ] (` zero))) ≡ true
dec₁-yes = refl

-- … and it says NO to a wrong reduct, which is what distinguishes a
-- decision procedure from a step function
dec₁-no : isYes ((polyId • Top) ↪? polyId) ≡ false
dec₁-no = refl

-- and no to a normal term
dec₂-no : isYes (idTop ↪? idTop) ≡ false
dec₂-no = refl

-- type application fires, and the type substitution [α ↦ Top] is
-- performed by the rewrite system inside the annotation:
run₁ : reduct (polyId • Top) ≡ just (λx[ Top ] (` zero))
run₁ = refl

-- a value does not stp
run₂ : reduct idTop ≡ nothing
run₂ = refl

-- a stuck term does not stp (projection of an absent label)
run₃ : reduct (rec # 7) ≡ nothing
run₃ = refl

-- ─── (2) evaluation to normal form ──────────────────────────────────
-- ((Λα<:Top. λx:α. x) [Top]) (λx:Top. x)  ⟶*  λx:Top. x
ex₁ : [] ⊢ expr
ex₁ = (polyId • Top) · idTop

run₄ : eval 10 ex₁ ≡ idTop
run₄ = refl

run₅ : reduct (eval 10 ex₁) ≡ nothing        -- the result is normal
run₅ = refl

-- the certified version of the same: a decision, with the ⟶* derivation
run₄′ : isJustYes (evalDec 10 ex₁ idTop) ≡ true
run₄′ = refl

run₄″ : isJustYes (evalDec 10 ex₁ polyId) ≡ false
run₄″ = refl

-- record projection, twice, through a record that must first be seen to
-- be a value
ex₂ : [] ⊢ expr
ex₂ = (rec # lb) • Top

run₆ : eval 10 ex₂ ≡ (λx[ Top ] (` zero))
run₆ = refl

-- projection of the first field
run₇ : eval 10 (rec # la) ≡ idTop
run₇ = refl

-- a redex UNDER a record: {a = (Λα<:Top.λx:α.x)[Top], b = …} is not a
-- value until its first field has been reduced
ex₃ : [] ⊢ expr
ex₃ = RcdE (consE la (polyId • Top) (consE lb idTop nilE))

run₈ : eval 10 ex₃ ≡ RcdE (consE la (λx[ Top ] (` zero)) (consE lb idTop nilE))
run₈ = refl

-- and then projecting from it
run₉ : eval 10 (ex₃ # la) ≡ (λx[ Top ] (` zero))
run₉ = refl

-- a longer chain: apply the polymorphic identity to itself at Top→Top
ex₄ : [] ⊢ expr
ex₄ = ((polyId • (Top ⇒ Top)) · idTop) · (RcdE nilE)

run₁₀ : eval 20 ex₄ ≡ RcdE nilE
run₁₀ = refl

-- ─── (3) the animator, and its certificate ──────────────────────────
animate : Dec (Σ[ e′ ∈ [] ⊢ expr ] (ex₁ ↪ e′))
animate = stp⁺ ex₁

animate-fires : reduct ex₁ ≡ just ((λx[ Top ] (` zero)) · idTop)
animate-fires = refl

-- typing of the examples, so the runs are runs of WELL-TYPED terms
Γ₀ : Ctx []
Γ₀ _ ()

⊢polyId : Γ₀ ⊢ polyId ∶ (∀[<: Top ] ((` zero) ⇒ (` zero)))
⊢polyId = ⊢Λ (⊢λ (⊢` refl))

⊢idTop : Γ₀ ⊢ idTop ∶ (Top ⇒ Top)
⊢idTop = ⊢λ (⊢` refl)

⊢rec : Γ₀ ⊢ rec ∶ (RcdT (consT la (Top ⇒ Top)
                        (consT lb (∀[<: Top ] ((` zero) ⇒ (` zero))) nilT)))
⊢rec = ⊢rcd (⊢ᴿ-cons ⊢idTop (⊢ᴿ-cons ⊢polyId ⊢ᴿ-nil))

-- record WIDTH subtyping, checked
⊢rec-wide : Γ₀ ⊢ rec ∶ (RcdT (consT la (Top ⇒ Top) nilT))
⊢rec-wide = ⊢<: ⊢rec (<:-rcd (<:ᴿ-cons here (<:-reflexive _) <:ᴿ-nil))

-- (polyId [Top]) : Top→Top, applied to idTop coerced to Top by T-Sub
⊢ex₁ : Γ₀ ⊢ ex₁ ∶ Top
⊢ex₁ = ⊢· (⊢• ⊢polyId <:-top) (⊢<: ⊢idTop <:-top)

-- preservation, run on the concrete reduction of run₁
⊢after : Γ₀ ⊢ (λx[ Top ] (` zero)) ∶ (Top ⇒ Top)
⊢after = preservation (⊢• ⊢polyId <:-top) β-Λ
