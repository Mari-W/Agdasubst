{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.STLCTyping — extrinsic typing + SUBJECT REDUCTION for co-de-Bruijn STLC.
--
-- Built on the shared library: the substitution engine Sf.STLC (whose σ-laws are
-- rewrites) and the generic context machinery Sf.Context.  The SR proof is
-- SUBST-FREE: there is no use of `Relation.…PropositionalEquality.subst` and no
-- manual application of any substitution lemma — every σ-/context-law fires as a
-- registered rewrite, so the proof terms are the bare typed smart-constructors.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.STLCTyping where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sf.STLC hiding (thinL; thinR)  -- the σ-engine's opaque cover-thinnings;
                                          -- the typing layer uses Sf.Context's transparent thL/thR

-- simple types (the closed classifier)
data Type : Set where
  ι   : Type
  _⇒_ : Type → Type → Type
infixr 5 _⇒_
variable A B C : Type

-- contexts = the generic Cx with the closed simple-type classifier
open import Sf.Context ⊤ (λ _ → Type) public
variable Φ Ψ : Cx Γ

-- ── the typing judgement ──
data _⊢_∶_ : ∀ {Γ} → Cx Γ → Tm Γ → Type → Set where
  ⊢var  : (ε ,- A) ⊢ var ∶ A
  ⊢app  : ∀ {Γ}{Φ : Cx Γ}{sₗ sᵣ}{l : Tm sₗ}{r : Tm sᵣ}{cv : Cover sₗ sᵣ Γ}{A B}
        → splitL cv Φ ⊢ l ∶ (A ⇒ B) → splitR cv Φ ⊢ r ∶ A → Φ ⊢ app (pair l r cv) ∶ B
  ⊢lamᵘ : ∀ {Γ}{Φ : Cx Γ}{t}{A B} → (Φ ,- A) ⊢ t ∶ B → Φ ⊢ lam (use t)  ∶ (A ⇒ B)
  ⊢lamᵈ : ∀ {Γ}{Φ : Cx Γ}{t}{A B} → Φ        ⊢ t ∶ B → Φ ⊢ lam (drop t) ∶ (A ⇒ B)
infix 4 _⊢_∶_

-- typing of a thing-with-thinning: restrict the context to its support
_⊢↑_∶_ : ∀ {Δ} → Cx Δ → Tm ↑ Δ → Type → Set
Φ ⊢↑ (t ⇑ θ) ∶ A = rest θ Φ ⊢ t ∶ A
infix 4 _⊢↑_∶_

-- ── typed smart-constructors.  All DEFINITIONAL: cohL/cohR/rest-oe are rewrites. ──
-- typed smart-app: combine two typed things-with-thinnings
⊢app↑ : ∀ {Δ}{Ψ : Cx Δ}{A B}(l′ r′ : Tm ↑ Δ) → Ψ ⊢↑ l′ ∶ (A ⇒ B) → Ψ ⊢↑ r′ ∶ A → Ψ ⊢↑ (app↑ l′ r′) ∶ B
⊢app↑ {Ψ = Ψ} (l ⇑ θ) (r ⇑ φ) ⊢l ⊢r = ⊢app {Φ = rest (out (cop θ φ)) Ψ} {cv = cov (cop θ φ)} ⊢l ⊢r

-- typed smart-lam: read the body's thinning (use/drop) — body EXPLICIT so an
-- abstract body is a stuck neutral whose type is exactly the goal.
⊢lam↑ : ∀ {Δ}{Ψ : Cx Δ}{A B}(body : Tm ↑ (tt ∷ Δ)) → (Ψ ,- A) ⊢↑ body ∶ B → Ψ ⊢↑ (lam↑ body) ∶ (A ⇒ B)
⊢lam↑ (t ⇑ os θ) ⊢t = ⊢lamᵘ ⊢t
⊢lam↑ (t ⇑ o' θ) ⊢t = ⊢lamᵈ ⊢t

-- the fresh bound variable, typed.  rest oe Ψ ≡ ε fires (rewrite), so this is ⊢var.
⊢fresh : ∀ {Δ}{Ψ : Cx Δ}{A} → (Ψ ,- A) ⊢↑ var₀ ∶ A
⊢fresh = ⊢var

-- ── well-typed substitution ──
data WtSub : ∀ {Γ Δ} → Sub Δ Γ → Cx Γ → Cx Δ → Set where
  []   : ∀ {Δ}{Ψ : Cx Δ} → WtSub [] ε Ψ
  _,-_ : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{u}{A}
       → WtSub σ Φ Ψ → Ψ ⊢↑ u ∶ A → WtSub (σ ,- u) (Φ ,- A) Ψ

-- env split / weakening preserve typing (all definitional)
selL-pres : ∀ {Γₗ Γᵣ Γ Δ}{σ : Sub Δ Γ}{Φ}{Ψ}(cv : Cover Γₗ Γᵣ Γ) → WtSub σ Φ Ψ → WtSub (selL cv σ) (splitL cv Φ) Ψ
selL-pres czz     []         = []
selL-pres (css c) (wσ ,- ⊢u) = selL-pres c wσ ,- ⊢u
selL-pres (cs' c) (wσ ,- ⊢u) = selL-pres c wσ ,- ⊢u
selL-pres (c's c) (wσ ,- ⊢u) = selL-pres c wσ
selR-pres : ∀ {Γₗ Γᵣ Γ Δ}{σ : Sub Δ Γ}{Φ}{Ψ}(cv : Cover Γₗ Γᵣ Γ) → WtSub σ Φ Ψ → WtSub (selR cv σ) (splitR cv Φ) Ψ
selR-pres czz     []         = []
selR-pres (css c) (wσ ,- ⊢u) = selR-pres c wσ ,- ⊢u
selR-pres (cs' c) (wσ ,- ⊢u) = selR-pres c wσ
selR-pres (c's c) (wσ ,- ⊢u) = selR-pres c wσ ,- ⊢u
opaque
  unfolding wkSub
  wkSub-pres : ∀ {s Γ Δ}{σ : Sub Δ Γ}{Φ}{Ψ : Cx Δ}{A} → WtSub σ Φ Ψ → WtSub (wkSub {s} σ) Φ (Ψ ,- A)
  wkSub-pres []         = []
  wkSub-pres (wσ ,- ⊢u) = wkSub-pres wσ ,- ⊢u    -- rest (o' θ)(Ψ,-A) = rest θ Ψ, ⊢u reused

-- ── SUBSTITUTION PRESERVES TYPING (the crux; subst-free, σ-laws fire as rewrites) ──
opaque
  unfolding sub wkSub
  sub-pres : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{e}{A} → WtSub σ Φ Ψ → Φ ⊢ e ∶ A → Ψ ⊢↑ (sub e σ) ∶ A
  sub-pres ([] ,- ⊢u) ⊢var = ⊢u
  sub-pres {σ = σ} wσ (⊢app {l = l} {r = r} {cv = cv} ⊢l ⊢r) =
    ⊢app↑ (sub l (selL cv σ)) (sub r (selR cv σ)) (sub-pres (selL-pres cv wσ) ⊢l) (sub-pres (selR-pres cv wσ) ⊢r)
  sub-pres {σ = σ} {Ψ = Ψ} wσ (⊢lamᵘ {t = t} {A = A} ⊢t) =
    ⊢lam↑ (sub t (wkSub σ ,- var₀))
          (sub-pres {Ψ = Ψ ,- A} (_,-_ {u = var₀} (wkSub-pres wσ) (⊢fresh {Ψ = Ψ} {A = A})) ⊢t)
  sub-pres wσ (⊢lamᵈ ⊢t) = ⊢lamᵈ (sub-pres wσ ⊢t)

-- ════════════════════════════════════════════════════════════════════════════
-- β-reduction and SUBJECT REDUCTION
-- ════════════════════════════════════════════════════════════════════════════
opaque
  unfolding idEmb
  id-emb-pres : ∀ {sup Δ}(θ : sup ⊑ Δ)(Ψ : Cx Δ) → WtSub (idEmb θ) (rest θ Ψ) Ψ
  id-emb-pres oz     ε        = []
  id-emb-pres (os θ) (Ψ ,- A) = _,-_ {u = var₀} (wkSub-pres (id-emb-pres θ Ψ)) (⊢fresh {Ψ = Ψ})
  id-emb-pres (o' θ) (Ψ ,- A) = wkSub-pres (id-emb-pres θ Ψ)

-- the β-environment is well-typed: identity on the function's free vars, arg on
-- the bound var.  No subst — splitL/splitR are rest∘thin definitionally.
β-env-pres : ∀ {sₗ sᵣ Γ}{Φ : Cx Γ}{a : Tm sᵣ}{A}(cv : Cover sₗ sᵣ Γ)
  → splitR cv Φ ⊢ a ∶ A → WtSub (idEmb (thL cv) ,- (a ⇑ thR cv)) (splitL cv Φ ,- A) Φ
β-env-pres {Φ = Φ} {a = a} cv ⊢a = _,-_ {u = a ⇑ thR cv} (id-emb-pres (thL cv) Φ) ⊢a

-- ── VALUES: λ-abstractions only (use/drop) ──
data Value : ∀ {Γ} → Tm Γ → Set where
  V-lamᵘ : ∀ {Γ}{t : Tm (tt ∷ Γ)} → Value (lam (use t))
  V-lamᵈ : ∀ {Γ}{t : Tm Γ}        → Value (lam (drop t))

-- ── CALL-BY-VALUE small-step.  Contractum support may shrink, hence Tm ↑ Γ. ──
-- Congruence re-embeds the reduced subterm along the cover-thinning and reassembles
-- with app↑; the function must be reduced before the argument.
data _⟶_ : ∀ {Γ} → Tm Γ → Tm ↑ Γ → Set where
  -- β: only fires on a value argument
  β  : ∀ {Γ sₗ sᵣ}{t : Tm (tt ∷ sₗ)}{a : Tm sᵣ}{cv : Cover sₗ sᵣ Γ}
     → Value a → app (pair (lam (use t))  a cv) ⟶ sub t (idEmb (thL cv) ,- (a ⇑ thR cv))
  βᵈ : ∀ {Γ sₗ sᵣ}{t : Tm sₗ}{a : Tm sᵣ}{cv : Cover sₗ sᵣ Γ}
     → Value a → app (pair (lam (drop t)) a cv) ⟶ sub t (idEmb (thL cv))
  -- congruence: reduce the FUNCTION first
  ξ-fun : ∀ {Γ sₗ sᵣ}{l : Tm sₗ}{l′ : Tm ↑ sₗ}{r : Tm sᵣ}{cv : Cover sₗ sᵣ Γ}
        → l ⟶ l′ → app (pair l r cv) ⟶ app↑ (l′ ⟨ thL cv ⟩) (r ⇑ thR cv)
  -- congruence: once the function is a value, reduce the ARGUMENT
  ξ-arg : ∀ {Γ sₗ sᵣ}{l : Tm sₗ}{r : Tm sᵣ}{r′ : Tm ↑ sᵣ}{cv : Cover sₗ sᵣ Γ}
        → Value l → r ⟶ r′ → app (pair l r cv) ⟶ app↑ (l ⇑ thL cv) (r′ ⟨ thR cv ⟩)
infix 3 _⟶_

-- SUBJECT REDUCTION for CBV.  β/βᵈ via sub-pres on the β-environment; congruence
-- via ⊢app↑ + the IH (rest-functoriality makes the re-embedding land in the IH ctx).
preserve : ∀ {Γ}{Φ : Cx Γ}{e}{e′}{A} → Φ ⊢ e ∶ A → e ⟶ e′ → Φ ⊢↑ e′ ∶ A
preserve         (⊢app {cv = cv} (⊢lamᵘ ⊢t) ⊢a) (β  _) = sub-pres (β-env-pres cv ⊢a) ⊢t
preserve {Φ = Φ} (⊢app {cv = cv} (⊢lamᵈ ⊢t) ⊢a) (βᵈ _) = sub-pres (id-emb-pres (thL cv) Φ) ⊢t
preserve {Φ = Φ} (⊢app {r = r} {cv = cv} ⊢l ⊢r) (ξ-fun {l′ = l′} l⟶l′) =
  ⊢app↑ (l′ ⟨ thL cv ⟩) (r ⇑ thR cv) (preserve ⊢l l⟶l′) ⊢r
preserve {Φ = Φ} (⊢app {l = l} {cv = cv} ⊢l ⊢r) (ξ-arg {r′ = r′} _ r⟶r′) =
  ⊢app↑ (l ⇑ thL cv) (r′ ⟨ thR cv ⟩) ⊢l (preserve ⊢r r⟶r′)
