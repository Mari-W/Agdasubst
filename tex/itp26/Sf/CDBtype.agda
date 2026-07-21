{-# OPTIONS --rewriting --local-confluence-check #-}
-- ============================================================================
-- Extrinsic typing + SUBJECT REDUCTION for co-de-Bruijn STLC, on the working
-- substitution of CDBsub.  The context Cx Γ assigns a type to each variable of
-- the support Γ.
--
-- Substs remaining: 2 (cohL, cohR — the cop coproduct/context coherence).  The
-- other coherences are gone:
--   * cohSplitL/R : eliminated by DEFINING splitL := rest ∘ thinL (refl bridge).
--   * rest-oe     : a confluent REWRITE (oe is opaque, so no competing redex).
-- cohL/cohR resist rewrite-orientation: their LHS is non-linear in `cop θ φ`,
-- and keyed on splitL it never matches (splitL unfolds first); keyed on the
-- rest∘thinL form it races cop's unit law cop-oiL.  So they stay as substs.
-- ============================================================================
module CDBtype where
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Agda.Builtin.Equality.Rewrite
open import CDBsig
open import CDBterm
open import CDBsub

data Type : Set where
  ι   : Type
  _⇒_ : Type → Type → Type
infixr 5 _⇒_
variable A B C : Type

data Cx : Scope → Set where
  ε    : Cx []
  _,-_ : ∀ {Γ} → Cx Γ → Type → Cx (tt ∷ Γ)
infixl 5 _,-_
variable Φ Ψ : Cx Γ

-- restrict a context to the support picked out by a thinning
rest : ∀ {sup Δ} → sup ⊑ Δ → Cx Δ → Cx sup
rest oz     ε        = ε
rest (os θ) (Φ ,- A) = rest θ Φ ,- A
rest (o' θ) (Φ ,- A) = rest θ Φ

-- cover → its two embedding thinnings (sₗ⊑Γ and sᵣ⊑Γ)
thinL : ∀ {sₗ sᵣ Γ} → Cover sₗ sᵣ Γ → sₗ ⊑ Γ
thinL czz     = oz
thinL (css c) = os (thinL c)
thinL (cs' c) = os (thinL c)
thinL (c's c) = o' (thinL c)
thinR : ∀ {sₗ sᵣ Γ} → Cover sₗ sᵣ Γ → sᵣ ⊑ Γ
thinR czz     = oz
thinR (css c) = os (thinR c)
thinR (cs' c) = o' (thinR c)
thinR (c's c) = os (thinR c)

-- a context split is DEFINED as restriction along the cover-thinning, so the
-- "rest = split" coherences (cohSplitL/R) are now refl — 3 substs eliminated.
splitL : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Cx Γ → Cx Γₗ
splitL cv Φ = rest (thinL cv) Φ
splitR : ∀ {Γₗ Γᵣ Γ} → Cover Γₗ Γᵣ Γ → Cx Γ → Cx Γᵣ
splitR cv Φ = rest (thinR cv) Φ

-- COMPLETION rules of McBride's thinning algebra, so cohL/cohR below can be
-- confluent REWRITES.  Each LHS is stuck outside (oi/covL/covR/full are opaque
-- in CDBsig) ⇒ no competing redex ⇒ each is a sound rewrite.  Proven by
-- unfolding the opaque ops.  These exactly close the cohL/cohR × cop-oiL/cop-oiR
-- critical pairs (cop oi φ → covL φ, etc.).
opaque
  unfolding oi covL covR full
  rest-oi : ∀ {Δ}(Ψ : Cx Δ) → rest oi Ψ ≡ Ψ
  rest-oi ε        = refl
  rest-oi (Ψ ,- A) = cong (_,- A) (rest-oi Ψ)
  thinL-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ) → thinL (covL φ) ≡ oi
  thinL-covL oz     = refl
  thinL-covL (os φ) = cong os (thinL-covL φ)
  thinL-covL (o' φ) = cong os (thinL-covL φ)
  thinR-covL : ∀ {Γ Δ}(φ : Γ ⊑ Δ) → thinR (covL φ) ≡ φ
  thinR-covL oz     = refl
  thinR-covL (os φ) = cong os (thinR-covL φ)
  thinR-covL (o' φ) = cong o' (thinR-covL φ)
  thinL-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ) → thinL (covR θ) ≡ θ
  thinL-covR oz     = refl
  thinL-covR (os θ) = cong os (thinL-covR θ)
  thinL-covR (o' θ) = cong o' (thinL-covR θ)
  thinR-covR : ∀ {Γ Δ}(θ : Γ ⊑ Δ) → thinR (covR θ) ≡ oi
  thinR-covR oz     = refl
  thinR-covR (os θ) = cong os (thinR-covR θ)
  thinR-covR (o' θ) = cong os (thinR-covR θ)
  thinL-full : ∀ {Γ} → thinL (full {Γ}) ≡ oi
  thinL-full {[]}    = refl
  thinL-full {_ ∷ Γ} = cong os thinL-full
  thinR-full : ∀ {Γ} → thinR (full {Γ}) ≡ oi
  thinR-full {[]}    = refl
  thinR-full {_ ∷ Γ} = cong os thinR-full
{-# REWRITE rest-oi thinL-covL thinR-covL thinL-covR thinR-covR thinL-full thinR-full #-}

data _⊢_∶_ : ∀ {Γ} → Cx Γ → Tm Γ → Type → Set where
  ⊢var  : ∀ {A} → (ε ,- A) ⊢ var ∶ A
  ⊢app  : ∀ {Γ}{Φ : Cx Γ}{sₗ sᵣ}{l : Tm sₗ}{r : Tm sᵣ}{cv : Cover sₗ sᵣ Γ}{A B}
        → splitL cv Φ ⊢ l ∶ (A ⇒ B) → splitR cv Φ ⊢ r ∶ A → Φ ⊢ app (pair l r cv) ∶ B
  ⊢lamᵘ : ∀ {Γ}{Φ : Cx Γ}{t}{A B} → (Φ ,- A) ⊢ t ∶ B → Φ ⊢ lam (use t)  ∶ (A ⇒ B)
  ⊢lamᵈ : ∀ {Γ}{Φ : Cx Γ}{t}{A B} → Φ        ⊢ t ∶ B → Φ ⊢ lam (drop t) ∶ (A ⇒ B)
infix 4 _⊢_∶_

-- typing of a thing-with-thinning: restrict the context to its support
_⊢↑_∶_ : ∀ {Δ} → Cx Δ → Tm ↑ Δ → Type → Set
Φ ⊢↑ (t ⇑ θ) ∶ A = rest θ Φ ⊢ t ∶ A
infix 4 _⊢↑_∶_

-- the coproduct/context coherence (McBride §6): the cover-split of the merged
-- context is the per-side restriction.  Proven by unfolding cop and inducting.
-- cohL/cohR stated on the UNFOLDED rest∘thinL form (splitL unfolds eagerly, so a
-- splitL-keyed rule would never match the goal).  Registered as REWRITES; the
-- completion rules above close their critical pairs with cop-oiL/cop-oiR.
opaque
  unfolding cop
  cohL : ∀ {sₗ sᵣ Δ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(Ψ : Cx Δ)
       → rest (thinL (cov (cop θ φ))) (rest (out (cop θ φ)) Ψ) ≡ rest θ Ψ
  cohL oz     oz     ε        = refl
  cohL (os θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohL θ φ Ψ)
  cohL (os θ) (o' φ) (Ψ ,- A) = cong (_,- A) (cohL θ φ Ψ)
  cohL (o' θ) (os φ) (Ψ ,- A) = cohL θ φ Ψ
  cohL (o' θ) (o' φ) (Ψ ,- A) = cohL θ φ Ψ
  cohR : ∀ {sₗ sᵣ Δ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(Ψ : Cx Δ)
       → rest (thinR (cov (cop θ φ))) (rest (out (cop θ φ)) Ψ) ≡ rest φ Ψ
  cohR oz     oz     ε        = refl
  cohR (os θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohR θ φ Ψ)
  cohR (os θ) (o' φ) (Ψ ,- A) = cohR θ φ Ψ
  cohR (o' θ) (os φ) (Ψ ,- A) = cong (_,- A) (cohR θ φ Ψ)
  cohR (o' θ) (o' φ) (Ψ ,- A) = cohR θ φ Ψ
{-# REWRITE cohL cohR #-}

-- typed smart-app: combine two typed things-with-thinnings.  Now SUBST-FREE:
-- cohL/cohR fire as rewrites, so the cop coherence holds definitionally.
⊢app↑ : ∀ {Δ}{Ψ : Cx Δ}{A B}(l′ r′ : Tm ↑ Δ)
      → Ψ ⊢↑ l′ ∶ (A ⇒ B) → Ψ ⊢↑ r′ ∶ A → Ψ ⊢↑ (app↑ l′ r′) ∶ B
⊢app↑ {Ψ = Ψ} (l ⇑ θ) (r ⇑ φ) ⊢l ⊢r =
  ⊢app {Φ = rest (out (cop θ φ)) Ψ} {cv = cov (cop θ φ)} ⊢l ⊢r

-- law for oe: restricting any context by the empty thinning yields ε.
-- Proven `unfolding oe` (need the clauses), but oe stays opaque OUTSIDE, so
-- registering this as a rewrite is confluent (no `oe → o' oe` competing redex).
opaque
  unfolding oe
  rest-oe : ∀ {Δ}(Ψ : Cx Δ) → rest oe Ψ ≡ ε
  rest-oe ε        = refl
  rest-oe (Ψ ,- A) = rest-oe Ψ
{-# REWRITE rest-oe #-}

-- typed smart-lam: pattern-match the body's thinning (use/drop) — definitional.
-- body is EXPLICIT: applied to an abstract body (in sub-pres) this is a stuck
-- neutral whose type is exactly the goal; implicit body would spawn os/o' metas.
⊢lam↑ : ∀ {Δ}{Ψ : Cx Δ}{A B}(body : Tm ↑ (tt ∷ Δ))
      → (Ψ ,- A) ⊢↑ body ∶ B → Ψ ⊢↑ (lam↑ body) ∶ (A ⇒ B)
⊢lam↑ (t ⇑ os θ) ⊢t = ⊢lamᵘ ⊢t
⊢lam↑ (t ⇑ o' θ) ⊢t = ⊢lamᵈ ⊢t

-- the fresh bound variable, typed.  rest oe Ψ ≡ ε now fires definitionally (rewrite),
-- so this is just ⊢var — no subst.
⊢fresh : ∀ {Δ}{Ψ : Cx Δ}{A} → (Ψ ,- A) ⊢↑ (var ⇑ os oe) ∶ A
⊢fresh = ⊢var

-- well-typed substitution: each entry typed in the target context
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
  wkSub-pres : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ}{Ψ : Cx Δ}{A} → WtSub σ Φ Ψ → WtSub (wkSub σ) Φ (Ψ ,- A)
  wkSub-pres []         = []
  wkSub-pres (wσ ,- ⊢u) = wkSub-pres wσ ,- ⊢u    -- rest (o' θ)(Ψ,-A) = rest θ Ψ, so ⊢u reused

-- SUBSTITUTION PRESERVES TYPING
opaque
  unfolding sub wkSub lift
  sub-pres : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{e}{A}
           → WtSub σ Φ Ψ → Φ ⊢ e ∶ A → Ψ ⊢↑ (sub e σ) ∶ A
  sub-pres ([] ,- ⊢u) ⊢var = ⊢u
  sub-pres {σ = σ} wσ (⊢app {l = l} {r = r} {cv = cv} ⊢l ⊢r) =
    ⊢app↑ (sub l (selL cv σ)) (sub r (selR cv σ))
          (sub-pres (selL-pres cv wσ) ⊢l) (sub-pres (selR-pres cv wσ) ⊢r)
  sub-pres {σ = σ} {Ψ = Ψ} wσ (⊢lamᵘ {t = t} {A = A} ⊢t) =
    ⊢lam↑ (sub t (wkSub σ ,- (var ⇑ os oe)))
          (sub-pres {Ψ = Ψ ,- A}
            (_,-_ {u = var ⇑ os oe} (wkSub-pres wσ) (⊢fresh {Ψ = Ψ} {A = A})) ⊢t)
  sub-pres wσ (⊢lamᵈ ⊢t) = ⊢lamᵈ (sub-pres wσ ⊢t)

-- ============================================================================
-- β-reduction and SUBJECT REDUCTION
-- ============================================================================
-- identity substitution embedded along a thinning θ : sup ⊑ Δ  (Sub Δ sup)
idEmb : ∀ {sup Δ} → sup ⊑ Δ → Sub Δ sup
idEmb oz     = []
idEmb (os θ) = wkSub (idEmb θ) ,- (var ⇑ os oe)
idEmb (o' θ) = wkSub (idEmb θ)

id-emb-pres : ∀ {sup Δ}(θ : sup ⊑ Δ)(Ψ : Cx Δ) → WtSub (idEmb θ) (rest θ Ψ) Ψ
id-emb-pres oz     ε        = []
id-emb-pres (os θ) (Ψ ,- A) = _,-_ {u = var ⇑ os oe} (wkSub-pres (id-emb-pres θ Ψ)) (⊢fresh {Ψ = Ψ})
id-emb-pres (o' θ) (Ψ ,- A) = wkSub-pres (id-emb-pres θ Ψ)

-- the β-environment is well-typed: identity on the function's free vars, arg on
-- the bound var.  No subst — splitL/splitR are rest∘thin definitionally.
β-env-pres : ∀ {sₗ sᵣ Γ}{Φ : Cx Γ}{a : Tm sᵣ}{A}(cv : Cover sₗ sᵣ Γ)
  → splitR cv Φ ⊢ a ∶ A → WtSub (idEmb (thinL cv) ,- (a ⇑ thinR cv)) (splitL cv Φ ,- A) Φ
β-env-pres {Φ = Φ} {a = a} cv ⊢a = _,-_ {u = a ⇑ thinR cv} (id-emb-pres (thinL cv) Φ) ⊢a

-- single-step β (head redex).  Contractum support may shrink, hence Tm ↑ Γ.
data _⟶_ : ∀ {Γ} → Tm Γ → Tm ↑ Γ → Set where
  β  : ∀ {Γ sₗ sᵣ}{t : Tm (tt ∷ sₗ)}{a : Tm sᵣ}{cv : Cover sₗ sᵣ Γ}
     → app (pair (lam (use t))  a cv) ⟶ sub t (idEmb (thinL cv) ,- (a ⇑ thinR cv))
  βᵈ : ∀ {Γ sₗ sᵣ}{t : Tm sₗ}{a : Tm sᵣ}{cv : Cover sₗ sᵣ Γ}
     → app (pair (lam (drop t)) a cv) ⟶ sub t (idEmb (thinL cv))
infix 3 _⟶_

-- SUBJECT REDUCTION
preserve : ∀ {Γ}{Φ : Cx Γ}{e}{e′}{A} → Φ ⊢ e ∶ A → e ⟶ e′ → Φ ⊢↑ e′ ∶ A
preserve         (⊢app {cv = cv} (⊢lamᵘ ⊢t) ⊢a) β  = sub-pres (β-env-pres cv ⊢a) ⊢t
preserve {Φ = Φ} (⊢app {cv = cv} (⊢lamᵈ ⊢t) ⊢a) βᵈ = sub-pres (id-emb-pres (thinL cv) Φ) ⊢t
