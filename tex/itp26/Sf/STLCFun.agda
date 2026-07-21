{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.STLCFun — PROTOTYPE: substitutions as FUNCTIONS (one canonical cons, no
-- duplicate `,-`/`∙`).  Goal: show the spine/completion laws that plagued the
-- data representation (wk-↾, selL-cop) become trivial — pointwise `refl` or a
-- thinning-level fact (Fac-L) — because restriction/selection are PREcomposition
-- and weakening is POSTcomposition, so they associate definitionally.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.STLCFun where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Sf.Scaffold ⊤
open import Sf.Fac ⊤
open import Sf.STLC using (Tm; var; app; lam; app↑; lam↑)

-- a position in Γ = a singleton thinning that picks one slot
Pos : Scope → Set
Pos Γ = (tt ∷ []) ⊑ Γ

-- FUNCTIONAL substitution: each position ↦ a thing-with-thinning.  No `,-`.
FSub : Scope → Scope → Set
FSub Δ Γ = Pos Γ → Tm ↑ Δ

-- restriction = PREcompose the position with the thinning
_↾_ : ∀ {Δ sup Γ} → FSub Δ Γ → sup ⊑ Γ → FSub Δ sup
(σ ↾ θ) p = σ (p ⨾ θ)
infixl 8 _↾_

-- cover-selection = restriction along the cover-thinning (also PREcompose)
selL : ∀ {Γₗ Γᵣ Γ Δ} → Cover Γₗ Γᵣ Γ → FSub Δ Γ → FSub Δ Γₗ
selL cv σ = σ ↾ thinL cv

-- weakening = POSTcompose the RESULT with renaming
wkSub : ∀ {Δ Γ} → FSub Δ Γ → FSub (tt ∷ Δ) Γ
wkSub σ p = (σ p) ⟨ o' oi ⟩

-- the ONE cons: dispatch on the position (os = head, o' = tail)
_∙_ : ∀ {Δ Γ} → Tm ↑ Δ → FSub Δ Γ → FSub Δ (tt ∷ Γ)
(u ∙ σ) (os p) = u
(u ∙ σ) (o' p) = σ p
infixr 5 _∙_

-- identity: the position IS the var's embedding
idS : ∀ {Γ} → FSub Γ Γ
idS p = var ⇑ p

-- ════════════════════════════════════════════════════════════════════════════
-- PAYOFF.  The laws that needed opacity gymnastics + completions in the data
-- representation are now immediate.
-- ════════════════════════════════════════════════════════════════════════════

-- (1) wk-↾ : POINTWISE REFL.  (wkSub σ ↾ θ) p = (σ(p⨾θ))⟨o'oi⟩ = wkSub(σ↾θ) p.
--     Both sides build the SAME `p ⨾ θ`, so no opacity/completion/race.
wk-↾ : ∀ {Δ sup Γ}(σ : FSub Δ Γ)(θ : sup ⊑ Γ)(p : Pos sup)
     → (wkSub σ ↾ θ) p ≡ wkSub (σ ↾ θ) p
wk-↾ σ θ p = refl

-- (2) selL-cop : reduces to the THINNING fact Fac-L (which is already a rewrite),
--     not a Sub-level recursion + completion.
selL-cop : ∀ {sₗ sᵣ Δ Θ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(τ : FSub Θ Δ)(p : Pos sₗ)
         → selL (cov (cop θ φ)) (τ ↾ out (cop θ φ)) p ≡ (τ ↾ θ) p
selL-cop θ φ τ p = cong (λ x → τ (p ⨾ x)) (Fac-L θ φ)

-- (3) VarCons : the fresh-var position hits the head — REFL.
varCons : ∀ {Δ Γ}(u : Tm ↑ Δ)(σ : FSub Δ Γ) → (u ∙ σ) (os oe) ≡ u
varCons u σ = refl

-- (4) ShiftCons : ↑ₛ ⨟ (u ∙ σ) ... here directly: the tail of a cons is σ — REFL.
shiftTail : ∀ {Δ Γ}(u : Tm ↑ Δ)(σ : FSub Δ Γ)(p : Pos Γ) → (u ∙ σ) (o' p) ≡ σ p
shiftTail u σ p = refl

-- ════════════════════════════════════════════════════════════════════════════
-- THE σ-CALCULUS ACTION on functional Sub (cf. Sf.SystemF / Sf.STLC `sub`).
-- ════════════════════════════════════════════════════════════════════════════
selR : ∀ {Γₗ Γᵣ Γ Δ} → Cover Γₗ Γᵣ Γ → FSub Δ Γ → FSub Δ Γᵣ
selR cv σ = σ ↾ thinR cv

var₀ : ∀ {Δ} → Tm ↑ (tt ∷ Δ)
var₀ = var ⇑ os oe

-- binder lift: position 0 ↦ var₀, rest ↦ weakened σ.  No `,-`, no `wkSub` race.
lift : ∀ {Δ Γ} → FSub Δ Γ → FSub (tt ∷ Δ) (tt ∷ Γ)
lift σ = var₀ ∙ wkSub σ

-- the action recurses on the TERM; the lift builds a Sub with NO sub-call (wkSub
-- only postcomposes a renaming), so termination is structural — the very thing
-- the data `σ ⨟ ↑ₛ` reroute could not achieve.
sub : ∀ {Γ Δ} → Tm Γ → FSub Δ Γ → Tm ↑ Δ
sub var                 σ = σ (os oz)
sub (app (pair l r cv)) σ = app↑ (sub l (selL cv σ)) (sub r (selR cv σ))
sub (lam (use t))       σ = lam↑ (sub t (lift σ))
sub (lam (drop t))      σ = lam <$> (drop <$> sub t σ)

_⟪_⟫ : ∀ {Δ Θ} → Tm ↑ Δ → FSub Θ Δ → Tm ↑ Θ
(t ⇑ θ) ⟪ σ ⟫ = sub t (σ ↾ θ)
infixl 8 _⟪_⟫

-- composition = Kleisli (pointwise apply ⟪⟫).  Associative by ∘-assoc.
_⨟_ : ∀ {Γ Δ Θ} → FSub Δ Γ → FSub Θ Δ → FSub Θ Γ
(σ ⨟ τ) p = (σ p) ⟪ τ ⟫
infixl 6 _⨟_

-- ════ HONEST LIMIT: ⨟ does NOT associate for free.  It is KLEISLI composition
-- ((σ⨟τ) p = (σ p)⟪τ⟫), so Ass reduces to the FUSION law (u⟪τ⟫)⟪υ⟫ ≡ u⟪τ⨟υ⟫,
-- which recurses on the TERM — same term-induction as the data representation.
-- So: functional Sub frees the SPINE laws (wk-↾/selL-cop above, the completion
-- explosion), but the ACTION laws (fusion/assoc/IdSubst) are UNCHANGED.  Stated,
-- not proved-by-refl:
Ass-needs-fusion : ∀ {Γ Δ Δ′ Θ}(σ : FSub Δ Γ)(τ : FSub Δ′ Δ)(υ : FSub Θ Δ′)(p : Pos Γ)
    → ((σ ⨟ τ) ⨟ υ) p ≡ ((σ p) ⟪ τ ⟫) ⟪ υ ⟫     -- LHS just unfolds; RHS still needs Clos to reach (σ⨟(τ⨟υ)) p
Ass-needs-fusion σ τ υ p = refl

-- NOTE on VarCons (`var₀ ⟪ u ∙ σ ⟫ ≡ u`): the fresh-var lookup routes through the
-- POSITION `os oz ⨾ os oe`, and `⨾` is OPAQUE so the cons can't dispatch until the
-- structural rule `os a ⨾ os b ≡ os (a⨾b)` reduces it.  So positions-as-thinnings
-- need the structural-⨾ rules registered to make the cons compute — a thinning-level
-- completion (no funext).  That's the concrete next item for the action laws.

-- ════════════════════════════════════════════════════════════════════════════
-- η-LAWS via funext (the user's point: the PROOF doesn't matter — once registered
-- as a rewrite it fires on syntactic match; funext is a mild consistent axiom).
-- ════════════════════════════════════════════════════════════════════════════
postulate funext : ∀ {a b}{A : Set a}{B : Set b}{f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

-- the σ_SP shift, functionally: weaken every position by o'
↑ₛ : ∀ {Γ} → FSub (tt ∷ Γ) Γ
↑ₛ p = var ⇑ o' p

-- []⊑Γ is unique (so the head of ↑ₛ-cons lands on var₀'s embedding)
opaque
  unfolding oe
  oe-uniq : ∀ {Γ}(p : (tt ∷ []) ⊑ (tt ∷ Γ)) → ∀ {q : [] ⊑ Γ} → p ≡ os q → p ≡ os oe
  oe-uniq .(os q) {q} refl = cong os (go q)
    where go : ∀ {Γ}(r : [] ⊑ Γ) → r ≡ oe
          go {[]}    oz     = refl
          go {_ ∷ Γ} (o' r) = cong o' (go r)

-- IdCons : var₀ ∙ ↑ₛ ≡ idS  — proven pointwise + funext.  Head needs oe-uniqueness,
-- tail is refl.  This is the law that was "blocked" on the data rep; here it's routine.
IdCons : ∀ {Γ} → (var₀ ∙ ↑ₛ) ≡ idS {tt ∷ Γ}
IdCons = funext go
  where go : ∀ {Γ}(p : (tt ∷ []) ⊑ (tt ∷ Γ)) → (var₀ ∙ ↑ₛ) p ≡ idS p
        go (os q) = cong (λ z → var ⇑ os z) (sym (oe-uniqℓ q))
          where opaque
                  unfolding oe
                  oe-uniqℓ : ∀ {Γ}(r : [] ⊑ Γ) → r ≡ oe
                  oe-uniqℓ {[]} oz = refl
                  oe-uniqℓ {_ ∷ Γ} (o' r) = cong o' (oe-uniqℓ r)
        go (o' q) = refl
