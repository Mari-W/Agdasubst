{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.SystemFTyping — extrinsic typing + CALL-BY-VALUE SUBJECT REDUCTION for
-- co-de-Bruijn System F, on the "OPTION A" FULL-CONTEXT scheme.
--
-- The context `Cx Δ` is a FULL telescope over the WHOLE scope Δ — it is never
-- restricted.  Each tm-var's classifier is a `Ty ↑` over its PREFIX; `lookup`
-- WEAKENS it up to Δ (pure thinning composition, total, distributive).  The
-- judgement carries a thinning:  `Φ ⊢[ θ ] t ∶ A`  with  Φ : Cx Δ, t over its
-- support `sup`, θ : sup ⊑ Δ, A : Ty ↑ Δ.  Types only ever WEAKEN — never
-- restrict — so the old `_⇂_` / `factor` / `junkTy` re-base blocker (a tm-var's
-- type escaping its scope) simply cannot arise.  No `rest`, no `cohL/cohR`.
--
-- The SR proof is SUBST-FREE: no `Relation.…PropositionalEquality.subst`, no
-- manual substitution lemmas — every σ-law and every thinning law fires as a
-- registered rewrite (the σ-engine of Sf.SystemF, plus Sf.Fac's Fac-L/Fac-R),
-- so the proof terms are the bare typed smart-constructors.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.SystemFTyping where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sf.SystemF
-- the coproduct injection-factorisation rewrites (Fac-L/Fac-R/…) for I = Sort.
-- `thinL`/`thinR` here are Sf.Thin's opaque cover-thinnings, the SAME ones the
-- σ-engine and the judgement use — Fac fires on `thinL cv ⨾ out (cop θ φ)`.
open import Sf.Fac Sort public
-- the SUBSTITUTION coherence (selL-cop/selR-cop + the cop-unit completion) as
-- rewrites.  With these, substitution distributes over the ARROW former
-- DEFINITIONALLY:  `(A ⇒↑ B) ⟪ σ ⟫ ≡ (A ⟪ σ ⟫) ⇒↑ (B ⟪ σ ⟫)` holds by `refl`
-- (verified).  The ∀ former is NOT definitional — its distribution `⟪⟫-∀`
-- intrinsically needs `wk-↾`/`sub-wk`, neither of which is a confluent rewrite
-- (`wk-↾` races `↾-oe`), so it stays the single propositional bridge `∀↑-dist`.
open import Sf.SystemFCoh

-- ════════════════════════════════════════════════════════════════════════════
-- CONTEXTS — a FULL telescope over the whole scope.  A tm-var's classifier is a
-- `Ty ↑ Γ` over its PREFIX Γ (System F's context is dependent: a tm-var's type
-- mentions the ty-vars before it).  A ty-var carries a trivial classifier
-- (System F = one kind), so `,*` stores nothing.
-- ════════════════════════════════════════════════════════════════════════════
data Cx : Scope → Set where
  ε    : Cx []
  _,*  : ∀ {Γ} → Cx Γ → Cx (ty ∷ Γ)
  _,-_ : ∀ {Γ} → Cx Γ → (Ty ↑ Γ) → Cx (tm ∷ Γ)
infixl 5 _,-_
infixl 5 _,*
variable Φ Ψ : Cx Γ

-- ── LOOKUP.  `lookup Φ θ` with θ : (tm ∷ []) ⊑ Δ singles out one tm-var and
-- returns its stored classifier WEAKENED up to the full Δ (pure `wk↑`, i.e. `o'`
-- on the thinning — no traversal).  Total; ty-binders on the path are skipped
-- (their classifier is trivial). ──
lookup : ∀ {Δ} → Cx Δ → (tm ∷ []) ⊑ Δ → Ty ↑ Δ
lookup (Φ ,- A) (os θ) = wk↑ tm A
lookup (Φ ,- A) (o' θ) = wk↑ tm (lookup Φ θ)
lookup (Φ ,*)   (o' θ) = wk↑ ty (lookup Φ θ)

-- ════════════════════════════════════════════════════════════════════════════
-- TYPE-FORMERS as smart constructors over things-with-thinnings (merge supports).
-- ════════════════════════════════════════════════════════════════════════════
_⇒↑_ : ∀ {Δ} → Ty ↑ Δ → Ty ↑ Δ → Ty ↑ Δ
A ⇒↑ B = _`→_ <$> pairUp A B
infixr 5 _⇒↑_
∀↑ : ∀ {Δ} → Ty ↑ (ty ∷ Δ) → Ty ↑ Δ
∀↑ X = `∀ <$> bindUp X

-- ── ARROW INJECTIVITY.  `_⇒↑_` is a defined function (merge-then-`<$>`), so it is
-- NOT a constructor and unification cannot invert it.  But the two components are
-- RECOVERABLE: `domOf`/`codOf` peel the cover's two side-thinnings, and Fac-L/Fac-R
-- (Sf.Fac) collapse `thinL/thinR (cov (cop θ φ)) ⨾ out (cop θ φ)` to θ/φ, so on a
-- real arrow the projections compute by `refl`.  This gives propositional
-- injectivity — exactly what inverting a `⊢lamᵘ` against the `⊢app` arrow needs. ──
open import Relation.Binary.PropositionalEquality using (cong) renaming (trans to ≡-trans; sym to ≡-sym)
domOf : ∀ {Δ} → Ty ↑ Δ → Ty ↑ Δ
domOf (_`→_ (pair a b cv) ⇑ θ) = a ⇑ (thinL cv ⨾ θ)
domOf X = X
codOf : ∀ {Δ} → Ty ↑ Δ → Ty ↑ Δ
codOf (_`→_ (pair a b cv) ⇑ θ) = b ⇑ (thinR cv ⨾ θ)
codOf X = X
-- on a genuine arrow the projections compute (Fac-L/Fac-R), so these are `refl`.
domOf-⇒↑ : ∀ {Δ}(A B : Ty ↑ Δ) → domOf (A ⇒↑ B) ≡ A
domOf-⇒↑ A B = refl
codOf-⇒↑ : ∀ {Δ}(A B : Ty ↑ Δ) → codOf (A ⇒↑ B) ≡ B
codOf-⇒↑ A B = refl
⇒↑-injˡ : ∀ {Δ}{A B A′ B′ : Ty ↑ Δ} → (A ⇒↑ B) ≡ (A′ ⇒↑ B′) → A ≡ A′
⇒↑-injˡ {A = A}{B}{A′}{B′} eq = ≡-trans (≡-sym (domOf-⇒↑ A B)) (≡-trans (cong domOf eq) (domOf-⇒↑ A′ B′))
⇒↑-injʳ : ∀ {Δ}{A B A′ B′ : Ty ↑ Δ} → (A ⇒↑ B) ≡ (A′ ⇒↑ B′) → B ≡ B′
⇒↑-injʳ {A = A}{B}{A′}{B′} eq = ≡-trans (≡-sym (codOf-⇒↑ A B)) (≡-trans (cong codOf eq) (codOf-⇒↑ A′ B′))
-- ∀↑ injectivity, same idea: `bodyOf` peels the binder (use/drop ↦ os/o').
bodyOf : ∀ {Δ} → Ty ↑ Δ → Ty ↑ (ty ∷ Δ)
bodyOf (`∀ (use t)  ⇑ θ) = t ⇑ os θ
bodyOf (`∀ (drop t) ⇑ θ) = t ⇑ o' θ
bodyOf (a ⇑ θ) = wk↑ ty (a ⇑ θ)
bodyOf-∀↑ : ∀ {Δ}(B : Ty ↑ (ty ∷ Δ)) → bodyOf (∀↑ B) ≡ B
bodyOf-∀↑ (t ⇑ os θ) = refl
bodyOf-∀↑ (t ⇑ o' θ) = refl
∀↑-inj : ∀ {Δ}{B B′ : Ty ↑ (ty ∷ Δ)} → (∀↑ B) ≡ (∀↑ B′) → B ≡ B′
∀↑-inj {B = B}{B′} eq = ≡-trans (≡-sym (bodyOf-∀↑ B)) (≡-trans (cong bodyOf eq) (bodyOf-∀↑ B′))

-- ════════════════════════════════════════════════════════════════════════════
-- THE TYPING JUDGEMENT  `Φ ⊢[ θ ] t ∶ A`.
--   Φ : Cx Δ   (full context),   t : Exp sup tm   (term over its support),
--   θ : sup ⊑ Δ   (support into the full scope),   A : Ty ↑ Δ   (type over Δ).
-- Every subterm-thinning is just `thinL cv ⨾ θ` / `thinR cv ⨾ θ` — no restriction.
-- ════════════════════════════════════════════════════════════════════════════
data _⊢[_]_∶_ : ∀ {sup Δ} → Cx Δ → sup ⊑ Δ → Tm sup → Ty ↑ Δ → Set where
  -- the sole tm-var: its type is the (weakened) stored classifier, looked up at θ.
  ⊢var : ∀ {Δ}{Φ : Cx Δ}{θ : (tm ∷ []) ⊑ Δ}
       → Φ ⊢[ θ ] var ∶ lookup Φ θ
  -- application: just thinning composition through the cover.
  ⊢app : ∀ {sₗ sᵣ sup Δ}{Φ : Cx Δ}{l : Tm sₗ}{r : Tm sᵣ}{cv : Cover sₗ sᵣ sup}
           {θ : sup ⊑ Δ}{A B : Ty ↑ Δ}
       → Φ ⊢[ thinL cv ⨾ θ ] l ∶ (A ⇒↑ B)
       → Φ ⊢[ thinR cv ⨾ θ ] r ∶ A
       → Φ ⊢[ θ ] `app (pair l r cv) ∶ B
  -- λ(x:a).body.  The domain `a` is a Ty-subterm split off by the cover; its type
  -- over Δ is `a ⇑ (thinL cv ⨾ θ)`.  use/drop read whether the bound var survives.
  ⊢lamᵘ : ∀ {sₐ sᵦ sup Δ}{Φ : Cx Δ}{a : Ty sₐ}{body : Tm (tm ∷ sᵦ)}
            {cv : Cover sₐ sᵦ sup}{θ : sup ⊑ Δ}{B : Ty ↑ Δ}
        → (Φ ,- (a ⇑ (thinL cv ⨾ θ))) ⊢[ os (thinR cv ⨾ θ) ] body ∶ wk↑ tm B
        → Φ ⊢[ θ ] `lam (pair a (use body) cv) ∶ ((a ⇑ (thinL cv ⨾ θ)) ⇒↑ B)
  -- the drop body is typed in the SAME extended context with the weakened type
  -- (the bound var is simply absent — thinning head `o'`).  This makes use/drop
  -- uniform, so `⊢lam↑` is definitional.
  ⊢lamᵈ : ∀ {sₐ sᵦ sup Δ}{Φ : Cx Δ}{a : Ty sₐ}{body : Tm sᵦ}
            {cv : Cover sₐ sᵦ sup}{θ : sup ⊑ Δ}{B : Ty ↑ Δ}
        → (Φ ,- (a ⇑ (thinL cv ⨾ θ))) ⊢[ o' (thinR cv ⨾ θ) ] body ∶ wk↑ tm B
        → Φ ⊢[ θ ] `lam (pair a (drop body) cv) ∶ ((a ⇑ (thinL cv ⨾ θ)) ⇒↑ B)
  -- Λα.body (binds a ty-var).  Body typed under `Φ ,*`; result type `∀ B`.
  ⊢Lamᵘ : ∀ {sup Δ}{Φ : Cx Δ}{body : Tm (ty ∷ sup)}{θ : sup ⊑ Δ}{B : Ty ↑ (ty ∷ Δ)}
        → (Φ ,*) ⊢[ os θ ] body ∶ B
        → Φ ⊢[ θ ] `Lam (use body) ∶ ∀↑ B
  ⊢Lamᵈ : ∀ {sup Δ}{Φ : Cx Δ}{body : Tm sup}{θ : sup ⊑ Δ}{B : Ty ↑ (ty ∷ Δ)}
        → (Φ ,*) ⊢[ o' θ ] body ∶ B
        → Φ ⊢[ θ ] `Lam (drop body) ∶ ∀↑ B
  -- e[a] (type application).  e : ∀ B (B : Ty ↑ (ty ∷ Δ)); result B[a/α] via the
  -- uniform `_⟪_⟫` against the env mapping the bound ty-var to `a` over Δ.
  ⊢App : ∀ {sₑ sₐ sup Δ}{Φ : Cx Δ}{e : Tm sₑ}{a : Ty sₐ}{cv : Cover sₑ sₐ sup}
           {θ : sup ⊑ Δ}{B : Ty ↑ (ty ∷ Δ)}
       → Φ ⊢[ thinL cv ⨾ θ ] e ∶ ∀↑ B
       → Φ ⊢[ θ ] `App (pair e a cv) ∶ (B ⟪ idS ,- (a ⇑ (thinR cv ⨾ θ)) ⟫)
infix 4 _⊢[_]_∶_

-- ════════════════════════════════════════════════════════════════════════════
-- typing of a thing-with-thinning: `Φ ⊢↑ (t ⇑ θ) ∶ A` := `Φ ⊢[ θ ] t ∶ A`.
-- No restriction, no re-base — Φ and A stay over the full Δ.
-- ════════════════════════════════════════════════════════════════════════════
_⊢↑_∶_ : ∀ {Δ} → Cx Δ → Tm ↑ Δ → Ty ↑ Δ → Set
Φ ⊢↑ (t ⇑ θ) ∶ A = Φ ⊢[ θ ] t ∶ A
infix 4 _⊢↑_∶_

-- ════════════════════════════════════════════════════════════════════════════
-- TERM-level smart constructors (Sf.SystemF does not export them).
-- ════════════════════════════════════════════════════════════════════════════
app↑ : ∀ {Δ} → Tm ↑ Δ → Tm ↑ Δ → Tm ↑ Δ
app↑ l r = `app <$> pairUp l r
lam↑ : ∀ {Δ} → Ty ↑ Δ → Tm ↑ (tm ∷ Δ) → Tm ↑ Δ
lam↑ A body = `lam <$> pairUp A (bindUp body)
Lam↑ : ∀ {Δ} → Tm ↑ (ty ∷ Δ) → Tm ↑ Δ
Lam↑ body = `Lam <$> bindUp body
App↑ : ∀ {Δ} → Tm ↑ Δ → Ty ↑ Δ → Tm ↑ Δ
App↑ e A = `App <$> pairUp e A

-- ── TYPED smart-constructors.  All DEFINITIONAL: Fac-L/Fac-R fire as rewrites,
-- so `thinL (cov (cop θ φ)) ⨾ out (cop θ φ) ≡ θ` definitionally — no coherence. ──
⊢app↑ : ∀ {Δ}{Ψ : Cx Δ}{A B : Ty ↑ Δ}(l′ r′ : Tm ↑ Δ)
      → Ψ ⊢↑ l′ ∶ (A ⇒↑ B) → Ψ ⊢↑ r′ ∶ A → Ψ ⊢↑ (app↑ l′ r′) ∶ B
⊢app↑ (l ⇑ θ) (r ⇑ φ) ⊢l ⊢r = ⊢app {cv = cov (cop θ φ)} ⊢l ⊢r

-- typed smart-lam: read the body's thinning (use/drop) — body EXPLICIT so an
-- abstract body is a stuck neutral whose type is exactly the goal.
⊢lam↑ : ∀ {sₐ Δ}{Ψ : Cx Δ}{B : Ty ↑ Δ}(a : Ty sₐ)(α : sₐ ⊑ Δ)(body : Tm ↑ (tm ∷ Δ))
      → (Ψ ,- (a ⇑ α)) ⊢↑ body ∶ wk↑ tm B → Ψ ⊢↑ (lam↑ (a ⇑ α) body) ∶ ((a ⇑ α) ⇒↑ B)
⊢lam↑ a α (t ⇑ os θ) ⊢t = ⊢lamᵘ ⊢t
⊢lam↑ a α (t ⇑ o' θ) ⊢t = ⊢lamᵈ ⊢t

-- typed smart-Lam.
⊢Lam↑ : ∀ {Δ}{Ψ : Cx Δ}{B : Ty ↑ (ty ∷ Δ)}(body : Tm ↑ (ty ∷ Δ))
      → (Ψ ,*) ⊢↑ body ∶ B → Ψ ⊢↑ (Lam↑ body) ∶ ∀↑ B
⊢Lam↑ (t ⇑ os θ) ⊢t = ⊢Lamᵘ ⊢t
⊢Lam↑ (t ⇑ o' θ) ⊢t = ⊢Lamᵈ ⊢t

-- typed smart-App.  DEFINITIONAL: Fac-L/Fac-R make `thinL/thinR (cov (cop θ φ)) ⨾
-- out (cop θ φ)` collapse to θ/φ, so the result type is `B ⟪ idS ,- a′ ⟫`.
⊢App↑ : ∀ {Δ}{Ψ : Cx Δ}(B : Ty ↑ (ty ∷ Δ))(e′ : Tm ↑ Δ)(a′ : Ty ↑ Δ)
      → Ψ ⊢↑ e′ ∶ ∀↑ B → Ψ ⊢↑ (App↑ e′ a′) ∶ (B ⟪ idS ,- a′ ⟫)
⊢App↑ B (e ⇑ θ) (a ⇑ φ) ⊢e = ⊢App {a = a}{cv = cov (cop θ φ)}{B = B} ⊢e

-- ════════════════════════════════════════════════════════════════════════════
-- WELL-TYPED SUBSTITUTION.  `WtSub σ Φ Ψ`: σ : Sub Δ Γ maps each Γ-variable's
-- classifier (moved BY THE SAME σ, via `_⟪_⟫`) to a typed Ψ-term.  ty-vars carry
-- no classifier, so `,*` just records a typed entry (the ty-var image — always a
-- type, never observed by typing, so we only thread the spine).
-- ════════════════════════════════════════════════════════════════════════════
data WtSub : ∀ {Γ Δ} → Sub Δ Γ → Cx Γ → Cx Δ → Set where
  []   : ∀ {Δ}{Ψ : Cx Δ} → WtSub [] ε Ψ
  _,*  : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{u : Ty ↑ Δ}
       → WtSub σ Φ Ψ → WtSub (σ ,- u) (Φ ,*) Ψ
  _,-_ : ∀ {Γ Δ}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{u : Tm ↑ Δ}{A : Ty ↑ Γ}
       → WtSub σ Φ Ψ → Ψ ⊢↑ u ∶ (A ⟪ σ ⟫) → WtSub (σ ,- u) (Φ ,- A) Ψ

-- ════════════════════════════════════════════════════════════════════════════
-- SPINE: `selL`/`selR` of a restricted σ = restrict by the cover-thinned θ.  Pure
-- structural recursion on the cover (which drives how θ/σ peel); `thinL`/`thinR`
-- unfold inside the block.  Registered as rewrites so the `⊢app`/`⊢App` IHs land
-- on the nose: `sub l (selL cv (σ ↾ θ)) ≡ sub l (σ ↾ (thinL cv ⨾ θ))`.
-- ════════════════════════════════════════════════════════════════════════════
open import Relation.Binary.PropositionalEquality using (refl; cong)
opaque
  unfolding thinL thinR oi _⨾_
  -- the empty-cover base: selecting an empty cover-side of a fully-peeled σ.
  sel-czz : ∀ {Δ Δ′}(θ : [] ⊑ Δ)(σ : Sub Δ′ Δ) → selL czz (σ ↾ θ) ≡ σ ↾ (oz ⨾ θ)
  sel-czz oz     []       = refl
  sel-czz (o' θ) (σ ,- u) = sel-czz θ σ
  selL-↾ : ∀ {sₗ sᵣ sup Δ Δ′}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ)(σ : Sub Δ′ Δ)
         → selL cv (σ ↾ θ) ≡ σ ↾ (thinL cv ⨾ θ)
  selL-↾ czz     θ      σ        = sel-czz θ σ
  selL-↾ (css c) (os θ) (σ ,- u) = cong (_,- u) (selL-↾ c θ σ)
  selL-↾ (css c) (o' θ) (σ ,- u) = selL-↾ (css c) θ σ
  selL-↾ (cs' c) (os θ) (σ ,- u) = cong (_,- u) (selL-↾ c θ σ)
  selL-↾ (cs' c) (o' θ) (σ ,- u) = selL-↾ (cs' c) θ σ
  selL-↾ (c's c) (os θ) (σ ,- u) = selL-↾ c θ σ
  selL-↾ (c's c) (o' θ) (σ ,- u) = selL-↾ (c's c) θ σ
  sel-czzR : ∀ {Δ Δ′}(θ : [] ⊑ Δ)(σ : Sub Δ′ Δ) → selR czz (σ ↾ θ) ≡ σ ↾ (oz ⨾ θ)
  sel-czzR oz     []       = refl
  sel-czzR (o' θ) (σ ,- u) = sel-czzR θ σ
  selR-↾ : ∀ {sₗ sᵣ sup Δ Δ′}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ)(σ : Sub Δ′ Δ)
         → selR cv (σ ↾ θ) ≡ σ ↾ (thinR cv ⨾ θ)
  selR-↾ czz     θ      σ        = sel-czzR θ σ
  selR-↾ (css c) (os θ) (σ ,- u) = cong (_,- u) (selR-↾ c θ σ)
  selR-↾ (css c) (o' θ) (σ ,- u) = selR-↾ (css c) θ σ
  selR-↾ (cs' c) (os θ) (σ ,- u) = selR-↾ c θ σ
  selR-↾ (cs' c) (o' θ) (σ ,- u) = selR-↾ (cs' c) θ σ
  selR-↾ (c's c) (os θ) (σ ,- u) = cong (_,- u) (selR-↾ c θ σ)
  selR-↾ (c's c) (o' θ) (σ ,- u) = selR-↾ (c's c) θ σ
-- NOT registered as rewrites (they race the `_↾_` clauses / `↾-oe`).  Used only to
-- transport WtSub along a cover-split: `selL-pres`/`selR-pres` below.

-- ════════════════════════════════════════════════════════════════════════════
-- DECOUPLED WELL-TYPED SUBSTITUTION  `WtS θ τ σ Φ Ψ`.
--
-- The crux of co-de-Bruijn SR is that the confluence-delicate identity
-- `selL cv (σ ↾ θ) ≡ σ ↾ (thinL cv ⨾ θ)` cannot be a global rewrite.  We avoid
-- it by DECOUPLING the term-substitution from the type-substitution:
--   • `τ : Sub Δ sup`  — the substitution the TERM is `sub`'d by (over its
--     support `sup`); it gets `selL cv`/`selR cv`'d STRUCTURALLY, exactly as the
--     `sub` clauses do, so the IHs land definitionally (no `_↾_`).
--   • `σ : Sub Δ Γ`   — the FULL substitution the TYPES move by (`A ⟪ σ ⟫`).
--     Types may mention ty-vars outside the term's support, so they need the
--     full σ; σ is THREADED UNCHANGED through `selL-pres`/`selR-pres`.
--   • `θ : sup ⊑ Γ`    — ties them together; the invariant is `τ = σ ↾ θ`.
-- Per sup-variable selected by θ, its τ-entry must be a typed Ψ-term at the
-- σ-moved classifier read from Φ.  ty-vars carry no classifier.
-- ════════════════════════════════════════════════════════════════════════════
data WtS : ∀ {sup Γ Δ} → sup ⊑ Γ → Sub Δ sup → Sub Δ Γ → Cx Γ → Cx Δ → Set where
  []   : ∀ {Δ}{Ψ : Cx Δ} → WtS oz [] [] ε Ψ
  -- ty-var IN the support (os): τ and σ share the entry u.
  _,*ˢ : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{u : Ty ↑ Δ}
       → WtS θ τ σ Φ Ψ → WtS (os θ) (τ ,- u) (σ ,- u) (Φ ,*) Ψ
  -- ty-var DROPPED (o'): only σ carries the entry.
  _,*ᵈ : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{u : Ty ↑ Δ}
       → WtS θ τ σ Φ Ψ → WtS (o' θ) τ (σ ,- u) (Φ ,*) Ψ
  -- tm-var IN the support: τ and σ share the (typed) entry u.
  _,-ˢ_ : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{u : Tm ↑ Δ}{A : Ty ↑ Γ}
        → WtS θ τ σ Φ Ψ → Ψ ⊢↑ u ∶ (A ⟪ σ ⟫) → WtS (os θ) (τ ,- u) (σ ,- u) (Φ ,- A) Ψ
  -- tm-var DROPPED: only σ carries the entry.  NO typing requirement — a dropped
  -- tm-var never appears in any type (types mention only ty-vars), so its σ-image
  -- is irrelevant.  (A typed `,-ᵈ` would be unprovable when its classifier is
  -- uninhabited, yet the drop case of `subB` genuinely produces such an entry.)
  _,-ᵈ : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{u : Tm ↑ Δ}{A : Ty ↑ Γ}
       → WtS θ τ σ Φ Ψ → WtS (o' θ) τ (σ ,- u) (Φ ,- A) Ψ
infixl 5 _,*ˢ _,*ᵈ _,-ᵈ
infixl 5 _,-ˢ_

-- ── COVER-SPLIT preserves WtS.  Both τ and θ peel by the cover (DEFINITIONAL:
-- `selL cv τ` matches `sub`'s peeling, `thinL cv ⨾ θ` unfolds in the block); σ is
-- threaded UNCHANGED.  A `c's` (resp `cs'`) clause moves a support-var to the
-- dropped side, turning `,-ˢ`/`,*ˢ` into `,-ᵈ`/`,*ᵈ`. ──
opaque
  unfolding thinL thinR oi _⨾_
  selL-pres : ∀ {sₗ sᵣ sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
            → (cv : Cover sₗ sᵣ sup) → WtS θ τ σ Φ Ψ → WtS (thinL cv ⨾ θ) (selL cv τ) σ Φ Ψ
  selL-pres czz     []         = []
  selL-pres cv      (w ,*ᵈ)    = selL-pres cv w ,*ᵈ
  selL-pres cv      (w ,-ᵈ)    = selL-pres cv w ,-ᵈ
  selL-pres (css c) (w ,*ˢ)    = selL-pres c w ,*ˢ
  selL-pres (cs' c) (w ,*ˢ)    = selL-pres c w ,*ˢ
  selL-pres (c's c) (w ,*ˢ)    = selL-pres c w ,*ᵈ
  selL-pres (css c) (w ,-ˢ ⊢u) = selL-pres c w ,-ˢ ⊢u
  selL-pres (cs' c) (w ,-ˢ ⊢u) = selL-pres c w ,-ˢ ⊢u
  selL-pres (c's c) (w ,-ˢ ⊢u) = selL-pres c w ,-ᵈ
  selR-pres : ∀ {sₗ sᵣ sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
            → (cv : Cover sₗ sᵣ sup) → WtS θ τ σ Φ Ψ → WtS (thinR cv ⨾ θ) (selR cv τ) σ Φ Ψ
  selR-pres czz     []         = []
  selR-pres cv      (w ,*ᵈ)    = selR-pres cv w ,*ᵈ
  selR-pres cv      (w ,-ᵈ)    = selR-pres cv w ,-ᵈ
  selR-pres (css c) (w ,*ˢ)    = selR-pres c w ,*ˢ
  selR-pres (cs' c) (w ,*ˢ)    = selR-pres c w ,*ᵈ
  selR-pres (c's c) (w ,*ˢ)    = selR-pres c w ,*ˢ
  selR-pres (css c) (w ,-ˢ ⊢u) = selR-pres c w ,-ˢ ⊢u
  selR-pres (cs' c) (w ,-ˢ ⊢u) = selR-pres c w ,-ᵈ
  selR-pres (c's c) (w ,-ˢ ⊢u) = selR-pres c w ,-ˢ ⊢u

-- the WtS INVARIANT (helper):  the term-substitution IS the restriction of the
-- full type-substitution.  Holds by construction; needed only to bridge the term
-- side `selL cv τ` to the type side `σ ↾ ρ` on the lam DOMAIN (a type IN a term).
open import Relation.Binary.PropositionalEquality using (cong)
wts-inv : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
        → WtS θ τ σ Φ Ψ → τ ≡ σ ↾ θ
wts-inv []         = refl
wts-inv (_,*ˢ {u = u} w) = cong (_,- u) (wts-inv w)
wts-inv (w ,*ᵈ)    = wts-inv w
wts-inv (_,-ˢ_ {u = u} w _) = cong (_,- u) (wts-inv w)
wts-inv (w ,-ᵈ)    = wts-inv w

-- ── ∀-DISTRIBUTION OVER SUBSTITUTION, the SINGLE propositional bridge.
-- The ARROW distribution `(A ⇒↑ B) ⟪ σ ⟫ ≡ (A ⟪ σ ⟫) ⇒↑ (B ⟪ σ ⟫)` is now
-- DEFINITIONAL (Sf.SystemFCoh's selL-cop/selR-cop rewrites + `unfolding _⟪_⟫`),
-- so it needs no transformer — `sub-pres` writes the arrow former directly.
-- The ∀ distribution `⟪⟫-∀` cannot be made a rewrite (it needs `wk-↾`/`sub-wk`,
-- and `wk-↾` races `↾-oe`), so it is the lone `subst`, packaged as a derivation
-- TRANSFORMER each way.  `sub-pres` stays a bare smart-constructor term. ──
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
∀↑-dist : ∀ {Δ Θ}{Ψ : Cx Θ}{e : Tm ↑ Θ}(B : Ty ↑ (ty ∷ Δ))(σ : Sub Θ Δ)
        → Ψ ⊢↑ e ∶ ((∀↑ B) ⟪ σ ⟫) → Ψ ⊢↑ e ∶ ∀↑ (B ⟪ wkSub σ ,- var₀ ⟫)
∀↑-dist {Ψ = Ψ}{e = e} B σ = subst (λ T → Ψ ⊢↑ e ∶ T) (⟪⟫-∀ B σ)
∀↑-undist : ∀ {Δ Θ}{Ψ : Cx Θ}{e : Tm ↑ Θ}(B : Ty ↑ (ty ∷ Δ))(σ : Sub Θ Δ)
          → Ψ ⊢↑ e ∶ ∀↑ (B ⟪ wkSub σ ,- var₀ ⟫) → Ψ ⊢↑ e ∶ ((∀↑ B) ⟪ σ ⟫)
∀↑-undist {Ψ = Ψ}{e = e} B σ = subst (λ T → Ψ ⊢↑ e ∶ T) (sym (⟪⟫-∀ B σ))

-- ════════════════════════════════════════════════════════════════════════════
-- CONTEXT RENAMING and the RENAMING-PRESERVES-TYPING lemma `⊢-ren`.  Option A's
-- full context means weakening is NOT free (unlike the restriction scheme), so we
-- need the renaming lemma to push a derivation along a thinning `ψ : Δ ⊑ Δ′`.
-- This is a HELPER (it may use subst/cong/trans); `sub-pres`/`preserve` and the
-- *-pres functions stay subst-free and only APPLY it.
-- ════════════════════════════════════════════════════════════════════════════
open import Relation.Binary.PropositionalEquality using (cong₂)

-- ── PURE-SPINE renaming/restriction lemmas (helper level). ──
-- thinSub commutes with restriction.
thinSub-↾ : ∀ {sup Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ)(φ : sup ⊑ Γ) → thinSub ψ σ ↾ φ ≡ thinSub ψ (σ ↾ φ)
thinSub-↾ ψ []       oz     = refl
thinSub-↾ ψ (σ ,- u) (os φ) = cong (_,- (u ⟨ ψ ⟩)) (thinSub-↾ ψ σ φ)
thinSub-↾ ψ (σ ,- u) (o' φ) = thinSub-↾ ψ σ φ
-- restricting an embedded identity:  idEmb ψ ↾ φ ≡ idEmb (φ ⨾ ψ).
idEmb-↾ : ∀ {sup Δ Δ′}(ψ : Δ ⊑ Δ′)(φ : sup ⊑ Δ) → idEmb ψ ↾ φ ≡ idEmb (φ ⨾ ψ)
idEmb-↾ ψ φ = trans (cong (_↾ φ) (idEmb-thinSub ψ))
              (trans (thinSub-↾ ψ idS φ)
              (trans (cong (thinSub ψ) (idS↾-idEmb φ)) (thinSub-idEmb ψ φ)))
-- renaming IS substitution by an embedded identity.
opaque
  unfolding _⟪_⟫
  ren≡emb : ∀ {Δ Δ′ s}(u : Exp^ s ↑ Δ)(ψ : Δ ⊑ Δ′) → u ⟨ ψ ⟩ ≡ u ⟪ idEmb ψ ⟫
  ren≡emb (t ⇑ φ) ψ = trans (sym (sub-idEmb t (φ ⨾ ψ))) (cong (sub t) (sym (idEmb-↾ ψ φ)))
-- the `⊢App`-result instantiation commutes with renaming.
opaque
  unfolding idEmb _⟪_⟫
  inst-ren : ∀ {Δ Δ′ sₐ}(B : Ty ↑ (ty ∷ Δ))(a : Ty sₐ)(ρ : sₐ ⊑ Δ)(ψ : Δ ⊑ Δ′)
    → (B ⟪ idS ,- (a ⇑ ρ) ⟫) ⟨ ψ ⟩ ≡ (B ⟨ os ψ ⟩) ⟪ idS ,- (a ⇑ (ρ ⨾ ψ)) ⟫
  inst-ren B a ρ ψ =
    trans (ren≡emb (B ⟪ idS ,- (a ⇑ ρ) ⟫) ψ)
    (trans (⟪⟫-fusion B (idS ,- (a ⇑ ρ)) (idEmb ψ))
    (trans (cong (B ⟪_⟫) spine)
           (sym (trans (cong (_⟪ idS ,- (a ⇑ (ρ ⨾ ψ)) ⟫) (ren≡emb B (os ψ)))
                       (⟪⟫-fusion B (idEmb (os ψ)) (idS ,- (a ⇑ (ρ ⨾ ψ))))))))
    where
      spine : (idS ,- (a ⇑ ρ)) ⨟ idEmb ψ ≡ idEmb (os ψ) ⨟ (idS ,- (a ⇑ (ρ ⨾ ψ)))
      spine = cong₂ _,-_
                (sym (trans (wk-⨟-cons (idEmb ψ) idS (a ⇑ (ρ ⨾ ψ))) (IdR (idEmb ψ))))
                (sym (ren≡emb (a ⇑ ρ) ψ))
-- wk↑ commutes with renaming under the matching binder (definitional once `_⨾_` unfolds).
opaque
  unfolding _⨾_
  wk↑-⟨⟩ : ∀ {T} s {Δ Δ′}(B : T ↑ Δ)(ψ : Δ ⊑ Δ′) → (wk↑ s B) ⟨ os ψ ⟩ ≡ wk↑ s (B ⟨ ψ ⟩)
  wk↑-⟨⟩ s (t ⇑ ξ) ψ = refl

-- `CxR ψ Φ Φ′`: Φ′ : Cx Δ′ is Φ : Cx Δ renamed/extended along ψ : Δ ⊑ Δ′.
data CxR : ∀ {Δ Δ′} → Δ ⊑ Δ′ → Cx Δ → Cx Δ′ → Set where
  ozᶜ : CxR oz ε ε
  os* : ∀ {Δ Δ′}{ψ : Δ ⊑ Δ′}{Φ : Cx Δ}{Φ′ : Cx Δ′} → CxR ψ Φ Φ′ → CxR (os ψ) (Φ ,*) (Φ′ ,*)
  os- : ∀ {Δ Δ′}{ψ : Δ ⊑ Δ′}{Φ : Cx Δ}{Φ′ : Cx Δ′}(A : Ty ↑ Δ) → CxR ψ Φ Φ′ → CxR (os ψ) (Φ ,- A) (Φ′ ,- (A ⟨ ψ ⟩))
  o'* : ∀ {Δ Δ′}{ψ : Δ ⊑ Δ′}{Φ : Cx Δ}{Φ′ : Cx Δ′} → CxR ψ Φ Φ′ → CxR (o' ψ) Φ (Φ′ ,*)
  o'- : ∀ {Δ Δ′}{ψ : Δ ⊑ Δ′}{Φ : Cx Δ}{Φ′ : Cx Δ′}(C : Ty ↑ Δ′) → CxR ψ Φ Φ′ → CxR (o' ψ) Φ (Φ′ ,- C)

-- lookup commutes with the renaming: lookup Φ′ (x ⨾ ψ) = (lookup Φ x) ⟨ ψ ⟩.
opaque
  unfolding _⨾_
  lookup-ren : ∀ {Δ Δ′}{ψ : Δ ⊑ Δ′}{Φ : Cx Δ}{Φ′ : Cx Δ′}
             → CxR ψ Φ Φ′ → (x : (tm ∷ []) ⊑ Δ) → lookup Φ′ (x ⨾ ψ) ≡ (lookup Φ x) ⟨ ψ ⟩
  lookup-ren (os- A r) (os x) = refl
  lookup-ren (os- A r) (o' x) = cong (wk↑ tm) (lookup-ren r x)
  lookup-ren (os* r)   (o' x) = cong (wk↑ ty) (lookup-ren r x)
  lookup-ren (o'* r)   x      = cong (wk↑ ty) (lookup-ren r x)
  lookup-ren (o'- C r) x      = cong (wk↑ tm) (lookup-ren r x)

-- renaming distributes over the type-formers (helper-level, via the Scaffold laws).
⇒↑-⟨⟩ : ∀ {Δ Δ′}(A B : Ty ↑ Δ)(ψ : Δ ⊑ Δ′) → (A ⇒↑ B) ⟨ ψ ⟩ ≡ (A ⟨ ψ ⟩) ⇒↑ (B ⟨ ψ ⟩)
⇒↑-⟨⟩ A B ψ = cong (_`→_ <$>_) (pairUp-⟨⟩ A B ψ)
∀↑-⟨⟩ : ∀ {Δ Δ′}(B : Ty ↑ (ty ∷ Δ))(ψ : Δ ⊑ Δ′) → (∀↑ B) ⟨ ψ ⟩ ≡ ∀↑ (B ⟨ os ψ ⟩)
∀↑-⟨⟩ B ψ = cong (`∀ <$>_) (bindUp-⟨⟩ B ψ)

-- the two `_⨾_` structural reductions, as CLOSED lemmas (proven `unfolding _⨾_`
-- but NOT registered — so the global thinning-monoid rewrites stay confluent).
opaque
  unfolding _⨾_
  ⨾-osos : ∀ {sup Δ Δ′ s}(θ : sup ⊑ Δ)(ψ : Δ ⊑ Δ′) → os {s = s} θ ⨾ os ψ ≡ os (θ ⨾ ψ)
  ⨾-osos θ ψ = refl
  ⨾-o'os : ∀ {sup Δ Δ′ s}(θ : sup ⊑ Δ)(ψ : Δ ⊑ Δ′) → o' {s = s} θ ⨾ os ψ ≡ o' (θ ⨾ ψ)
  ⨾-o'os θ ψ = refl

-- renaming preserves typing.  Recursion on the derivation; the binder cases push
-- ψ under one binder (os ψ) and extend CxR with os*; the body thinning's `_⨾ os ψ`
-- is reduced through ⨾-osos/⨾-o'os.
⊢-ren : ∀ {sup Δ Δ′}{ψ : Δ ⊑ Δ′}{Φ : Cx Δ}{Φ′ : Cx Δ′}{θ : sup ⊑ Δ}{e : Tm sup}{A : Ty ↑ Δ}
      → CxR ψ Φ Φ′ → Φ ⊢[ θ ] e ∶ A → Φ′ ⊢[ θ ⨾ ψ ] e ∶ (A ⟨ ψ ⟩)
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢var {Φ = Φ}{θ = θ}) = subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] var ∶ T) (lookup-ren r θ) ⊢var
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢app {l = l}{r = rr}{cv = cv}{θ = θ}{A = A}{B = B} ⊢l ⊢r) =
  ⊢app {cv = cv} (subst (λ T → Φ′ ⊢[ thinL cv ⨾ (θ ⨾ ψ) ] l ∶ T) (⇒↑-⟨⟩ A B ψ) (⊢-ren r ⊢l)) (⊢-ren r ⊢r)
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢lamᵘ {a = a}{body = body}{cv = cv}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] `lam (pair a (use body) cv) ∶ T) (sym (⇒↑-⟨⟩ (a ⇑ (thinL cv ⨾ θ)) B ψ))
        (⊢lamᵘ (subst (λ φ → (Φ′ ,- (a ⇑ (thinL cv ⨾ θ) ⟨ ψ ⟩)) ⊢[ φ ] body ∶ (wk↑ tm (B ⟨ ψ ⟩))) (⨾-osos (thinR cv ⨾ θ) ψ)
               (subst (λ T → (Φ′ ,- (a ⇑ (thinL cv ⨾ θ) ⟨ ψ ⟩)) ⊢[ os (thinR cv ⨾ θ) ⨾ os ψ ] body ∶ T)
                      (wk↑-⟨⟩ tm B ψ) (⊢-ren (os- (a ⇑ (thinL cv ⨾ θ)) r) ⊢t))))
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢lamᵈ {a = a}{body = body}{cv = cv}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] `lam (pair a (drop body) cv) ∶ T) (sym (⇒↑-⟨⟩ (a ⇑ (thinL cv ⨾ θ)) B ψ))
        (⊢lamᵈ (subst (λ φ → (Φ′ ,- (a ⇑ (thinL cv ⨾ θ) ⟨ ψ ⟩)) ⊢[ φ ] body ∶ (wk↑ tm (B ⟨ ψ ⟩))) (⨾-o'os (thinR cv ⨾ θ) ψ)
               (subst (λ T → (Φ′ ,- (a ⇑ (thinL cv ⨾ θ) ⟨ ψ ⟩)) ⊢[ o' (thinR cv ⨾ θ) ⨾ os ψ ] body ∶ T)
                      (wk↑-⟨⟩ tm B ψ) (⊢-ren (os- (a ⇑ (thinL cv ⨾ θ)) r) ⊢t))))
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢Lamᵘ {body = body}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] `Lam (use body) ∶ T) (sym (∀↑-⟨⟩ B ψ))
        (⊢Lamᵘ (subst (λ φ → (Φ′ ,*) ⊢[ φ ] body ∶ (B ⟨ os ψ ⟩)) (⨾-osos θ ψ) (⊢-ren (os* r) ⊢t)))
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢Lamᵈ {body = body}{θ = θ}{B = B} ⊢t) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] `Lam (drop body) ∶ T) (sym (∀↑-⟨⟩ B ψ))
        (⊢Lamᵈ (subst (λ φ → (Φ′ ,*) ⊢[ φ ] body ∶ (B ⟨ os ψ ⟩)) (⨾-o'os θ ψ) (⊢-ren (os* r) ⊢t)))
⊢-ren {ψ = ψ}{Φ′ = Φ′} r (⊢App {e = e}{a = a}{cv = cv}{θ = θ}{B = B} ⊢e) =
  subst (λ T → Φ′ ⊢[ θ ⨾ ψ ] `App (pair e a cv) ∶ T) (sym (inst-ren B a (thinR cv ⨾ θ) ψ))
        (⊢App {a = a}{cv = cv}{θ = θ ⨾ ψ}{B = B ⟨ os ψ ⟩}
              (subst (λ T → Φ′ ⊢[ thinL cv ⨾ (θ ⨾ ψ) ] e ∶ T) (∀↑-⟨⟩ B ψ) (⊢-ren r ⊢e)))

-- the identity context-renaming (oi keeps every var; classifiers unchanged).
opaque
  unfolding oi
  cxr-id : ∀ {Δ}(Φ : Cx Δ) → CxR oi Φ Φ
  cxr-id ε        = ozᶜ
  cxr-id (Φ ,*)   = os* (cxr-id Φ)
  cxr-id (Φ ,- A) = subst (λ B → CxR (os oi) (Φ ,- A) (Φ ,- B)) (ren-id A) (os- A (cxr-id Φ))

-- wk↑ IS renaming by `o' oi`, and the matching subst-commutation (helper level).
opaque
  unfolding _⨾_
  ren-o'oi : ∀ {T} s {Δ}(B : T ↑ Δ) → B ⟨ o' oi ⟩ ≡ wk↑ s B
  ren-o'oi s (t ⇑ ξ) = refl
  ⨾-o'oi : ∀ {sup Δ s}(θ : sup ⊑ Δ) → θ ⨾ o' {s = s} oi ≡ o' θ
  ⨾-o'oi θ = refl
-- A ⟪ wkSub σ ⟫ ≡ wk↑ s′ (A ⟪ σ ⟫).  NOT registrable (races SCons-∙), so it is
-- consumed by the entry-weakening HELPERS `⊢wkσ-tm`/`⊢wkσ-ty` below.
opaque
  unfolding _⟪_⟫
  wk↑-⟪⟫ : ∀ {Δ Θ s' s}(A : Exp^ s ↑ Δ)(σ : Sub Θ Δ) → A ⟪ wkSub {s'} σ ⟫ ≡ wk↑ s' (A ⟪ σ ⟫)
  wk↑-⟪⟫ (a ⇑ ξ) σ = trans (cong (sub a) (wk-↾ σ ξ)) (sub-wk a (σ ↾ ξ))
  -- weaken-then-cons cancellation: substituting a freshly-weakened classifier by a
  -- cons drops the new entry (refl: the support skips the head var).
  wk-cons : ∀ {Δ Θ s' s}(A : Exp^ s ↑ Δ)(σ : Sub Θ Δ)(u : Exp^ s' ↑ Θ) → (wk↑ s' A) ⟪ σ ,- u ⟫ ≡ A ⟪ σ ⟫
  wk-cons (a ⇑ ξ) σ u = refl

-- one-binder context weakening of a derivation, specialised from `⊢-ren` along o' oi.
⊢wk-tm : ∀ {sup Δ}{Ψ : Cx Δ}{θ : sup ⊑ Δ}{t : Tm sup}{T : Ty ↑ Δ}(C : Ty ↑ Δ)
       → Ψ ⊢[ θ ] t ∶ T → (Ψ ,- C) ⊢[ o' θ ] t ∶ wk↑ tm T
⊢wk-tm {Ψ = Ψ}{θ = θ}{t = t}{T = T} C ⊢t =
  subst (λ T′ → (Ψ ,- C) ⊢[ o' θ ] t ∶ T′) (ren-o'oi tm T)
        (subst (λ φ → (Ψ ,- C) ⊢[ φ ] t ∶ (T ⟨ o' oi ⟩)) (⨾-o'oi θ) (⊢-ren (o'- C (cxr-id Ψ)) ⊢t))
⊢wk-ty : ∀ {sup Δ}{Ψ : Cx Δ}{θ : sup ⊑ Δ}{t : Tm sup}{T : Ty ↑ Δ}
       → Ψ ⊢[ θ ] t ∶ T → (Ψ ,*) ⊢[ o' θ ] t ∶ wk↑ ty T
⊢wk-ty {Ψ = Ψ}{θ = θ}{t = t}{T = T} ⊢t =
  subst (λ T′ → (Ψ ,*) ⊢[ o' θ ] t ∶ T′) (ren-o'oi ty T)
        (subst (λ φ → (Ψ ,*) ⊢[ φ ] t ∶ (T ⟨ o' oi ⟩)) (⨾-o'oi θ) (⊢-ren (o'* (cxr-id Ψ)) ⊢t))

-- ENTRY weakening at a σ-moved classifier: weaken AND retype `A ⟪ σ ⟫ ↦ A ⟪ wkSub σ ⟫`
-- (the wk↑-⟪⟫ coercion lives HERE, so `wkSub-pres` stays subst-free).
⊢wkσ-tm : ∀ {Δ Γ}{Ψ : Cx Δ}{u : Tm ↑ Δ}{A : Ty ↑ Γ}{σ : Sub Δ Γ}(C : Ty ↑ Δ)
        → Ψ ⊢↑ u ∶ (A ⟪ σ ⟫) → (Ψ ,- C) ⊢↑ wk↑ tm u ∶ (A ⟪ wkSub σ ⟫)
⊢wkσ-tm {Ψ = Ψ}{u = u ⇑ φ}{A = A}{σ = σ} C ⊢u =
  subst (λ T → (Ψ ,- C) ⊢[ o' φ ] u ∶ T) (sym (wk↑-⟪⟫ A σ)) (⊢wk-tm C ⊢u)
⊢wkσ-ty : ∀ {Δ Γ}{Ψ : Cx Δ}{u : Tm ↑ Δ}{A : Ty ↑ Γ}{σ : Sub Δ Γ}
        → Ψ ⊢↑ u ∶ (A ⟪ σ ⟫) → (Ψ ,*) ⊢↑ wk↑ ty u ∶ (A ⟪ wkSub {ty} σ ⟫)
⊢wkσ-ty {Ψ = Ψ}{u = u ⇑ φ}{A = A}{σ = σ} ⊢u =
  subst (λ T → (Ψ ,*) ⊢[ o' φ ] u ∶ T) (sym (wk↑-⟪⟫ A σ)) (⊢wk-ty ⊢u)

-- the fresh bound tm-var, typed at its σ-moved classifier (helper; the wk↑-⟪⟫
-- coercion lives here so the lam case of `sub-pres` is a bare smart-constructor).
⊢freshσ : ∀ {Δ Γ}{Ψ : Cx Δ}{A : Ty ↑ Γ}{σ : Sub Δ Γ}
        → (Ψ ,- (A ⟪ σ ⟫)) ⊢↑ var₀ ∶ (A ⟪ wkSub σ ⟫)
⊢freshσ {Ψ = Ψ}{A = A}{σ = σ} = subst (λ T → (Ψ ,- (A ⟪ σ ⟫)) ⊢[ os oe ] var ∶ T) (sym (wk↑-⟪⟫ A σ)) ⊢var

-- the lam BODY's codomain, after lifting σ:  (wk↑ tm B) ⟪ wkSub σ ,- var₀ ⟫
-- ≡ wk↑ tm (B ⟪ σ ⟫)  (weaken-then-cons then wk↑-⟪⟫).  Body-derivation transformer.
lam-body-dist : ∀ {Γ Δ}{Ψ′ : Cx (tm ∷ Δ)}{body : Tm ↑ (tm ∷ Δ)}(B : Ty ↑ Γ)(σ : Sub Δ Γ)
              → Ψ′ ⊢↑ body ∶ ((wk↑ tm B) ⟪ wkSub σ ,- var₀ ⟫) → Ψ′ ⊢↑ body ∶ wk↑ tm (B ⟪ σ ⟫)
lam-body-dist {Ψ′ = Ψ′}{body = b ⇑ φ} B σ =
  subst (λ T → Ψ′ ⊢[ φ ] b ∶ T) (trans (wk-cons B (wkSub σ) var₀) (wk↑-⟪⟫ B σ))

-- the Lamᵈ BODY bridge: the term `sub body (wkSub τ)` IS `wk↑ ty (sub body τ)`
-- (`sub-wk`), the form `Lam↑`/`bindUp` needs.  Coerces the whole thing-with-thinning.
Lam-drop-body : ∀ {sup Δ}{Ψ′ : Cx (ty ∷ Δ)}{T : Ty ↑ (ty ∷ Δ)}(body : Tm sup)(τ : Sub Δ sup)
              → Ψ′ ⊢↑ sub body (wkSub {ty} τ) ∶ T → Ψ′ ⊢↑ wk↑ ty (sub body τ) ∶ T
Lam-drop-body {Ψ′ = Ψ′}{T = T} body τ = subst (λ u → Ψ′ ⊢↑ u ∶ T) (sub-wk body τ)

-- the lam/App DOMAIN bridges:  on a TYPE-IN-A-TERM the engine's term-substitution
-- `selL/selR cv τ` equals the type-substitution restriction `σ ↾ (thinL/thinR cv ⨾ θ)`
-- (WtS invariant + selL-↾/selR-↾), so `sub a (selL cv τ) ≡ (a ⇑ thinL cv ⨾ θ) ⟪ σ ⟫`.
-- `_⟪_⟫` unfolds to `sub _ (σ ↾ _)`  (the definition; bridges term/type sides
-- while keeping `_⟪_⟫` OPAQUE in the consumers).
opaque
  unfolding _⟪_⟫
  ⟪⟫≡sub↾ : ∀ {sₐ Δ Θ}(a : Ty sₐ)(ρ : sₐ ⊑ Δ)(σ : Sub Θ Δ) → ((a ⇑ ρ) ⟪ σ ⟫) ≡ sub a (σ ↾ ρ)
  ⟪⟫≡sub↾ a ρ σ = refl
lam-dom : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
            {sₗ sᵣ}(cv : Cover sₗ sᵣ sup)(a : Ty sₗ)
        → WtS θ τ σ Φ Ψ → sub a (selL cv τ) ≡ ((a ⇑ (thinL cv ⨾ θ)) ⟪ σ ⟫)
lam-dom {θ = θ}{σ = σ} cv a w =
  trans (cong (λ ρ → sub a (selL cv ρ)) (wts-inv w))
        (trans (cong (sub a) (selL-↾ cv θ σ)) (sym (⟪⟫≡sub↾ a (thinL cv ⨾ θ) σ)))
app-dom : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
            {sₗ sᵣ}(cv : Cover sₗ sᵣ sup)(a : Ty sᵣ)
        → WtS θ τ σ Φ Ψ → sub a (selR cv τ) ≡ ((a ⇑ (thinR cv ⨾ θ)) ⟪ σ ⟫)
app-dom {θ = θ}{σ = σ} cv a w =
  trans (cong (λ ρ → sub a (selR cv ρ)) (wts-inv w))
        (trans (cong (sub a) (selR-↾ cv θ σ)) (sym (⟪⟫≡sub↾ a (thinR cv ⨾ θ) σ)))

-- recoerce the lam body's CONTEXT classifier from the type-side `(a⇑ρ)⟪σ⟫` (what
-- `⊢freshσ` produces) to the term-side `sub a (selL cv τ)` (what the built TERM has),
-- so `⊢lam↑`'s context matches the goal term's domain.
lam-ctx : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
            {sₗ sᵣ}(cv : Cover sₗ sᵣ sup)(a : Ty sₗ){body : Tm ↑ (tm ∷ Δ)}{T : Ty ↑ (tm ∷ Δ)}
        → WtS θ τ σ Φ Ψ
        → (Ψ ,- ((a ⇑ (thinL cv ⨾ θ)) ⟪ σ ⟫)) ⊢↑ body ∶ T → (Ψ ,- (sub a (selL cv τ))) ⊢↑ body ∶ T
lam-ctx {Ψ = Ψ} cv a {body = b ⇑ φ}{T = T} w =
  subst (λ C → (Ψ ,- C) ⊢[ φ ] b ∶ T) (sym (lam-dom cv a w))

-- the App-result SPINE identity (its own `unfolding _⟪_⟫`, so var₀⟪⟫ reduces).
opaque
  unfolding idEmb _⟪_⟫
  App-spine : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
                {sₗ sᵣ}(cv : Cover sₗ sᵣ sup)(a : Ty sᵣ)
            → WtS θ τ σ Φ Ψ
            → (wkSub σ ,- var₀) ⨟ (idS ,- (sub a (selR cv τ))) ≡ (idS ,- (a ⇑ (thinR cv ⨾ θ))) ⨟ σ
  App-spine {τ = τ}{σ = σ} cv a w =
    cong₂ _,-_ (trans (wk-⨟-cons σ idS (sub a (selR cv τ))) (IdR σ)) (app-dom cv a w)

-- the App RESULT re-assembly: `⊢App↑`'s output (function distributed by `∀↑-dist`,
-- argument `sub a (selR cv τ)`) coerces to the goal `(B ⟪ idS ,- (a ⇑ ρ) ⟫) ⟪ σ ⟫`.
-- The two `⟪⟫`-of-`⟪⟫` collapse by fusion to a single `B ⟪_⟫` over equal spines.
App-res : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
            {at : Tm ↑ Δ}{sₗ sᵣ}(cv : Cover sₗ sᵣ sup)(a : Ty sᵣ)(B : Ty ↑ (ty ∷ Γ))
        → WtS θ τ σ Φ Ψ
        → Ψ ⊢↑ at ∶ ((B ⟪ wkSub σ ,- var₀ ⟫) ⟪ idS ,- (sub a (selR cv τ)) ⟫)
        → Ψ ⊢↑ at ∶ ((B ⟪ idS ,- (a ⇑ (thinR cv ⨾ θ)) ⟫) ⟪ σ ⟫)
App-res {θ = θ}{τ = τ}{σ = σ}{Ψ = Ψ}{at = at ⇑ φ} cv a B w ⊢a =
  subst (λ T → Ψ ⊢[ φ ] at ∶ T)
        (trans (⟪⟫-fusion B (wkSub σ ,- var₀) (idS ,- (sub a (selR cv τ))))
        (trans (cong (λ S → B ⟪ S ⟫) (App-spine cv a w))
               (sym (⟪⟫-fusion B (idS ,- (a ⇑ (thinR cv ⨾ θ))) σ))))
        ⊢a

-- the lam RESULT re-assembly: coerce `⊢lam↑`'s output (domain `sub a (selL cv τ)`,
-- codomain `B ⟪ σ ⟫`) to the goal `((a ⇑ ρ) ⇒↑ B) ⟪ σ ⟫`.  The ARROW former
-- distributes over `σ` DEFINITIONALLY (Sf.SystemFCoh), so the goal reduces to
-- `((a ⇑ ρ) ⟪ σ ⟫) ⇒↑ (B ⟪ σ ⟫)` and only the DOMAIN needs `lam-dom`'s coercion.
opaque
  unfolding _⟪_⟫
  lam-res : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
              {lt : Tm ↑ Δ}{sₗ sᵣ}(cv : Cover sₗ sᵣ sup)(a : Ty sₗ)(B : Ty ↑ Γ)
          → WtS θ τ σ Φ Ψ
          → Ψ ⊢↑ lt ∶ ((sub a (selL cv τ)) ⇒↑ (B ⟪ σ ⟫))
          → Ψ ⊢↑ lt ∶ (((a ⇑ (thinL cv ⨾ θ)) ⇒↑ B) ⟪ σ ⟫)
  lam-res {θ = θ}{σ = σ}{Ψ = Ψ}{lt = lt ⇑ φ} cv a B w ⊢t =
    subst (λ D → Ψ ⊢[ φ ] lt ∶ (D ⇒↑ (B ⟪ σ ⟫))) (lam-dom cv a w) ⊢t

-- ── WEAKENING the well-typed substitution by one fresh TARGET binder.  `wkSub` on
-- both τ and σ;  every typed entry retyped through `⊢wkσ-*`.  Subst-free. ──
opaque
  unfolding wkSub
  wkSub-pres-tm : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}(C : Ty ↑ Δ)
                → WtS θ τ σ Φ Ψ → WtS θ (wkSub τ) (wkSub σ) Φ (Ψ ,- C)
  wkSub-pres-tm C []                          = []
  wkSub-pres-tm C (w ,*ˢ)                     = wkSub-pres-tm C w ,*ˢ
  wkSub-pres-tm C (w ,*ᵈ)                     = wkSub-pres-tm C w ,*ᵈ
  wkSub-pres-tm C (_,-ˢ_ {σ = σ}{A = A} w ⊢u) = wkSub-pres-tm C w ,-ˢ ⊢wkσ-tm {A = A}{σ = σ} C ⊢u
  wkSub-pres-tm C (w ,-ᵈ)                     = wkSub-pres-tm C w ,-ᵈ
  wkSub-pres-ty : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
                → WtS θ τ σ Φ Ψ → WtS θ (wkSub τ) (wkSub σ) Φ (Ψ ,*)
  wkSub-pres-ty []                          = []
  wkSub-pres-ty (w ,*ˢ)                     = wkSub-pres-ty w ,*ˢ
  wkSub-pres-ty (w ,*ᵈ)                     = wkSub-pres-ty w ,*ᵈ
  wkSub-pres-ty (_,-ˢ_ {σ = σ}{A = A} w ⊢u) = wkSub-pres-ty w ,-ˢ ⊢wkσ-ty {A = A}{σ = σ} ⊢u
  wkSub-pres-ty (w ,-ᵈ)                     = wkSub-pres-ty w ,-ᵈ

-- ════════════════════════════════════════════════════════════════════════════
-- THE VARIABLE CASE of `sub-pres`.  For a singleton support the WtS is an
-- all-dropped chain around one `,-ˢ`; the selected entry's typing IS the goal,
-- modulo the weaken-then-cons cancellations that lookup/σ accumulate (consumed by
-- this HELPER, so `sub-pres`'s ⊢var case is a bare application).
-- ════════════════════════════════════════════════════════════════════════════
var-pres : ∀ {Γ Δ}{θ : (tm ∷ []) ⊑ Γ}{τ : Sub Δ (tm ∷ [])}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}
         → WtS θ τ σ Φ Ψ → Ψ ⊢↑ sub var τ ∶ (lookup Φ θ ⟪ σ ⟫)
var-pres {Ψ = Ψ} (_,-ˢ_ {τ = τ}{σ = σ}{u = u}{A = A} w ⊢u) =
  subst (λ t → Ψ ⊢↑ t ∶ ((wk↑ tm A) ⟪ σ ,- u ⟫)) (sym (sub-var-cons τ u))
        (subst (λ T → Ψ ⊢↑ u ∶ T) (sym (wk-cons A σ u)) ⊢u)
  where opaque
          unfolding sub
          sub-var-cons : ∀ {Δ}(τ₀ : Sub Δ [])(u′ : Tm ↑ Δ) → sub var (τ₀ ,- u′) ≡ u′
          sub-var-cons [] u′ = refl
var-pres {Ψ = Ψ} (_,*ᵈ {θ = θw}{τ = τ}{σ = σ}{Φ = Φw}{u = u} w) =
  subst (λ T → Ψ ⊢↑ sub var τ ∶ T) (sym (wk-cons (lookup Φw θw) σ u)) (var-pres w)
var-pres {Ψ = Ψ} (_,-ᵈ {θ = θw}{τ = τ}{σ = σ}{Φ = Φw}{u = u} w) =
  subst (λ T → Ψ ⊢↑ sub var τ ∶ T) (sym (wk-cons (lookup Φw θw) σ u)) (var-pres w)

-- ════════════════════════════════════════════════════════════════════════════
-- SUBSTITUTION PRESERVES TYPING (the crux).  Recursion on the derivation; the
-- term-substitution `τ` is peeled by `selL/selR` (matching `sub`'s clauses,
-- DEFINITIONALLY via selL-pres/selR-pres), the type-substitution `σ` stays full.
-- SUBST-FREE: the ARROW distribution is now DEFINITIONAL (Sf.SystemFCoh), so the
-- ⊢app/⊢lam cases apply the IH with NO transformer; only the ∀ former still needs
-- the propositional `∀↑-dist`/`∀↑-undist` bridge (it cannot be a confluent
-- rewrite).  Body extensions go through wkSub-pres + ⊢freshσ.  No `subst` here.
-- ════════════════════════════════════════════════════════════════════════════
opaque
  unfolding sub _⟪_⟫
  sub-pres : ∀ {sup Γ Δ}{θ : sup ⊑ Γ}{τ : Sub Δ sup}{σ : Sub Δ Γ}{Φ : Cx Γ}{Ψ : Cx Δ}{e : Tm sup}{A : Ty ↑ Γ}
           → WtS θ τ σ Φ Ψ → Φ ⊢[ θ ] e ∶ A → Ψ ⊢↑ sub e τ ∶ (A ⟪ σ ⟫)
  sub-pres w ⊢var = var-pres w
  -- ARROW distributes over σ definitionally, so the function IH `⊢ … ∶ (A⇒↑B)⟪σ⟫`
  -- IS already at `(A⟪σ⟫) ⇒↑ (B⟪σ⟫)` — no transformer.
  sub-pres {τ = τ}{σ = σ} w (⊢app {l = l}{r = r}{cv = cv}{A = A}{B = B} ⊢l ⊢r) =
    ⊢app↑ (sub l (selL cv τ)) (sub r (selR cv τ))
          (sub-pres (selL-pres cv w) ⊢l) (sub-pres (selR-pres cv w) ⊢r)
  sub-pres {τ = τ}{σ = σ} w (⊢lamᵘ {a = a}{body = body}{cv = cv}{θ = θ}{B = B} ⊢t) =
    lam-res cv a B w
      (⊢lam↑ (thing (sub a (selL cv τ))) (thn (sub a (selL cv τ))) (sub body (wkSub (selR cv τ) ,- var₀))
             (lam-ctx cv a w (lam-body-dist B σ
               (sub-pres (_,-ˢ_ {A = a ⇑ (thinL cv ⨾ θ)} (wkSub-pres-tm ((a ⇑ (thinL cv ⨾ θ)) ⟪ σ ⟫) (selR-pres cv w))
                                (⊢freshσ {A = a ⇑ (thinL cv ⨾ θ)}{σ = σ})) ⊢t))))
  sub-pres {τ = τ}{σ = σ} w (⊢lamᵈ {a = a}{body = body}{cv = cv}{θ = θ}{B = B} ⊢t) =
    lam-res cv a B w
      (⊢lam↑ (thing (sub a (selL cv τ))) (thn (sub a (selL cv τ))) (wk↑ tm (sub body (selR cv τ)))
             (⊢wk-tm (sub a (selL cv τ))
                     (sub-pres (_,-ᵈ {u = sub body (selR cv τ)} (selR-pres cv w)) ⊢t)))
  sub-pres {τ = τ}{σ = σ} w (⊢Lamᵘ {body = body}{B = B} ⊢t) =
    ∀↑-undist B σ (⊢Lam↑ (sub body (wkSub τ ,- var₀)) (sub-pres (wkSub-pres-ty w ,*ˢ) ⊢t))
  sub-pres {τ = τ}{σ = σ} w (⊢Lamᵈ {body = body}{B = B} ⊢t) =
    ∀↑-undist B σ (⊢Lam↑ (wk↑ ty (sub body τ)) (Lam-drop-body body τ (sub-pres (wkSub-pres-ty w ,*ᵈ) ⊢t)))
  sub-pres {τ = τ}{σ = σ} w (⊢App {e = e}{a = a}{cv = cv}{θ = θ}{B = B} ⊢e) =
    App-res {at = App↑ (sub e (selL cv τ)) (sub a (selR cv τ))} cv a B w
      (⊢App↑ (B ⟪ wkSub σ ,- var₀ ⟫) (sub e (selL cv τ)) (sub a (selR cv τ))
             (∀↑-dist B σ (sub-pres (selL-pres cv w) ⊢e)))

-- ════════════════════════════════════════════════════════════════════════════
-- THE IDENTITY well-typed substitution `id-pres : WtS oi idS idS Φ Φ` (term- AND
-- type-substitution both `idS`).  Mirrors `idS = wkSub idS ,- var₀`: a ty-binder
-- threads `wkSub-pres-ty`, a tm-binder threads `wkSub-pres-tm` and types the fresh
-- var.  This is the base the β-redex extends with the typed argument.  Subst-free.
-- ════════════════════════════════════════════════════════════════════════════
-- `restrict-pres φ Φ` : the TERM-substitution `idEmb φ` (over the support of φ)
-- paired with the FULL type-substitution `idS`.  A kept var (os) is `,*ˢ`/`,-ˢ`,
-- a dropped var (o') becomes `,*ᵈ`/`,-ᵈ`.  This is exactly the β-redex's
-- function-side environment: identity on the lam's free vars, full idS for types.
opaque
  unfolding idEmb idS
  restrict-pres : ∀ {sup Δ}(φ : sup ⊑ Δ)(Φ : Cx Δ) → WtS φ (idEmb φ) idS Φ Φ
  restrict-pres oz     ε        = []
  restrict-pres (os φ) (Φ ,*)   = wkSub-pres-ty (restrict-pres φ Φ) ,*ˢ
  restrict-pres (os φ) (Φ ,- A) =
    _,-ˢ_ {A = A} (wkSub-pres-tm (A ⟪ idS ⟫) (restrict-pres φ Φ)) (⊢freshσ {A = A}{σ = idS})
  restrict-pres (o' φ) (Φ ,*)   = wkSub-pres-ty (restrict-pres φ Φ) ,*ᵈ
  restrict-pres (o' φ) (Φ ,- A) = _,-ᵈ {u = var₀} (wkSub-pres-tm (A ⟪ idS ⟫) (restrict-pres φ Φ))


-- ════════════════════════════════════════════════════════════════════════════
-- CALL-BY-VALUE small-step reduction and SUBJECT REDUCTION.
--   Values: λ- and Λ-abstractions (use/drop).  `_⟶_ : Tm Γ → Tm ↑ Γ` (the
--   contractum's support may shrink).  preserve re-embeds the contractum along θ.
-- ════════════════════════════════════════════════════════════════════════════
data Value : ∀ {Γ} → Tm Γ → Set where
  V-lamᵘ : ∀ {sₐ sᵦ Γ}{a : Ty sₐ}{t : Tm (tm ∷ sᵦ)}{cv : Cover sₐ sᵦ Γ} → Value (`lam (pair a (use t)  cv))
  V-lamᵈ : ∀ {sₐ sᵦ Γ}{a : Ty sₐ}{t : Tm sᵦ}      {cv : Cover sₐ sᵦ Γ} → Value (`lam (pair a (drop t) cv))
  V-Lamᵘ : ∀ {Γ}{t : Tm (ty ∷ Γ)} → Value (`Lam (use t))
  V-Lamᵈ : ∀ {Γ}{t : Tm Γ}        → Value (`Lam (drop t))

data _⟶_ : ∀ {Γ} → Tm Γ → Tm ↑ Γ → Set where
  -- term-β (lam use): value-guarded; bound var ↦ arg, lam free vars ↦ identity.
  β  : ∀ {Γ sₐ sᵦ sˡ sʳ}{a : Ty sₐ}{t : Tm (tm ∷ sᵦ)}{cvL : Cover sₐ sᵦ sˡ}{arg : Tm sʳ}{cv : Cover sˡ sʳ Γ}
     → Value arg
     → `app (pair (`lam (pair a (use t) cvL)) arg cv)
         ⟶ sub t (idEmb (thinR cvL ⨾ thinL cv) ,- (arg ⇑ thinR cv))
  -- term-β (lam drop): the bound var is absent, so just drop it (no arg needed).
  βᵈ : ∀ {Γ sₐ sᵦ sˡ sʳ}{a : Ty sₐ}{t : Tm sᵦ}{cvL : Cover sₐ sᵦ sˡ}{arg : Tm sʳ}{cv : Cover sˡ sʳ Γ}
     → Value arg
     → `app (pair (`lam (pair a (drop t) cvL)) arg cv)
         ⟶ sub t (idEmb (thinR cvL ⨾ thinL cv))
  -- TYPE-β (Lam use): no value guard — type application fires regardless.
  βT : ∀ {Γ sᵇ sᵃ}{t : Tm (ty ∷ sᵇ)}{A : Ty sᵃ}{cv : Cover sᵇ sᵃ Γ}
     → `App (pair (`Lam (use t)) A cv)
         ⟶ sub t (idEmb (thinL cv) ,- (A ⇑ thinR cv))
  -- TYPE-β (Lam drop): the bound ty-var is absent.
  βTᵈ : ∀ {Γ sᵇ sᵃ}{t : Tm sᵇ}{A : Ty sᵃ}{cv : Cover sᵇ sᵃ Γ}
     → `App (pair (`Lam (drop t)) A cv)
         ⟶ sub t (idEmb (thinL cv))
  -- congruence: reduce the FUNCTION first
  ξ-fun : ∀ {Γ sₗ sᵣ}{l : Tm sₗ}{l′ : Tm ↑ sₗ}{r : Tm sᵣ}{cv : Cover sₗ sᵣ Γ}
        → l ⟶ l′ → `app (pair l r cv) ⟶ app↑ (l′ ⟨ thinL cv ⟩) (r ⇑ thinR cv)
  -- congruence: once the function is a value, reduce the ARGUMENT
  ξ-arg : ∀ {Γ sₗ sᵣ}{l : Tm sₗ}{r : Tm sᵣ}{r′ : Tm ↑ sᵣ}{cv : Cover sₗ sᵣ Γ}
        → Value l → r ⟶ r′ → `app (pair l r cv) ⟶ app↑ (l ⇑ thinL cv) (r′ ⟨ thinR cv ⟩)
  -- congruence: reduce the function position of a type application
  ξ-App : ∀ {Γ sₑ sₐ}{e : Tm sₑ}{e′ : Tm ↑ sₑ}{A : Ty sₐ}{cv : Cover sₑ sₐ Γ}
        → e ⟶ e′ → `App (pair e A cv) ⟶ App↑ (e′ ⟨ thinL cv ⟩) (A ⇑ thinR cv)
infix 3 _⟶_

-- the β-environment is well-typed: identity-embed the function's free vars (term
-- side, along `ρ`) under the FULL type-substitution idS, then the typed argument
-- (image `arg ⇑ ρ′`) on the bound var.  `Dom` is the bound var's classifier.
β-env-pres : ∀ {sᵦ sʳ Δ}{Φ : Cx Δ}{arg : Tm sʳ}{Dom : Ty ↑ Δ}
               (ρ : sᵦ ⊑ Δ)(ρ′ : sʳ ⊑ Δ)
           → Φ ⊢[ ρ′ ] arg ∶ Dom
           → WtS (os ρ) (idEmb ρ ,- (arg ⇑ ρ′)) (idS ,- (arg ⇑ ρ′)) (Φ ,- Dom) Φ
β-env-pres {Φ = Φ}{Dom = Dom} ρ ρ′ ⊢arg = _,-ˢ_ {A = Dom} (restrict-pres ρ Φ) ⊢arg
-- the βᵈ (lam/Lam drop) environment: no argument — the dropped bound var carries an
-- arbitrary (never-inspected) σ-image; only the restricted identity matters.
βᵈ-env-pres : ∀ {sᵦ Δ}{Φ : Cx Δ}{Dom : Ty ↑ Δ}{u : Tm ↑ Δ}(ρ : sᵦ ⊑ Δ)
            → WtS (o' ρ) (idEmb ρ) (idS ,- u) (Φ ,- Dom) Φ
βᵈ-env-pres {u = u} ρ = _,-ᵈ {u = u} (restrict-pres ρ _)

-- the TYPE-β environment: identity-embed the body's free vars, the type argument
-- `u` SHARED on the bound TY-var (`,*ˢ`).  No typing requirement (ty-vars carry no
-- classifier).  `βTᵈ-env-pres` is the drop analog (the bound ty-var is absent).
βT-env-pres : ∀ {sᵇ Δ}{Φ : Cx Δ}{u : Ty ↑ Δ}(ρ : sᵇ ⊑ Δ)
            → WtS (os ρ) (idEmb ρ ,- u) (idS ,- u) (Φ ,*) Φ
βT-env-pres {u = u} ρ = restrict-pres ρ _ ,*ˢ
βTᵈ-env-pres : ∀ {sᵇ Δ}{Φ : Cx Δ}{u : Ty ↑ Δ}(ρ : sᵇ ⊑ Δ)
             → WtS (o' ρ) (idEmb ρ) (idS ,- u) (Φ ,*) Φ
βTᵈ-env-pres {u = u} ρ = restrict-pres ρ _ ,*ᵈ

-- ════════════════════════════════════════════════════════════════════════════
-- SUBJECT REDUCTION.  preserve re-embeds the contractum along θ.  β/βᵈ/βT/βTᵈ
-- apply `sub-pres` to the β-environment; the ξ congruences rebuild with the typed
-- smart-constructors + the IH.
-- ════════════════════════════════════════════════════════════════════════════
-- the term smart-constructors commute with re-embedding (pairUp-⟨⟩); turns the
-- contractum `(app↑ X Y) ⟨ θ ⟩` into `app↑ (X⟨θ⟩) (Y⟨θ⟩)` so the typed
-- smart-constructors apply.  Derivation transformers (helpers, may use subst).
app↑-⟨⟩ : ∀ {Δ Θ}{Ψ : Cx Θ}{T : Ty ↑ Θ}(X Y : Tm ↑ Δ)(θ : Δ ⊑ Θ)
        → Ψ ⊢↑ (app↑ (X ⟨ θ ⟩) (Y ⟨ θ ⟩)) ∶ T → Ψ ⊢↑ ((app↑ X Y) ⟨ θ ⟩) ∶ T
app↑-⟨⟩ {Ψ = Ψ}{T = T} X Y θ = subst (λ Z → Ψ ⊢↑ Z ∶ T) (sym (cong (`app <$>_) (pairUp-⟨⟩ X Y θ)))
App↑-⟨⟩ : ∀ {Δ Θ}{Ψ : Cx Θ}{T : Ty ↑ Θ}(X : Tm ↑ Δ)(Y : Ty ↑ Δ)(θ : Δ ⊑ Θ)
        → Ψ ⊢↑ (App↑ (X ⟨ θ ⟩) (Y ⟨ θ ⟩)) ∶ T → Ψ ⊢↑ ((App↑ X Y) ⟨ θ ⟩) ∶ T
App↑-⟨⟩ {Ψ = Ψ}{T = T} X Y θ = subst (λ Z → Ψ ⊢↑ Z ∶ T) (sym (cong (`App <$>_) (pairUp-⟨⟩ X Y θ)))

-- re-embedding a β-contractum: (sub t (idEmb φ ,- (arg ⇑ φ′))) ⟨ θ ⟩
--   ≡ sub t (idEmb (φ ⨾ θ) ,- (arg ⇑ (φ′ ⨾ θ)))  (sub-thin + thinSub-idEmb).
β-reembed : ∀ {sᵇ sʳ sup Δ}{Ψ : Cx Δ}{T : Ty ↑ Δ}(t : Tm (tm ∷ sᵇ))(φ : sᵇ ⊑ sup)(arg : Tm sʳ)(φ′ : sʳ ⊑ sup)(θ : sup ⊑ Δ)
          → Ψ ⊢↑ sub t (idEmb (φ ⨾ θ) ,- (arg ⇑ (φ′ ⨾ θ))) ∶ T
          → Ψ ⊢↑ ((sub t (idEmb φ ,- (arg ⇑ φ′))) ⟨ θ ⟩) ∶ T
β-reembed {Ψ = Ψ}{T = T} t φ arg φ′ θ =
  subst (λ u → Ψ ⊢↑ u ∶ T)
        (trans (cong (sub t) (cong₂ _,-_ (sym (thinSub-idEmb θ φ)) refl))
               (sub-thin t θ (idEmb φ ,- (arg ⇑ φ′))))
-- the βᵈ analog (no argument).  Reused for βTᵈ (the dropped-ty-var type-β).
βᵈ-reembed : ∀ {sᵇ sup Δ}{Ψ : Cx Δ}{T : Ty ↑ Δ}(t : Tm sᵇ)(φ : sᵇ ⊑ sup)(θ : sup ⊑ Δ)
           → Ψ ⊢↑ sub t (idEmb (φ ⨾ θ)) ∶ T → Ψ ⊢↑ ((sub t (idEmb φ)) ⟨ θ ⟩) ∶ T
βᵈ-reembed {Ψ = Ψ}{T = T} t φ θ =
  subst (λ u → Ψ ⊢↑ u ∶ T) (trans (cong (sub t) (sym (thinSub-idEmb θ φ))) (sub-thin t θ (idEmb φ)))
-- the TYPE-β analog: bound TY-var, the argument is a TYPE.  Same spine proof.
βT-reembed : ∀ {sᵇ sʳ sup Δ}{Ψ : Cx Δ}{T : Ty ↑ Δ}(t : Tm (ty ∷ sᵇ))(φ : sᵇ ⊑ sup)(arg : Ty sʳ)(φ′ : sʳ ⊑ sup)(θ : sup ⊑ Δ)
           → Ψ ⊢↑ sub t (idEmb (φ ⨾ θ) ,- (arg ⇑ (φ′ ⨾ θ))) ∶ T
           → Ψ ⊢↑ ((sub t (idEmb φ ,- (arg ⇑ φ′))) ⟨ θ ⟩) ∶ T
βT-reembed {Ψ = Ψ}{T = T} t φ arg φ′ θ =
  subst (λ u → Ψ ⊢↑ u ∶ T)
        (trans (cong (sub t) (cong₂ _,-_ (sym (thinSub-idEmb θ φ)) refl))
               (sub-thin t θ (idEmb φ ,- (arg ⇑ φ′))))

-- ── THE β CASES of `preserve`, factored out so the lam/Lam can be INVERTED.  The
-- function's typing has a DEFINED type-former (`⇒↑`/`∀↑`) as its index, which the
-- unifier cannot peel — so we keep the lam's type a free variable `T` here (the
-- constructor match then just instantiates it), and recover the components with the
-- arrow/∀ injectivity above to coerce the argument and the result. ──

-- term-β (use): invert ⊢lamᵘ (its type kept FREE as `T`), retype the arg at the
-- body's domain, run `sub-pres` on the β-environment, coerce the codomain, re-embed.
preserveβᵘ : ∀ {sˡ sʳ sup Δ}{Φ : Cx Δ}{sᵃ sᵇ}{a : Ty sᵃ}{t : Tm (tm ∷ sᵇ)}
               {cvL : Cover sᵃ sᵇ sˡ}{arg : Tm sʳ}{Dom Cod : Ty ↑ Δ}{T : Ty ↑ Δ}
           (θ : sup ⊑ Δ)(cv : Cover sˡ sʳ sup)
           → Φ ⊢[ thinL cv ⨾ θ ] `lam (pair a (use t) cvL) ∶ T
           → Φ ⊢[ thinR cv ⨾ θ ] arg ∶ Dom
           → T ≡ (Dom ⇒↑ Cod)
           → Φ ⊢↑ ((sub t (idEmb (thinR cvL ⨾ thinL cv) ,- (arg ⇑ thinR cv))) ⟨ θ ⟩) ∶ Cod
preserveβᵘ {Φ = Φ}{t = t}{arg = arg} θ cv (⊢lamᵘ {cv = cvL}{B = Blam} ⊢t) ⊢r eq =
  β-reembed t (thinR cvL ⨾ thinL cv) arg (thinR cv) θ
    (subst (λ C → Φ ⊢↑ (sub t (idEmb ((thinR cvL ⨾ thinL cv) ⨾ θ) ,- (arg ⇑ (thinR cv ⨾ θ)))) ∶ C)
           (trans (wk-cons Blam idS (arg ⇑ (thinR cv ⨾ θ))) (⇒↑-injʳ eq))
      (sub-pres (β-env-pres ((thinR cvL ⨾ thinL cv) ⨾ θ) (thinR cv ⨾ θ)
                            (subst (λ D → Φ ⊢[ thinR cv ⨾ θ ] arg ∶ D) (sym (⇒↑-injˡ eq)) ⊢r)) ⊢t))

-- term-β (drop): the bound var is absent — no argument, no domain coercion.
preserveβᵈ : ∀ {sˡ sʳ sup Δ}{Φ : Cx Δ}{sᵃ sᵇ}{a : Ty sᵃ}{t : Tm sᵇ}
               {cvL : Cover sᵃ sᵇ sˡ}{arg : Tm sʳ}{Dom Cod : Ty ↑ Δ}{T : Ty ↑ Δ}
           (θ : sup ⊑ Δ)(cv : Cover sˡ sʳ sup)
           → Φ ⊢[ thinL cv ⨾ θ ] `lam (pair a (drop t) cvL) ∶ T
           → Φ ⊢[ thinR cv ⨾ θ ] arg ∶ Dom
           → T ≡ (Dom ⇒↑ Cod)
           → Φ ⊢↑ ((sub t (idEmb (thinR cvL ⨾ thinL cv))) ⟨ θ ⟩) ∶ Cod
preserveβᵈ {Φ = Φ}{t = t}{arg = arg} θ cv (⊢lamᵈ {cv = cvL}{B = Blam} ⊢t) ⊢r eq =
  βᵈ-reembed t (thinR cvL ⨾ thinL cv) θ
    (subst (λ C → Φ ⊢↑ (sub t (idEmb ((thinR cvL ⨾ thinL cv) ⨾ θ))) ∶ C)
           (trans (wk-cons Blam idS (arg ⇑ (thinR cv ⨾ θ))) (⇒↑-injʳ eq))
      (sub-pres (βᵈ-env-pres {u = arg ⇑ (thinR cv ⨾ θ)} ((thinR cvL ⨾ thinL cv) ⨾ θ)) ⊢t))

-- type-β (use): invert ⊢Lamᵘ (its type kept FREE as `T`), run `sub-pres` on the
-- type-β-environment, coerce the body through ∀-injectivity, re-embed along θ.  The
-- contractum's term-substitution uses the App cover `cv` (no nested Lam cover).
preserveβTᵘ : ∀ {sᵇ sᵃ sup Δ}{Φ : Cx Δ}{t : Tm (ty ∷ sᵇ)}{Cod : Ty ↑ (ty ∷ Δ)}{T : Ty ↑ Δ}
            (θ : sup ⊑ Δ)(cv : Cover sᵇ sᵃ sup)(A : Ty sᵃ)
            → Φ ⊢[ thinL cv ⨾ θ ] `Lam (use t) ∶ T
            → T ≡ (∀↑ Cod)
            → Φ ⊢↑ ((sub t (idEmb (thinL cv) ,- (A ⇑ thinR cv))) ⟨ θ ⟩) ∶ (Cod ⟪ idS ,- (A ⇑ (thinR cv ⨾ θ)) ⟫)
preserveβTᵘ {Φ = Φ}{t = t}{Cod = Cod} θ cv A (⊢Lamᵘ {B = Blam} ⊢t) eq =
  βT-reembed t (thinL cv) A (thinR cv) θ
    (subst (λ C → Φ ⊢↑ (sub t (idEmb (thinL cv ⨾ θ) ,- (A ⇑ (thinR cv ⨾ θ)))) ∶ (C ⟪ idS ,- (A ⇑ (thinR cv ⨾ θ)) ⟫))
           (∀↑-inj {B = Blam}{B′ = Cod} eq)
      (sub-pres (βT-env-pres {u = A ⇑ (thinR cv ⨾ θ)} (thinL cv ⨾ θ)) ⊢t))

-- type-β (drop): the bound ty-var is absent.
preserveβTᵈ : ∀ {sᵇ sᵃ sup Δ}{Φ : Cx Δ}{t : Tm sᵇ}{Cod : Ty ↑ (ty ∷ Δ)}{T : Ty ↑ Δ}
            (θ : sup ⊑ Δ)(cv : Cover sᵇ sᵃ sup)(A : Ty sᵃ)
            → Φ ⊢[ thinL cv ⨾ θ ] `Lam (drop t) ∶ T
            → T ≡ (∀↑ Cod)
            → Φ ⊢↑ ((sub t (idEmb (thinL cv))) ⟨ θ ⟩) ∶ (Cod ⟪ idS ,- (A ⇑ (thinR cv ⨾ θ)) ⟫)
preserveβTᵈ {Φ = Φ}{t = t}{Cod = Cod} θ cv A (⊢Lamᵈ {B = Blam} ⊢t) eq =
  βᵈ-reembed t (thinL cv) θ
    (subst (λ C → Φ ⊢↑ (sub t (idEmb (thinL cv ⨾ θ))) ∶ (C ⟪ idS ,- (A ⇑ (thinR cv ⨾ θ)) ⟫))
           (∀↑-inj {B = Blam}{B′ = Cod} eq)
      (sub-pres (βTᵈ-env-pres {u = A ⇑ (thinR cv ⨾ θ)} (thinL cv ⨾ θ)) ⊢t))

preserve : ∀ {sup Δ}{Φ : Cx Δ}{θ : sup ⊑ Δ}{e : Tm sup}{e′ : Tm ↑ sup}{A : Ty ↑ Δ}
         → Φ ⊢[ θ ] e ∶ A → e ⟶ e′ → Φ ⊢↑ (e′ ⟨ θ ⟩) ∶ A
-- term-β (lam use): invert the lam, run `sub-pres` on the β-environment (identity
-- on the function's free vars, the typed arg on the bound var), re-embed along θ.
preserve {θ = θ} (⊢app {cv = cv} ⊢l ⊢r) (β _) = preserveβᵘ θ cv ⊢l ⊢r refl
-- term-β (lam drop): the bound var is absent — drop it, no argument.
preserve {θ = θ} (⊢app {cv = cv} ⊢l ⊢r) (βᵈ _) = preserveβᵈ θ cv ⊢l ⊢r refl
-- TYPE-β (Lam use): invert the Lam, run `sub-pres` on the type-β-environment.
preserve {θ = θ} (⊢App {a = A}{cv = cv}{B = B} ⊢e) βT = preserveβTᵘ {Cod = B} θ cv A ⊢e refl
-- TYPE-β (Lam drop): the bound ty-var is absent.
preserve {θ = θ} (⊢App {a = A}{cv = cv}{B = B} ⊢e) βTᵈ = preserveβTᵈ {Cod = B} θ cv A ⊢e refl
-- ξ-fun: function reduces
preserve {θ = θ} (⊢app {r = r}{cv = cv} ⊢l ⊢r) (ξ-fun {l′ = l′} l⟶l′) =
  app↑-⟨⟩ (l′ ⟨ thinL cv ⟩) (r ⇑ thinR cv) θ
    (⊢app↑ (l′ ⟨ thinL cv ⟩ ⟨ θ ⟩) (r ⇑ (thinR cv ⨾ θ)) (preserve ⊢l l⟶l′) ⊢r)
-- ξ-arg: argument reduces
preserve {θ = θ} (⊢app {l = l}{cv = cv} ⊢l ⊢r) (ξ-arg {r′ = r′} _ r⟶r′) =
  app↑-⟨⟩ (l ⇑ thinL cv) (r′ ⟨ thinR cv ⟩) θ
    (⊢app↑ (l ⇑ (thinL cv ⨾ θ)) (r′ ⟨ thinR cv ⟩ ⟨ θ ⟩) ⊢l (preserve ⊢r r⟶r′))
-- ξ-App: type-application function reduces
preserve {θ = θ} (⊢App {a = a}{cv = cv}{B = B} ⊢e) (ξ-App {e′ = e′} e⟶e′) =
  App↑-⟨⟩ (e′ ⟨ thinL cv ⟩) (a ⇑ thinR cv) θ
    (⊢App↑ B (e′ ⟨ thinL cv ⟩ ⟨ θ ⟩) (a ⇑ (thinR cv ⨾ θ)) (preserve ⊢e e⟶e′))
