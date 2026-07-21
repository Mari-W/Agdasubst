{-# OPTIONS --rewriting --local-confluence-check #-}
-- ============================================================================
-- Co-de-Bruijn SUBSTITUTION COMPOSITION + the σ-laws.  The question this file
-- answers: does the equational σ-theory on co-de-Bruijn substitutions stay
-- "σ-calculus clean" (Map fires on the cons, first arg) or does it bottom out in
-- a thinning-⨾ obligation (which is locked to symbolic-only — see ToggleDemo)?
-- ============================================================================
module CDBcomp where
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Agda.Builtin.Equality.Rewrite
open import CDBsig
open import CDBterm
open import CDBsub

-- restrict a substitution along a thinning (the Sub analog of `rest` on contexts)
_↾_ : ∀ {Θ sup Δ} → Sub Θ Δ → sup ⊑ Δ → Sub Θ sup
[]       ↾ oz   = []
(τ ,- u) ↾ os θ = (τ ↾ θ) ,- u
(τ ,- u) ↾ o' θ = τ ↾ θ
infixl 8 _↾_

-- apply a substitution to a thing-with-thinning (substitute its support).
-- OPAQUE so that `u ⟪ τ ⟫` is a neutral — this is what lets the σ-laws (Clos/Ass)
-- be REGISTERED as rewrites (de-Bruijn σ_SP style): a transparent ⟪⟫ would make
-- the law LHSs reduce.  Proofs that need its clause use `unfolding _⟪_⟫`.
opaque
  _⟪_⟫ : ∀ {Δ Θ} → Tm ↑ Δ → Sub Θ Δ → Tm ↑ Θ
  (t ⇑ θ) ⟪ τ ⟫ = sub t (τ ↾ θ)
infixl 8 _⟪_⟫

-- substitution composition.  Recurses on the FIRST arg (the cons), exactly like
-- the de-Bruijn σ-calculus Map — so Map holds DEFINITIONALLY (it is this clause).
_⨟_ : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
[]       ⨟ τ = []
(σ ,- u) ⨟ τ = (σ ⨟ τ) ,- (u ⟪ τ ⟫)
infixl 6 _⨟_

-- Map is definitional:
Map : ∀ {Γ Δ Θ}(σ : Sub Δ Γ)(u : Tm ↑ Δ)(τ : Sub Θ Δ)
    → (σ ,- u) ⨟ τ ≡ (σ ⨟ τ) ,- (u ⟪ τ ⟫)
Map σ u τ = refl

-- ── pieces of substitution fusion (the crux of associativity) ──
-- selL/selR commute with composition (structural, no ⨾)
selL-⨟ : ∀ {Γₗ Γᵣ Γ Δ Θ}(cv : Cover Γₗ Γᵣ Γ)(σ : Sub Δ Γ)(τ : Sub Θ Δ)
       → selL cv (σ ⨟ τ) ≡ (selL cv σ) ⨟ τ
selL-⨟ czz     []       τ = refl
selL-⨟ (css c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫)) (selL-⨟ c σ τ)
selL-⨟ (cs' c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫)) (selL-⨟ c σ τ)
selL-⨟ (c's c) (σ ,- u) τ = selL-⨟ c σ τ
selR-⨟ : ∀ {Γₗ Γᵣ Γ Δ Θ}(cv : Cover Γₗ Γᵣ Γ)(σ : Sub Δ Γ)(τ : Sub Θ Δ)
       → selR cv (σ ⨟ τ) ≡ (selR cv σ) ⨟ τ
selR-⨟ czz     []       τ = refl
selR-⨟ (css c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫)) (selR-⨟ c σ τ)
selR-⨟ (cs' c) (σ ,- u) τ = selR-⨟ c σ τ
selR-⨟ (c's c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫)) (selR-⨟ c σ τ)

-- the SUBSTITUTION version of cohL/cohR (same shape, same completion):
-- restricting τ to the merged support, then split = restricting to one side.
opaque
  unfolding cop
  selL-cop : ∀ {sₗ sᵣ Δ Θ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(τ : Sub Θ Δ)
           → selL (cov (cop θ φ)) (τ ↾ out (cop θ φ)) ≡ τ ↾ θ
  selL-cop oz     oz     []       = refl
  selL-cop (os θ) (os φ) (τ ,- u) = cong (_,- u) (selL-cop θ φ τ)
  selL-cop (os θ) (o' φ) (τ ,- u) = cong (_,- u) (selL-cop θ φ τ)
  selL-cop (o' θ) (os φ) (τ ,- u) = selL-cop θ φ τ
  selL-cop (o' θ) (o' φ) (τ ,- u) = selL-cop θ φ τ
  selR-cop : ∀ {sₗ sᵣ Δ Θ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(τ : Sub Θ Δ)
           → selR (cov (cop θ φ)) (τ ↾ out (cop θ φ)) ≡ τ ↾ φ
  selR-cop oz     oz     []       = refl
  selR-cop (os θ) (os φ) (τ ,- u) = cong (_,- u) (selR-cop θ φ τ)
  selR-cop (os θ) (o' φ) (τ ,- u) = selR-cop θ φ τ
  selR-cop (o' θ) (os φ) (τ ,- u) = cong (_,- u) (selR-cop θ φ τ)
  selR-cop (o' θ) (o' φ) (τ ,- u) = selR-cop θ φ τ

-- ⟪_⟫ distributes over app↑ — uses ONLY the Sub-cohL coherences, NO ⨾
opaque
  unfolding _⟪_⟫ sub wkSub lift
  ⟪⟫-app↑ : ∀ {Δ Θ}(A B : Tm ↑ Δ)(υ : Sub Θ Δ)
          → (app↑ A B) ⟪ υ ⟫ ≡ app↑ (A ⟪ υ ⟫) (B ⟪ υ ⟫)
  ⟪⟫-app↑ (l ⇑ θ) (r ⇑ φ) υ =
    cong₂ app↑ (cong (sub l) (selL-cop θ φ υ)) (cong (sub r) (selR-cop θ φ υ))

-- ── weakening lemmas (test: can fusion stay ⨾-free using o'-weakening?) ──
wk↑ : ∀ {Δ} → Tm ↑ Δ → Tm ↑ (tt ∷ Δ)
wk↑ (t ⇑ ξ) = t ⇑ o' ξ

opaque
  unfolding wkSub
  selL-wk : ∀ {Γₗ Γᵣ Γ Δ}(cv : Cover Γₗ Γᵣ Γ)(ρ : Sub Δ Γ) → selL cv (wkSub ρ) ≡ wkSub (selL cv ρ)
  selL-wk czz     []             = refl
  selL-wk (css c) (ρ ,- (t ⇑ ξ)) = cong (_,- (t ⇑ o' ξ)) (selL-wk c ρ)
  selL-wk (cs' c) (ρ ,- (t ⇑ ξ)) = cong (_,- (t ⇑ o' ξ)) (selL-wk c ρ)
  selL-wk (c's c) (ρ ,- u)       = selL-wk c ρ
  selR-wk : ∀ {Γₗ Γᵣ Γ Δ}(cv : Cover Γₗ Γᵣ Γ)(ρ : Sub Δ Γ) → selR cv (wkSub ρ) ≡ wkSub (selR cv ρ)
  selR-wk czz     []             = refl
  selR-wk (css c) (ρ ,- (t ⇑ ξ)) = cong (_,- (t ⇑ o' ξ)) (selR-wk c ρ)
  selR-wk (cs' c) (ρ ,- u)       = selR-wk c ρ
  selR-wk (c's c) (ρ ,- (t ⇑ ξ)) = cong (_,- (t ⇑ o' ξ)) (selR-wk c ρ)

-- app↑ commutes with o'-weakening — DEFINITIONAL via cop (o' θ)(o' φ) clause, NO ⨾
opaque
  unfolding cop
  app↑-wk : ∀ {Δ}(A B : Tm ↑ Δ) → app↑ (wk↑ A) (wk↑ B) ≡ wk↑ (app↑ A B)
  app↑-wk (l ⇑ θ) (r ⇑ φ) = refl

-- FINDING: `sub t (wkSub ρ) ≡ wk↑ (sub t ρ)` is ⨾-free in var/app (above), but
-- the LAM case is NOT: going under the binder, the weakening var must be inserted
-- AFTER the bound var — a middle-insertion `⟨ os (o' oi) ⟩`, i.e. `_⨾_`.  So the
-- substitution-fusion lemma (the crux of Ass) intrinsically uses `⨾` in its PROOF.
-- That is fine and expected: `⨾` is symbolic-but-lawful (oi⨾/⨾oi/⨾⨾ are rewrites),
-- so the proof goes through propositionally — exactly as the de-Bruijn σ-calculus
-- proves Ass from Clos.  The `⨾` toggle only forbids making `⨾`'s CLAUSES rewrites;
-- it never blocks a propositional proof.  (Full fusion = McBride §9 hereditary subst.)
--   var/app fragment, ⨾-free:
opaque
  unfolding sub wkSub lift
  sub-wk-var : ∀ {Δ}(u : Tm ↑ Δ) → sub var (wkSub ([] ,- u)) ≡ wk↑ (sub var ([] ,- u))
  sub-wk-var u = refl

-- ── THE fusion crux: app↑ commutes with renaming = cop commutes with ⨾ ──
-- (this is what Clos/Ass bottom out in; the only place ⨾ is needed, propositionally)
open import CDBterm using (_⟨_⟩; thn; thing)
opaque
  unfolding cop _⨾_
  cop-⨾ : ∀ {Γ₁ Γ₂ Δ Δ′}(θ₁ : Γ₁ ⊑ Δ)(θ₂ : Γ₂ ⊑ Δ)(ψ : Δ ⊑ Δ′)
        → cop (θ₁ ⨾ ψ) (θ₂ ⨾ ψ)
        ≡ mkCop (inl (cop θ₁ θ₂)) (inr (cop θ₁ θ₂)) (out (cop θ₁ θ₂) ⨾ ψ) (cov (cop θ₁ θ₂))
  cop-⨾ θ₁      θ₂      oz       = refl
  cop-⨾ θ₁      θ₂      (o' ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl
  cop-⨾ (os θ₁) (os θ₂) (os ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl
  cop-⨾ (os θ₁) (o' θ₂) (os ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl
  cop-⨾ (o' θ₁) (os θ₂) (os ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl
  cop-⨾ (o' θ₁) (o' θ₂) (os ψ) rewrite cop-⨾ θ₁ θ₂ ψ = refl

  -- app↑/lam↑ commute with renaming (immediate from cop-⨾ and the ⨾ clauses)
  app↑-⟨⟩ : ∀ {Δ Δ′ sl sr}(l : Tm sl)(α : sl ⊑ Δ)(r : Tm sr)(β : sr ⊑ Δ)(ψ : Δ ⊑ Δ′)
          → (app↑ (l ⇑ α) (r ⇑ β)) ⟨ ψ ⟩ ≡ app↑ ((l ⇑ α) ⟨ ψ ⟩) ((r ⇑ β) ⟨ ψ ⟩)
  app↑-⟨⟩ l α r β ψ rewrite cop-⨾ α β ψ = refl
  lam↑-⟨⟩ : ∀ {Δ Δ′ sup}(t : Tm sup)(ξ : sup ⊑ (tt ∷ Δ))(ψ : Δ ⊑ Δ′)
          → (lam↑ (t ⇑ ξ)) ⟨ ψ ⟩ ≡ lam↑ ((t ⇑ ξ) ⟨ os ψ ⟩)
  lam↑-⟨⟩ t (os ξ) ψ = refl
  lam↑-⟨⟩ t (o' ξ) ψ = refl

-- thin the TARGET of a substitution by a thinning (renames each entry, uses ⨾)
thinSub : ∀ {Δ Δ′ Γ} → Δ ⊑ Δ′ → Sub Δ Γ → Sub Δ′ Γ
thinSub ψ []             = []
thinSub ψ (σ ,- (t ⇑ ξ)) = thinSub ψ σ ,- (t ⇑ (ξ ⨾ ψ))

selL-thin : ∀ {Γₗ Γᵣ Γ Δ Δ′}(cv : Cover Γₗ Γᵣ Γ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ)
          → selL cv (thinSub ψ σ) ≡ thinSub ψ (selL cv σ)
selL-thin czz     ψ []             = refl
selL-thin (css c) ψ (σ ,- (t ⇑ ξ)) = cong (_,- (t ⇑ (ξ ⨾ ψ))) (selL-thin c ψ σ)
selL-thin (cs' c) ψ (σ ,- (t ⇑ ξ)) = cong (_,- (t ⇑ (ξ ⨾ ψ))) (selL-thin c ψ σ)
selL-thin (c's c) ψ (σ ,- u)       = selL-thin c ψ σ
selR-thin : ∀ {Γₗ Γᵣ Γ Δ Δ′}(cv : Cover Γₗ Γᵣ Γ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ)
          → selR cv (thinSub ψ σ) ≡ thinSub ψ (selR cv σ)
selR-thin czz     ψ []             = refl
selR-thin (css c) ψ (σ ,- (t ⇑ ξ)) = cong (_,- (t ⇑ (ξ ⨾ ψ))) (selR-thin c ψ σ)
selR-thin (cs' c) ψ (σ ,- u)       = selR-thin c ψ σ
selR-thin (c's c) ψ (σ ,- (t ⇑ ξ)) = cong (_,- (t ⇑ (ξ ⨾ ψ))) (selR-thin c ψ σ)

-- ⨾ clause-lemmas + oe-absorption (propositional; ⨾/oe stay symbolic for confluence)
opaque
  unfolding _⨾_ oe
  ⨾-oss : ∀ {Γ Δ Θ}(ξ : Γ ⊑ Δ)(ψ : Δ ⊑ Θ) → os ξ ⨾ os ψ ≡ os (ξ ⨾ ψ)
  ⨾-oss ξ ψ = refl
  ⨾-o's : ∀ {Γ Δ Θ}(ξ : Γ ⊑ Δ)(ψ : Δ ⊑ Θ) → o' ξ ⨾ os ψ ≡ o' (ξ ⨾ ψ)
  ⨾-o's ξ ψ = refl
  oe⨾ : ∀ {Δ Δ′}(ψ : Δ ⊑ Δ′) → oe ⨾ ψ ≡ oe
  oe⨾ oz      = refl
  oe⨾ (os ψ) = cong o' (oe⨾ ψ)
  oe⨾ (o' ψ) = cong o' (oe⨾ ψ)

-- Tm↑ wrappers of the renaming-commutations
opaque
  unfolding cop _⨾_
  app↑-⟨⟩↑ : ∀ {Δ Δ′}(A B : Tm ↑ Δ)(ψ : Δ ⊑ Δ′) → (app↑ A B) ⟨ ψ ⟩ ≡ app↑ (A ⟨ ψ ⟩) (B ⟨ ψ ⟩)
  app↑-⟨⟩↑ (l ⇑ α) (r ⇑ β) ψ = app↑-⟨⟩ l α r β ψ
  lam↑-⟨⟩↑ : ∀ {Δ Δ′}(X : Tm ↑ (tt ∷ Δ))(ψ : Δ ⊑ Δ′) → (lam↑ X) ⟨ ψ ⟩ ≡ lam↑ (X ⟨ os ψ ⟩)
  lam↑-⟨⟩↑ (t ⇑ ξ) ψ = lam↑-⟨⟩ t ξ ψ

-- weakening commutes with target-thinning
opaque
  unfolding wkSub
  wkSub-thinSub : ∀ {Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ) → wkSub (thinSub ψ σ) ≡ thinSub (os ψ) (wkSub σ)
  wkSub-thinSub ψ []             = refl
  wkSub-thinSub ψ (σ ,- (t ⇑ ξ)) =
    cong₂ _,-_ (wkSub-thinSub ψ σ) (cong (t ⇑_) (sym (⨾-o's ξ ψ)))

-- the lift (wkSub σ ,- fresh) commutes with target-thinning (uses ⨾-oss + oe⨾)
liftThin : ∀ {Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ)
         → (wkSub (thinSub ψ σ) ,- (var ⇑ os oe)) ≡ thinSub (os ψ) (wkSub σ ,- (var ⇑ os oe))
liftThin ψ σ = cong₂ _,-_ (wkSub-thinSub ψ σ) (cong (var ⇑_) (sym (trans (⨾-oss oe ψ) (cong os (oe⨾ ψ)))))

-- SUB COMMUTES WITH RENAMING (the McBride §9 lemma; ⨾ lives here, propositionally)
opaque
  unfolding sub wkSub lift
  sub-thin : ∀ {Γ Δ Δ′}(t : Tm Γ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ) → sub t (thinSub ψ σ) ≡ (sub t σ) ⟨ ψ ⟩
  sub-thin var ψ ([] ,- (t ⇑ η)) = refl
  sub-thin (app (pair l r cv)) ψ σ =
    trans (cong₂ app↑ (cong (sub l) (selL-thin cv ψ σ)) (cong (sub r) (selR-thin cv ψ σ)))
    (trans (cong₂ app↑ (sub-thin l ψ (selL cv σ)) (sub-thin r ψ (selR cv σ)))
           (sym (app↑-⟨⟩↑ (sub l (selL cv σ)) (sub r (selR cv σ)) ψ)))
  sub-thin (lam (use t)) ψ σ =
    trans (cong (λ e → lam↑ (sub t e)) (liftThin ψ σ))
    (trans (cong lam↑ (sub-thin t (os ψ) (wkSub σ ,- (var ⇑ os oe))))
           (sym (lam↑-⟨⟩↑ (sub t (wkSub σ ,- (var ⇑ os oe))) ψ)))
  sub-thin (lam (drop t)) ψ σ = cong (λ Z → lam (drop (thing Z)) ⇑ thn Z) (sub-thin t ψ σ)

-- bridges: wkSub = thinSub (o' oi),  wk↑ A = A⟨o' oi⟩   (both via the ⨾-o' clause)
opaque
  unfolding _⨾_
  ⨾-o' : ∀ {Γ Δ Θ}(ξ : Γ ⊑ Δ)(ψ : Δ ⊑ Θ) → ξ ⨾ o' ψ ≡ o' (ξ ⨾ ψ)
  ⨾-o' ξ ψ = refl
wk↑≡⟨⟩ : ∀ {Δ}(A : Tm ↑ Δ) → wk↑ A ≡ A ⟨ o' oi ⟩
wk↑≡⟨⟩ (t ⇑ θ) = cong (t ⇑_) (sym (⨾-o' θ oi))
opaque
  unfolding wkSub
  wkSub≡thin : ∀ {Δ Γ}(ρ : Sub Δ Γ) → wkSub ρ ≡ thinSub (o' oi) ρ
  wkSub≡thin []             = refl
  wkSub≡thin (ρ ,- (t ⇑ ξ)) = cong₂ _,-_ (wkSub≡thin ρ) (cong (t ⇑_) (sym (⨾-o' ξ oi)))
sub-wk : ∀ {Γ Δ}(t : Tm Γ)(ρ : Sub Δ Γ) → sub t (wkSub ρ) ≡ wk↑ (sub t ρ)
sub-wk t ρ = trans (cong (sub t) (wkSub≡thin ρ))
                   (trans (sub-thin t (o' oi) ρ) (sym (wk↑≡⟨⟩ (sub t ρ))))

-- weakening commutes with restriction (structural)
opaque
  unfolding wkSub
  wk-↾ : ∀ {Θ sup Δ}(τ : Sub Θ Δ)(θ : sup ⊑ Δ) → (wkSub τ) ↾ θ ≡ wkSub (τ ↾ θ)
  wk-↾ []             oz     = refl
  wk-↾ (τ ,- (t ⇑ ξ)) (os θ) = cong (_,- (t ⇑ o' ξ)) (wk-↾ τ θ)
  wk-↾ (τ ,- u)       (o' θ) = wk-↾ τ θ

-- ⟪_⟫ distributes over lam↑ (use case via wk-↾; drop case via sub-wk)
opaque
  unfolding _⟪_⟫ sub wkSub lift
  ⟪⟫-lam↑ : ∀ {Δ Θ}(X : Tm ↑ (tt ∷ Δ))(υ : Sub Θ Δ)
          → (lam↑ X) ⟪ υ ⟫ ≡ lam↑ (X ⟪ wkSub υ ,- (var ⇑ os oe) ⟫)
  ⟪⟫-lam↑ (t ⇑ os ξ) υ = cong (λ e → lam↑ (sub t (e ,- (var ⇑ os oe)))) (sym (wk-↾ υ ξ))
  ⟪⟫-lam↑ (t ⇑ o' ξ) υ =
    sym (trans (cong (λ e → lam↑ (sub t e)) (wk-↾ υ ξ)) (cong lam↑ (sub-wk t (υ ↾ ξ))))

-- restricting by the empty thinning kills the substitution (needs oe opaque-unfold)
opaque
  unfolding oe
  ↾-oe : ∀ {Θ Δ}(τ : Sub Θ Δ) → τ ↾ oe ≡ []
  ↾-oe []       = refl
  ↾-oe (τ ,- u) = ↾-oe τ

-- weakened composition: (wkSub σ) ⨟ (wkSub υ , fresh) = wkSub (σ ⨟ υ)
opaque
  unfolding _⟪_⟫ sub wkSub lift
  wkSub-⨟ : ∀ {Γ Δ Θ}(σ : Sub Δ Γ)(υ : Sub Θ Δ)
          → (wkSub σ) ⨟ (wkSub υ ,- (var ⇑ os oe)) ≡ wkSub (σ ⨟ υ)
  wkSub-⨟ []             υ = refl
  wkSub-⨟ (σ ,- (t ⇑ ξ)) υ =
    cong₂ _,-_ (wkSub-⨟ σ υ) (trans (cong (sub t) (wk-↾ υ ξ)) (sub-wk t (υ ↾ ξ)))

-- the binder lift commutes with composition
opaque
  unfolding _⟪_⟫ sub wkSub lift
  lift-⨟ : ∀ {Γ Δ Θ}(σ : Sub Δ Γ)(υ : Sub Θ Δ)
         → (wkSub σ ,- (var ⇑ os oe)) ⨟ (wkSub υ ,- (var ⇑ os oe)) ≡ wkSub (σ ⨟ υ) ,- (var ⇑ os oe)
  lift-⨟ σ υ = cong₂ _,-_ (wkSub-⨟ σ υ) (cong (λ e → sub var (e ,- (var ⇑ os oe))) (↾-oe (wkSub υ)))

-- ══ Clos: substitution fusion  (e[σ])[υ] = e[σ⨟υ] ══
opaque
  unfolding _⟪_⟫ sub wkSub lift
  sub-fusion : ∀ {Γ Δ Θ}(t : Tm Γ)(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (sub t σ) ⟪ υ ⟫ ≡ sub t (σ ⨟ υ)
  sub-fusion var ([] ,- u) υ = refl
  sub-fusion (app (pair l r cv)) σ υ =
    trans (⟪⟫-app↑ (sub l (selL cv σ)) (sub r (selR cv σ)) υ)
    (trans (cong₂ app↑ (sub-fusion l (selL cv σ) υ) (sub-fusion r (selR cv σ) υ))
           (cong₂ app↑ (cong (sub l) (sym (selL-⨟ cv σ υ))) (cong (sub r) (sym (selR-⨟ cv σ υ)))))
  sub-fusion (lam (use t)) σ υ =
    trans (⟪⟫-lam↑ (sub t (wkSub σ ,- (var ⇑ os oe))) υ)
          (cong lam↑ (trans (sub-fusion t (wkSub σ ,- (var ⇑ os oe)) (wkSub υ ,- (var ⇑ os oe)))
                            (cong (sub t) (lift-⨟ σ υ))))
  sub-fusion (lam (drop t)) σ υ = cong (λ Z → lam (drop (thing Z)) ⇑ thn Z) (sub-fusion t σ υ)

-- restriction commutes with composition
↾-⨟ : ∀ {Δ Δ′ Θ sup}(τ : Sub Δ′ Δ)(θ : sup ⊑ Δ)(υ : Sub Θ Δ′) → (τ ↾ θ) ⨟ υ ≡ (τ ⨟ υ) ↾ θ
↾-⨟ []       oz     υ = refl
↾-⨟ (τ ,- u) (os θ) υ = cong (_,- (u ⟪ υ ⟫)) (↾-⨟ τ θ υ)
↾-⨟ (τ ,- u) (o' θ) υ = ↾-⨟ τ θ υ

-- ══ Ass: associativity of substitution composition  (σ⨟τ)⨟υ = σ⨟(τ⨟υ) ══
-- ⟪⟫-fusion: the Clos law packaged for the cons-entry (needs ⟪⟫ unfolded)
opaque
  unfolding _⟪_⟫ sub wkSub lift
  ⟪⟫-fusion : ∀ {Δ Δ′ Θ}(u : Tm ↑ Δ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′)
            → (u ⟪ τ ⟫) ⟪ υ ⟫ ≡ u ⟪ τ ⨟ υ ⟫
  ⟪⟫-fusion (t ⇑ θ) τ υ = trans (sub-fusion t (τ ↾ θ) υ) (cong (sub t) (↾-⨟ τ θ υ))

Ass : ∀ {Γ Δ Δ′ Θ}(σ : Sub Δ Γ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
Ass []             τ υ = refl
Ass (σ ,- (t ⇑ θ)) τ υ = cong₂ _,-_ (Ass σ τ υ) (⟪⟫-fusion (t ⇑ θ) τ υ)

-- REGISTER the composition laws as REWRITES (now definitional, σ_SP-style)
{-# REWRITE ⟪⟫-fusion Ass #-}

-- ══ VarCons-z is definitional ══
opaque
  unfolding sub lift
  VarCons-z : ∀ {Δ}(u : Tm ↑ Δ) → sub var ([] ,- u) ≡ u
  VarCons-z u = refl

-- identity substitution and the identity laws
opaque
  idS : ∀ {Γ} → Sub Γ Γ
  idS {[]}    = []
  idS {_ ∷ Γ} = wkSub idS ,- (var ⇑ os oe)

-- weakening absorbs a cons on the right
opaque
  unfolding _⟪_⟫ sub wkSub lift
  wk-⨟-cons : ∀ {Γ Δ Θ}(σ : Sub Δ Γ)(τ : Sub Θ Δ)(u : Tm ↑ Θ) → wkSub σ ⨟ (τ ,- u) ≡ σ ⨟ τ
  wk-⨟-cons []             τ u = refl
  wk-⨟-cons (σ ,- (t ⇑ ξ)) τ u = cong (_,- sub t (τ ↾ ξ)) (wk-⨟-cons σ τ u)

-- ══ IdL: id ⨟ σ = σ ══
opaque
  unfolding _⟪_⟫ idS sub wkSub lift
  IdL : ∀ {Γ Δ}(σ : Sub Δ Γ) → idS ⨟ σ ≡ σ
  IdL []             = refl
  IdL (σ ,- (t ⇑ ξ)) =
    cong₂ _,-_ (trans (wk-⨟-cons idS σ (t ⇑ ξ)) (IdL σ))
               (cong (sub var) (cong (_,- (t ⇑ ξ)) (↾-oe σ)))

-- ── the laws are now DEFINITIONAL (the registered rewrites fire by refl) ──
{-# REWRITE IdL #-}
_Ass-def : ∀ {Γ Δ Δ′ Θ}(σ : Sub Δ Γ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
_Ass-def σ τ υ = refl
_Clos-def : ∀ {Δ Δ′ Θ}(u : Tm ↑ Δ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (u ⟪ τ ⟫) ⟪ υ ⟫ ≡ u ⟪ τ ⨟ υ ⟫
_Clos-def u τ υ = refl
_IdL-def : ∀ {Γ Δ}(σ : Sub Δ Γ) → idS ⨟ σ ≡ σ
_IdL-def σ = refl

-- ── right identity: sub t idEmb θ ≡ t⇑θ  (support-tracking; gives IdSubst, IdR) ──
opaque
  thinL : ∀ {sₗ sᵣ Γ} → Cover sₗ sᵣ Γ → sₗ ⊑ Γ
  thinL czz = oz ; thinL (css c) = os (thinL c) ; thinL (cs' c) = os (thinL c) ; thinL (c's c) = o' (thinL c)
  thinR : ∀ {sₗ sᵣ Γ} → Cover sₗ sᵣ Γ → sᵣ ⊑ Γ
  thinR czz = oz ; thinR (css c) = os (thinR c) ; thinR (cs' c) = o' (thinR c) ; thinR (c's c) = os (thinR c)
opaque
  idEmb : ∀ {sup Δ} → sup ⊑ Δ → Sub Δ sup
  idEmb oz     = []
  idEmb (os θ) = wkSub (idEmb θ) ,- (var ⇑ os oe)
  idEmb (o' θ) = wkSub (idEmb θ)
opaque
  unfolding oe
  oe-unique : ∀ {Δ}(θ : [] ⊑ Δ) → θ ≡ oe
  oe-unique oz     = refl
  oe-unique (o' θ) = cong o' (oe-unique θ)
-- cop of a cover's two thinnings reconstructs the cover, out = oi  (like cop-⨾)
opaque
  unfolding cop thinL thinR
  cop-thin : ∀ {sₗ sᵣ Γ}(cv : Cover sₗ sᵣ Γ)
           → cop (thinL cv) (thinR cv) ≡ mkCop (thinL cv) (thinR cv) oi cv
  cop-thin czz                  = refl
  cop-thin (css c) rewrite cop-thin c = refl
  cop-thin (cs' c) rewrite cop-thin c = refl
  cop-thin (c's c) rewrite cop-thin c = refl


-- o'-variant: wkSub (thinSub θ ρ) = thinSub (o' θ) ρ
opaque
  unfolding wkSub
  wkSub-thinSub-o' : ∀ {Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(ρ : Sub Δ Γ) → wkSub (thinSub ψ ρ) ≡ thinSub (o' ψ) ρ
  wkSub-thinSub-o' ψ []             = refl
  wkSub-thinSub-o' ψ (ρ ,- (t ⇑ ξ)) = cong₂ _,-_ (wkSub-thinSub-o' ψ ρ) (cong (t ⇑_) (sym (⨾-o' ξ ψ)))

-- idEmb θ is idS renamed by θ
opaque
  unfolding idS wkSub idEmb thinL thinR
  idEmb-thinSub : ∀ {sup Δ}(θ : sup ⊑ Δ) → idEmb θ ≡ thinSub θ idS
  idEmb-thinSub oz     = refl
  idEmb-thinSub (os θ) =
    cong₂ _,-_ (trans (cong wkSub (idEmb-thinSub θ)) (wkSub-thinSub θ idS))
               (cong (var ⇑_) (sym (trans (⨾-oss oe θ) (cong os (oe⨾ θ)))))
  idEmb-thinSub (o' θ) = trans (cong wkSub (idEmb-thinSub θ)) (wkSub-thinSub-o' θ idS)
  -- selecting idS along a cover = the embedding of the cover-thinning
  selL-idS : ∀ {sₗ sᵣ Γ}(cv : Cover sₗ sᵣ Γ) → selL cv idS ≡ idEmb (thinL cv)
  selL-idS czz     = refl
  selL-idS (css c) = cong (_,- (var ⇑ os oe)) (trans (selL-wk c idS) (cong wkSub (selL-idS c)))
  selL-idS (cs' c) = cong (_,- (var ⇑ os oe)) (trans (selL-wk c idS) (cong wkSub (selL-idS c)))
  selL-idS (c's c) = trans (selL-wk c idS) (cong wkSub (selL-idS c))
  selR-idS : ∀ {sₗ sᵣ Γ}(cv : Cover sₗ sᵣ Γ) → selR cv idS ≡ idEmb (thinR cv)
  selR-idS czz     = refl
  selR-idS (css c) = cong (_,- (var ⇑ os oe)) (trans (selR-wk c idS) (cong wkSub (selR-idS c)))
  selR-idS (cs' c) = trans (selR-wk c idS) (cong wkSub (selR-idS c))
  selR-idS (c's c) = cong (_,- (var ⇑ os oe)) (trans (selR-wk c idS) (cong wkSub (selR-idS c)))

-- ══ IdSubst:  sub t idS  =  t ⇑ oi ══
opaque
  unfolding idS oe oi sub wkSub idEmb lift
  sub-idS : ∀ {sup}(t : Tm sup) → sub t idS ≡ (t ⇑ oi)
  sub-idS var = refl
  sub-idS (app (pair l r cv)) =
    trans (cong₂ app↑
            (trans (cong (sub l) (trans (selL-idS cv) (idEmb-thinSub (thinL cv))))
                   (trans (sub-thin l (thinL cv) idS) (cong (_⟨ thinL cv ⟩) (sub-idS l))))
            (trans (cong (sub r) (trans (selR-idS cv) (idEmb-thinSub (thinR cv))))
                   (trans (sub-thin r (thinR cv) idS) (cong (_⟨ thinR cv ⟩) (sub-idS r)))))
          (cong (λ c → app (pair l r (cov c)) ⇑ out c) (cop-thin cv))
  sub-idS (lam (use t))  = cong lam↑ (sub-idS t)
  sub-idS (lam (drop t)) = cong (λ Z → lam (drop (thing Z)) ⇑ thn Z) (sub-idS t)

-- sub t idEmb θ = t⇑θ  (general), idS↾θ = idEmb θ,  then ⟪⟫-id and IdR
sub-idEmb : ∀ {sup Δ}(t : Tm sup)(θ : sup ⊑ Δ) → sub t (idEmb θ) ≡ (t ⇑ θ)
sub-idEmb t θ = trans (cong (sub t) (idEmb-thinSub θ)) (trans (sub-thin t θ idS) (cong (_⟨ θ ⟩) (sub-idS t)))
opaque
  unfolding idS wkSub idEmb thinL thinR
  idS↾-idEmb : ∀ {sup Δ}(θ : sup ⊑ Δ) → idS ↾ θ ≡ idEmb θ
  idS↾-idEmb oz     = refl
  idS↾-idEmb (os θ) = cong (_,- (var ⇑ os oe)) (trans (wk-↾ idS θ) (cong wkSub (idS↾-idEmb θ)))
  idS↾-idEmb (o' θ) = trans (wk-↾ idS θ) (cong wkSub (idS↾-idEmb θ))
opaque
  unfolding _⟪_⟫ sub wkSub lift
  ⟪⟫-id : ∀ {Δ}(u : Tm ↑ Δ) → u ⟪ idS ⟫ ≡ u
  ⟪⟫-id (t ⇑ θ) = trans (cong (sub t) (idS↾-idEmb θ)) (sub-idEmb t θ)

-- ══ IdR:  σ ⨟ idS  =  σ ══
IdR : ∀ {Γ Δ}(σ : Sub Δ Γ) → σ ⨟ idS ≡ σ
IdR []       = refl
IdR (σ ,- u) = cong₂ _,-_ (IdR σ) (⟪⟫-id u)

{-# REWRITE ⟪⟫-id IdR #-}

-- IdCons (idS's defining clause, exposed)
opaque
  unfolding idS wkSub idEmb thinL thinR
  IdCons : ∀ {s Γ} → idS {s ∷ Γ} ≡ wkSub idS ,- (var ⇑ os oe)
  IdCons = refl

-- now that sub/wkSub are opaque, IdSubst and ShiftCons register too
{-# REWRITE sub-idS #-}

-- Inst-· / Inst-ƛ as sub's clauses, exposed (need unfolding sub)
opaque
  unfolding sub lift
  Inst-· : ∀ {sₗ sᵣ Γ Δ}(l : Tm sₗ)(r : Tm sᵣ)(cv : Cover sₗ sᵣ Γ)(σ : Sub Δ Γ)
         → sub (app (pair l r cv)) σ ≡ app↑ (sub l (selL cv σ)) (sub r (selR cv σ))
  Inst-· l r cv σ = refl
  Inst-ƛ : ∀ {Γ Δ}(t : Tm (tt ∷ Γ))(σ : Sub Δ Γ)
         → sub (lam (use t)) σ ≡ lam↑ (sub t (lift σ))
  Inst-ƛ t σ = refl
{-# REWRITE VarCons-z #-}

-- thinSub is functorial, idEmb commutes with thinning, selL of idEmb
thinSub-∘ : ∀ {Δ Δ′ Δ″ Γ}(φ : Δ ⊑ Δ′)(ψ : Δ′ ⊑ Δ″)(ρ : Sub Δ Γ)
          → thinSub ψ (thinSub φ ρ) ≡ thinSub (φ ⨾ ψ) ρ
thinSub-∘ φ ψ []             = refl
thinSub-∘ φ ψ (ρ ,- (t ⇑ ξ)) = cong₂ _,-_ (thinSub-∘ φ ψ ρ) refl
thinSub-idEmb : ∀ {sup Δ Δ′}(ψ : Δ ⊑ Δ′)(φ : sup ⊑ Δ) → thinSub ψ (idEmb φ) ≡ idEmb (φ ⨾ ψ)
thinSub-idEmb ψ φ = trans (cong (thinSub ψ) (idEmb-thinSub φ))
                          (trans (thinSub-∘ φ ψ idS) (sym (idEmb-thinSub (φ ⨾ ψ))))
selL-idEmb : ∀ {sₗ sᵣ sup Δ}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ)
           → selL cv (idEmb θ) ≡ idEmb (thinL cv ⨾ θ)
selL-idEmb cv θ = trans (cong (selL cv) (idEmb-thinSub θ))
                  (trans (selL-thin cv θ idS)
                  (trans (cong (thinSub θ) (selL-idS cv)) (thinSub-idEmb θ (thinL cv))))
selR-idEmb : ∀ {sₗ sᵣ sup Δ}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ)
           → selR cv (idEmb θ) ≡ idEmb (thinR cv ⨾ θ)
selR-idEmb cv θ = trans (cong (selR cv) (idEmb-thinSub θ))
                  (trans (selR-thin cv θ idS)
                  (trans (cong (thinSub θ) (selR-idS cv)) (thinSub-idEmb θ (thinR cv))))

-- NOTE: registering {selL-idS selR-idS selL-idEmb selR-idEmb sub-idEmb cop-⨾ cop-thin
-- Inst-· Inst-ƛ} to join the IdSubst×Inst pair gives conf=14 — NOT the ⨾ toggle
-- (cop-⨾/cop-thin absorb ⨾ symbolically) but unjoined critical pairs in the COPRODUCT
-- algebra (cop-thin's LHS reduces since thinL/thinR are transparent; cop-⨾ races
-- cop-oiL/⨾⨾).  Closing them is a Knuth-Bendix completion of the cop algebra
-- (needs thinL/thinR opaque + the closing rules).  The lemmas above are kept proven.

-- combined law: cop of post-composed cover-thinnings (stable LHS: thinL/thinR opaque)
cop-thin-⨾ : ∀ {sₗ sᵣ sup Δ}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ)
           → cop (thinL cv ⨾ θ) (thinR cv ⨾ θ) ≡ mkCop (thinL cv) (thinR cv) θ cv
cop-thin-⨾ cv θ =
  trans (cop-⨾ (thinL cv) (thinR cv) θ)
        (cong (λ c → mkCop (inl c) (inr c) (out c ⨾ θ) (cov c)) (cop-thin cv))

-- THE COPRODUCT-ALGEBRA COMPLETION: now IdSubst AND Inst-·/Inst-ƛ both compute
{-# REWRITE selL-idS selR-idS selL-idEmb selR-idEmb sub-idEmb cop-thin cop-thin-⨾ Inst-· #-}


-- lift of an identity = identity at the bigger scope (closes the Inst-ƛ × IdSubst pair)
opaque
  unfolding idS idEmb oi
  idS≡idEmb-oi : ∀ {Γ} → idS {Γ} ≡ idEmb (oi {Γ})
  idS≡idEmb-oi {[]}    = refl
  idS≡idEmb-oi {s ∷ Γ} = cong (λ ρ → wkSub ρ ,- (var ⇑ os oe)) idS≡idEmb-oi
opaque
  unfolding lift idEmb
  lift-idEmb : ∀ {sup Δ}(θ : sup ⊑ Δ) → lift (idEmb θ) ≡ idEmb (os θ)
  lift-idEmb θ = refl
lift-idS : ∀ {Γ} → lift (idS {Γ}) ≡ idEmb (os (oi {Γ}))
lift-idS = trans (cong lift idS≡idEmb-oi) (lift-idEmb oi)

{-# REWRITE lift-idEmb lift-idS Inst-ƛ #-}

{-# REWRITE ↾-oe #-}

-- ════════════════════════════════════════════════════════════════════════════
-- FAITHFULNESS AUDIT: wkSub and lift are DERIVED from the σ_SP primitive ↑ (=wk),
-- not new primitives.  ↑ = the shift substitution; weaken = _⨟ ↑; ⇑σ = var₀ ∙ (σ⨟↑).
-- ════════════════════════════════════════════════════════════════════════════
opaque
  ↑ₛ : ∀ {Γ} → Sub (tt ∷ Γ) Γ          -- the σ_SP shift primitive `↑` (OPAQUE atom, ≠ wkSub)
  ↑ₛ = wkSub idS
opaque
  unfolding _⟪_⟫ wkSub ↑ₛ
  -- wkSub is DERIVED:  wkSub σ ≡ σ ⨟ ↑
  wkSub≡⨟↑ : ∀ {Γ Δ}(σ : Sub Δ Γ) → wkSub σ ≡ σ ⨟ ↑ₛ
  wkSub≡⨟↑ []             = refl
  wkSub≡⨟↑ (σ ,- (t ⇑ θ)) =
    cong₂ _,-_ (wkSub≡⨟↑ σ)
      (sym (trans (cong (sub t) (trans (wk-↾ idS θ) (cong wkSub (idS↾-idEmb θ))))
                  (sub-wk t (idEmb θ))))
-- lift IS the σ_SP up-arrow:  lift σ ≡ var₀ ∙ (σ ⨟ ↑)   ( = (σ ⨟ ↑) ,- var₀ )
opaque
  unfolding lift
  lift≡⇑ : ∀ {Γ Δ}(σ : Sub Δ Γ) → lift σ ≡ (σ ⨟ ↑ₛ) ,- (var ⇑ os oe)
  lift≡⇑ σ = cong (_,- (var ⇑ os oe)) (wkSub≡⨟↑ σ)

-- ════════════════════════════════════════════════════════════════════════════
-- η-laws via the OPAQUE cons `∙`, WITHOUT the non-primitive `wk-⨟-cons` rewrite.
-- Stripping `wk-⨟-cons` from the rewrite set removes the overlap that blocked
-- SCons-∙ at conf 1; `↑ ⨟ σ` is then STUCK (⨟ on the opaque `wkSub idS`), so
-- SCons-∙'s LHS has no competing redex.  ShiftCons is recovered as a LEMMA.
opaque
  _∙_ : ∀ {Γ Δ} → Tm ↑ Δ → Sub Δ Γ → Sub Δ (tt ∷ Γ)
  u ∙ σ = σ ,- u
infixr 5 _∙_
opaque
  unfolding _⟪_⟫ sub wkSub lift _∙_ ↑ₛ
  SCons-∙ : ∀ {Γ Δ}(σ : Sub Δ (tt ∷ Γ)) → ((var ⇑ os oe) ⟪ σ ⟫) ∙ (↑ₛ ⨟ σ) ≡ σ
  SCons-∙ (σ ,- u) = cong (_,- u) (trans (wk-⨟-cons idS σ u) (IdL σ))
opaque
  unfolding _∙_ ↑ₛ
  IdCons-∙ : ∀ {Γ} → (var ⇑ os oe) ∙ (↑ₛ {Γ}) ≡ idS {tt ∷ Γ}
  IdCons-∙ = sym IdCons
{-# REWRITE SCons-∙ IdCons-∙ #-}

-- ── the rest of the cons-laws on the opaque `∙` (point-free σ-calculus completion) ──
-- With ALL of VarCons/Map/ShiftCons/SCons/IdCons as ∙-rewrites, the system is the known
-- confluent σ_SP completion: e.g. VarCons-∙ (var₀⟪u∙σ⟫→u) is what joins SCons-∙×ShiftCons-∙.
opaque
  unfolding _∙_ ↑ₛ
  Map-∙ : ∀ {Γ Δ Θ}(u : Tm ↑ Δ)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → (u ∙ σ) ⨟ τ ≡ (u ⟪ τ ⟫) ∙ (σ ⨟ τ)
  Map-∙ u σ τ = refl
  ShiftCons-∙ : ∀ {Γ Δ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → ↑ₛ ⨟ (u ∙ σ) ≡ σ
  ShiftCons-∙ u σ = trans (wk-⨟-cons idS σ u) (IdL σ)
opaque
  unfolding _⟪_⟫ _∙_
  VarCons-∙ : ∀ {Γ Δ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → (var ⇑ os oe) ⟪ u ∙ σ ⟫ ≡ u
  VarCons-∙ u σ = refl
{-# REWRITE Map-∙ ShiftCons-∙ VarCons-∙ #-}
