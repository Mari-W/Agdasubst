{-# OPTIONS --rewriting --local-confluence-check #-}
-- Simultaneous substitution for co-de-Bruijn λ-terms (McBride §9).
-- Environments shift WITHOUT traversal: weakening a thing-with-thinning by one
-- binder is just `o'` on the thinning — no composition, no term traversal.
-- Terminates by structural recursion alone (McBride's "surprising" §9 result).
module CDBsub where
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import CDBsig
open import CDBterm

-- the empty thinning into Δ.  OPAQUE on purpose: if it unfolded to `o' oe`,
-- then `rest oe Ψ → ε` (CDBtype) would race `rest (o' oe) Ψ` (stuck for abstract
-- Ψ) and break confluence.  Opaque ⇒ no competing redex ⇒ the rest-oe rewrite is
-- sound.  (This is the de-Bruijn "make the seam-operator opaque" trick, at the
-- thinning level.)
opaque
  oe : ∀ {Δ} → [] ⊑ Δ
  oe {[]}    = oz
  oe {_ ∷ Δ} = o' oe

-- a substitution: a thing-with-thinning in Δ for each variable of Γ
data Sub (Δ : Scope) : Scope → Set where
  []   : Sub Δ []
  _,-_ : ∀ {Γ} → Sub Δ Γ → (Tm ↑ Δ) → Sub Δ (tt ∷ Γ)
infixl 5 _,-_

-- split an env along a cover (structural — McBride: tight scope control)
selL : ∀ {Γₗ Γᵣ Γ Δ} → Cover Γₗ Γᵣ Γ → Sub Δ Γ → Sub Δ Γₗ
selL czz     []       = []
selL (css c) (σ ,- u) = selL c σ ,- u
selL (cs' c) (σ ,- u) = selL c σ ,- u
selL (c's c) (σ ,- u) = selL c σ
selR : ∀ {Γₗ Γᵣ Γ Δ} → Cover Γₗ Γᵣ Γ → Sub Δ Γ → Sub Δ Γᵣ
selR czz     []       = []
selR (css c) (σ ,- u) = selR c σ ,- u
selR (cs' c) (σ ,- u) = selR c σ
selR (c's c) (σ ,- u) = selR c σ ,- u

-- shift the whole env under one binder: just `o'` on each thinning, no traversal.
-- OPAQUE so the σ-law ShiftCons (`wkSub σ ⨟ (τ,u) ≡ σ⨟τ`) can register as a rewrite.
opaque
  wkSub : ∀ {Γ Δ} → Sub Δ Γ → Sub (tt ∷ Δ) Γ
  wkSub []             = []
  wkSub (σ ,- (t ⇑ θ)) = wkSub σ ,- (t ⇑ o' θ)

-- smart lam: the body's thinning says whether the bound var survived substitution
lam↑ : ∀ {Δ} → Tm ↑ (tt ∷ Δ) → Tm ↑ Δ
lam↑ (t ⇑ os θ) = lam (use t)  ⇑ θ
lam↑ (t ⇑ o' θ) = lam (drop t) ⇑ θ

-- the binder LIFT of a substitution: weaken the target + map the bound var to itself.
-- OPAQUE so `sub t (lift σ)` is a matchable rewrite LHS — this is what lets the σ-law
-- Inst-ƛ join IdSubst on the lam clause (lift (idEmb θ) ≡ idEmb (os θ)).
opaque
  unfolding wkSub
  lift : ∀ {Γ Δ} → Sub Δ Γ → Sub (tt ∷ Δ) (tt ∷ Γ)
  lift σ = wkSub σ ,- (var ⇑ os oe)

-- OPAQUE so the σ-law IdSubst (`sub t idS ≡ t⇑oi`) can register as a rewrite.
opaque
  unfolding wkSub
  sub : ∀ {Γ Δ} → Tm Γ → Sub Δ Γ → Tm ↑ Δ
  sub var                 ([] ,- u) = u                          -- structural lookup, no σ x
  sub (app (pair l r cv)) σ         = app↑ (sub l (selL cv σ)) (sub r (selR cv σ))
  sub (lam (use t))       σ         = lam↑ (sub t (lift σ))
  sub (lam (drop t))      σ         = let t′ ⇑ θ = sub t σ in lam (drop t′) ⇑ θ

-- variable lookup is DEFINITIONAL (no funext gap — the de-Bruijn `σ x` is gone)
opaque
  unfolding sub
  _ : ∀ {Δ}(u : Tm ↑ Δ) → sub var ([] ,- u) ≡ u
  _ = λ u → refl
