{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- PROBE: the co-de-Bruijn σ-calculus on a FIRST-ORDER tight-VECTOR substitution.
-- Question: with `Sub` as inductive vector data (not `Pos → Ty↑`), does the
-- binder-commutation law `lift-↾` become structural / refl (no funext)?
-- ════════════════════════════════════════════════════════════════════════════
module Clean.F.VecSub where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Equality.Rewrite
open import Clean.Pos
open import Clean.F.Ty using (Ty; var₀)

-- the FIRST-ORDER tight-vector substitution: one tight leaf per scope position,
-- finite (no shift-tail — that's the co-de-Bruijn simplification over de Bruijn).
data Sub (Δ : Scope) : Scope → Set where
  ε   : Sub Δ []
  _∙_ : ∀ {Θ} → Ty ↑ Δ → Sub Δ Θ → Sub Δ (tt ∷ Θ)
infixr 5 _∙_

-- restriction by an ARBITRARY thinning — structural recursion on the thinning
_↾_ : ∀ {Δ sup Θ} → Sub Δ Θ → sup ⊑ Θ → Sub Δ sup
ε       ↾ oz    = ε
(t ∙ σ) ↾ os θ  = t ∙ (σ ↾ θ)
(t ∙ σ) ↾ o' θ  = σ ↾ θ
infixl 8 _↾_

-- target weakening: shift every leaf by one (free — thinning compose on each leaf)
wkSub : ∀ {Δ Θ} → Sub Δ Θ → Sub (tt ∷ Δ) Θ
wkSub ε       = ε
wkSub (t ∙ σ) = (t ⟨ o' oi ⟩) ∙ wkSub σ

-- lift: the de-Bruijn shorthand — here literally a constructor + weakening
lift : ∀ {Δ Θ} → Sub Δ Θ → Sub (tt ∷ Δ) (tt ∷ Θ)
lift σ = var₀ ∙ wkSub σ

-- ════ THE TEST 1: wkSub commutes with ↾ — PURE structural induction, NO funext ════
wkSub-↾ : ∀ {Δ sup Θ}(σ : Sub Δ Θ)(θ : sup ⊑ Θ) → wkSub (σ ↾ θ) ≡ wkSub σ ↾ θ
wkSub-↾ ε       oz     = refl
wkSub-↾ (t ∙ σ) (os θ) = cong (_ ∙_) (wkSub-↾ σ θ)
wkSub-↾ (t ∙ σ) (o' θ) = wkSub-↾ σ θ
{-# REWRITE wkSub-↾ #-}

-- ════ THE TEST 2: lift-↾ — now REFL, because wkSub-↾ fired by rewrite ════
lift-↾ : ∀ {Δ Ξ sup}(σ : Sub Ξ Δ)(θ : sup ⊑ Δ) → lift (σ ↾ θ) ≡ (lift σ) ↾ (os θ)
lift-↾ σ θ = refl

-- ════ THE TEST 3: ↾-assoc — structural on the vector, BUT each recursive case needs
-- `os φ ⨾ os θ ≡ os(φ⨾θ)` etc.  That is OBSTRUCTION 3 (the thinning-category laws / the
-- `os/os` clause that won't co-orient with `⨾∘⨾`) — ORTHOGONAL to the sub representation.
-- The vector dissolved the funext wall (Tests 1–2); the residue is purely the ⨾ monoid.
