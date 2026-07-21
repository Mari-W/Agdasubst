{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.Sub — LANGUAGE-INDEPENDENT substitution CONTAINER and its spine algebra.
--
-- A `Sub Δ Γ` maps each variable of Γ (of sort s) to a thing-with-thinning
-- `Exp^ s ↑ Δ`.  This module is parametric in the sorted syntax `Exp` and only
-- ever touches the ENTRIES via the generic renaming `_⟨_⟩` / `wk↑` of
-- Sf.Scaffold — it never looks inside a term.  Hence the whole spine algebra
-- (selL/selR, restriction `_↾_`, weakening `wkSub`, target-thinning `thinSub`,
-- the identity `idS`/`idEmb`) lives here, shared by every object language.
--
-- The *action* `sub`/`_⟪_⟫`/`_⨟_` and the σ-LAWS depend on the term recursion,
-- so they live in the per-language Sigma file (Sf.STLC / Sf.SystemF), built on
-- top of this container.
-- ════════════════════════════════════════════════════════════════════════════
import Agda.Builtin.List as L
-- `var` is the language's sole variable constructor (co-de-Bruijn: a var carries
-- no index — it is the unique inhabitant over the singleton support `s ∷ []`).
module Sf.Sub (I : Set)(Exp : L.List I → I → Set)
              (var : ∀ {s} → Exp (s L.∷ L.[]) s) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Sf.Scaffold I

Exp^ : I → Scope → Set
Exp^ s Γ = Exp Γ s

-- a substitution: a thing-with-thinning in Δ for each variable of Γ
data Sub (Δ : Scope) : Scope → Set where
  []   : Sub Δ []
  _,-_ : ∀ {s Γ} → Sub Δ Γ → (Exp^ s ↑ Δ) → Sub Δ (s ∷ Γ)
infixl 5 _,-_

-- ── split an env along a cover (structural — tight scope control) ──
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

-- restrict a substitution along a thinning (the Sub analog of context `rest`)
_↾_ : ∀ {Θ sup Δ} → Sub Θ Δ → sup ⊑ Δ → Sub Θ sup
[]       ↾ oz   = []
(τ ,- u) ↾ os θ = (τ ↾ θ) ,- u
(τ ,- u) ↾ o' θ = τ ↾ θ
infixl 8 _↾_

-- shift the whole env under one binder: just `o'` on each thinning, no traversal.
-- OPAQUE so `wkSub σ` is a stable head — this is what makes the restriction law
-- `wk-↾` (wkSub σ ↾ θ ≡ wkSub(σ↾θ)) a registrable rewrite LHS.  Its critical pair
-- with `↾-oe` (at θ = oe) is CLOSED by the completion `wkSub-[] : wkSub [] ≡ []`
-- (both reduce to []) — registering BOTH converges; this is the σ_SP completion,
-- not a transparency hack.
opaque
  wkSub : ∀ {s Γ Δ} → Sub Δ Γ → Sub (s ∷ Δ) Γ
  wkSub []             = []
  wkSub (σ ,- u)       = wkSub σ ,- wk↑ _ u
  -- the completion that lets wk-↾ join ↾-oe.
  wkSub-[] : ∀ {s Δ} → wkSub {s} ([] {Δ}) ≡ []
  wkSub-[] = refl

-- thin the TARGET of a substitution (renames each entry — the only spine op
-- that uses `_⨾_`, via `_⟨_⟩`).
thinSub : ∀ {Δ Δ′ Γ} → Δ ⊑ Δ′ → Sub Δ Γ → Sub Δ′ Γ
thinSub ψ []       = []
thinSub ψ (σ ,- u) = thinSub ψ σ ,- (u ⟨ ψ ⟩)

-- the fresh bound variable as a thing-with-thinning entry (var₀ = `0` in σ_SP)
var₀ : ∀ {s Δ} → Exp^ s ↑ (s ∷ Δ)
var₀ = var ⇑ os oe

-- identity substitution (σ_SP `id`).  OPAQUE so IdSubst/IdCons can register.
opaque
  idS : ∀ {Γ} → Sub Γ Γ
  idS {[]}    = []
  idS {_ ∷ Γ} = wkSub idS ,- var₀

-- identity substitution embedded along a thinning θ : sup ⊑ Δ (Sub Δ sup).
opaque
  idEmb : ∀ {sup Δ} → sup ⊑ Δ → Sub Δ sup
  idEmb oz     = []
  idEmb (os θ) = wkSub (idEmb θ) ,- var₀
  idEmb (o' θ) = wkSub (idEmb θ)

-- the σ_SP SHIFT primitive `↑`.  OPAQUE atom (≠ wkSub): general weakening
-- `wkSub σ ≡ σ ⨟ ↑` is a THEOREM, so realising ↑ as `wkSub idS` and keeping it
-- opaque is faithful — its realisation is unfolded only inside its own law-proofs.
opaque
  ↑ₛ : ∀ {s Γ} → Sub (s ∷ Γ) Γ
  ↑ₛ = wkSub idS

-- the binder LIFT (σ_SP up-arrow ⇑σ).  OPAQUE so `sub t (lift σ)` is a matchable
-- rewrite LHS — this is what lets Inst-ƛ join IdSubst on the lam clause.
opaque
  lift : ∀ {s Γ Δ} → Sub Δ Γ → Sub (s ∷ Δ) (s ∷ Γ)
  lift σ = wkSub σ ,- var₀

-- the OPAQUE cons `∙` (σ_SP cons).  Opaque because a bare constructor `_,-_` is
-- "not a legal rewrite rule" — but the opaque FUNCTION `∙` IS a legal rewrite
-- head, which is what lets the five cons-laws (VarCons/Map/ShiftCons/SCons/IdCons)
-- register as rewrites.
opaque
  _∙_ : ∀ {s Γ Δ} → Exp^ s ↑ Δ → Sub Δ Γ → Sub Δ (s ∷ Γ)
  u ∙ σ = σ ,- u
infixr 5 _∙_

-- ════════════════════════════════════════════════════════════════════════════
-- SPINE LEMMAS — selL/selR/wkSub/thinSub/_↾_ all commute with one another.
-- None looks inside a term; all are pure structural induction on the Sub spine.
-- ════════════════════════════════════════════════════════════════════════════

-- selL/selR commute with target-thinning
selL-thin : ∀ {Γₗ Γᵣ Γ Δ Δ′}(cv : Cover Γₗ Γᵣ Γ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ)
          → selL cv (thinSub ψ σ) ≡ thinSub ψ (selL cv σ)
selL-thin czz     ψ []       = refl
selL-thin (css c) ψ (σ ,- u) = cong (_,- (u ⟨ ψ ⟩)) (selL-thin c ψ σ)
selL-thin (cs' c) ψ (σ ,- u) = cong (_,- (u ⟨ ψ ⟩)) (selL-thin c ψ σ)
selL-thin (c's c) ψ (σ ,- u) = selL-thin c ψ σ
selR-thin : ∀ {Γₗ Γᵣ Γ Δ Δ′}(cv : Cover Γₗ Γᵣ Γ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ)
          → selR cv (thinSub ψ σ) ≡ thinSub ψ (selR cv σ)
selR-thin czz     ψ []       = refl
selR-thin (css c) ψ (σ ,- u) = cong (_,- (u ⟨ ψ ⟩)) (selR-thin c ψ σ)
selR-thin (cs' c) ψ (σ ,- u) = selR-thin c ψ σ
selR-thin (c's c) ψ (σ ,- u) = cong (_,- (u ⟨ ψ ⟩)) (selR-thin c ψ σ)

-- selL/selR commute with weakening
opaque
  unfolding wkSub
  selL-wk : ∀ {s Γₗ Γᵣ Γ Δ}(cv : Cover Γₗ Γᵣ Γ)(ρ : Sub Δ Γ) → selL cv (wkSub {s} ρ) ≡ wkSub (selL cv ρ)
  selL-wk czz     []       = refl
  selL-wk (css c) (ρ ,- u) = cong (_,- wk↑ _ u) (selL-wk c ρ)
  selL-wk (cs' c) (ρ ,- u) = cong (_,- wk↑ _ u) (selL-wk c ρ)
  selL-wk (c's c) (ρ ,- u) = selL-wk c ρ
  selR-wk : ∀ {s Γₗ Γᵣ Γ Δ}(cv : Cover Γₗ Γᵣ Γ)(ρ : Sub Δ Γ) → selR cv (wkSub {s} ρ) ≡ wkSub (selR cv ρ)
  selR-wk czz     []       = refl
  selR-wk (css c) (ρ ,- u) = cong (_,- wk↑ _ u) (selR-wk c ρ)
  selR-wk (cs' c) (ρ ,- u) = selR-wk c ρ
  selR-wk (c's c) (ρ ,- u) = cong (_,- wk↑ _ u) (selR-wk c ρ)

-- weakening commutes with restriction.  Registrable: wkSub opaque ⇒ `wkSub τ ↾ θ`
-- is a stable LHS; the wkSub-[] completion joins it to ↾-oe at θ = oe.
opaque
  unfolding wkSub
  wk-↾ : ∀ {s Θ sup Δ}(τ : Sub Θ Δ)(θ : sup ⊑ Δ) → (wkSub {s} τ) ↾ θ ≡ wkSub (τ ↾ θ)
  wk-↾ []       oz     = refl
  wk-↾ (τ ,- u) (os θ) = cong (_,- wk↑ _ u) (wk-↾ τ θ)
  wk-↾ (τ ,- u) (o' θ) = wk-↾ τ θ

-- restricting by the empty thinning kills the substitution.  (Registered as a
-- rewrite per-language, where Exp is concrete; oe is opaque OUTSIDE so there is
-- no `oe → o' oe` competing redex.)
opaque
  unfolding oe
  ↾-oe : ∀ {Θ Δ}(τ : Sub Θ Δ) → τ ↾ oe ≡ []
  ↾-oe []       = refl
  ↾-oe (τ ,- u) = ↾-oe τ

-- thinSub is functorial; wkSub = thinSub (o' oi)
thinSub-∘ : ∀ {Δ Δ′ Δ″ Γ}(φ : Δ ⊑ Δ′)(ψ : Δ′ ⊑ Δ″)(ρ : Sub Δ Γ)
          → thinSub ψ (thinSub φ ρ) ≡ thinSub (φ ⨾ ψ) ρ
thinSub-∘ φ ψ []       = refl
thinSub-∘ φ ψ (ρ ,- u) = cong₂ _,-_ (thinSub-∘ φ ψ ρ) (ren-∘ u φ ψ)
opaque
  unfolding wkSub
  wkSub≡thin : ∀ {s Δ Γ}(ρ : Sub Δ Γ) → wkSub {s} ρ ≡ thinSub (o' oi) ρ
  wkSub≡thin []       = refl
  wkSub≡thin {s} (ρ ,- u) = cong₂ _,-_ (wkSub≡thin ρ) (wk↑≡⟨⟩ s u)
  -- o'-variant: wkSub (thinSub ψ ρ) = thinSub (o' ψ) ρ
  wkSub-thinSub-o' : ∀ {s Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(ρ : Sub Δ Γ) → wkSub {s} (thinSub ψ ρ) ≡ thinSub (o' ψ) ρ
  wkSub-thinSub-o' ψ []       = refl
  wkSub-thinSub-o' {s} ψ (ρ ,- (t ⇑ ξ)) = cong₂ _,-_ (wkSub-thinSub-o' ψ ρ) (cong (t ⇑_) (sym (⨾-o' s ξ ψ)))
  -- os-variant: wkSub commutes with target-thinning
  wkSub-thinSub : ∀ {s Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(ρ : Sub Δ Γ) → wkSub {s} (thinSub ψ ρ) ≡ thinSub (os ψ) (wkSub ρ)
  wkSub-thinSub ψ []       = refl
  wkSub-thinSub {s} ψ (ρ ,- (t ⇑ ξ)) =
    cong₂ _,-_ (wkSub-thinSub ψ ρ) (cong (t ⇑_) (sym (⨾-os s ξ ψ)))
    where opaque
            unfolding _⨾_
            ⨾-os : ∀ {Γ Δ Θ} s (ξ : Γ ⊑ Δ)(ψ : Δ ⊑ Θ) → o' {s = s} ξ ⨾ os ψ ≡ o' (ξ ⨾ ψ)
            ⨾-os s ξ ψ = refl

-- ════════════════════════════════════════════════════════════════════════════
-- idEmb / idS SPINE LEMMAS — all pure thinning rearrangement (no term recursion),
-- so they live in the shared library.  They feed the σ-law IdSubst in the
-- per-language file.
-- ════════════════════════════════════════════════════════════════════════════

-- idEmb θ is idS renamed by θ
opaque
  unfolding wkSub idEmb idS oe _⨾_
  idEmb-thinSub : ∀ {sup Δ}(θ : sup ⊑ Δ) → idEmb θ ≡ thinSub θ idS
  idEmb-thinSub oz     = refl
  idEmb-thinSub (os θ) =
    cong₂ _,-_ (trans (cong wkSub (idEmb-thinSub θ)) (wkSub-thinSub θ idS))
               (cong (var ⇑_) (cong os (sym (oe⨾ θ))))
    where oe⨾ : ∀ {Δ Δ′}(ψ : Δ ⊑ Δ′) → oe ⨾ ψ ≡ oe
          oe⨾ oz = refl ; oe⨾ (os ψ) = cong o' (oe⨾ ψ) ; oe⨾ (o' ψ) = cong o' (oe⨾ ψ)
  idEmb-thinSub (o' θ) = trans (cong wkSub (idEmb-thinSub θ)) (wkSub-thinSub-o' θ idS)

-- thinSub is functorial through idEmb
thinSub-idEmb : ∀ {sup Δ Δ′}(ψ : Δ ⊑ Δ′)(φ : sup ⊑ Δ) → thinSub ψ (idEmb φ) ≡ idEmb (φ ⨾ ψ)
thinSub-idEmb ψ φ = trans (cong (thinSub ψ) (idEmb-thinSub φ)) (trans (thinSub-∘ φ ψ idS) (sym (idEmb-thinSub (φ ⨾ ψ))))

-- selecting idS along a cover = the embedding of the cover-thinning
opaque
  unfolding wkSub idEmb idS thinL thinR
  selL-idS : ∀ {sₗ sᵣ Γ}(cv : Cover sₗ sᵣ Γ) → selL cv idS ≡ idEmb (thinL cv)
  selL-idS czz     = refl
  selL-idS (css c) = cong (_,- var₀) (trans (selL-wk c idS) (cong wkSub (selL-idS c)))
  selL-idS (cs' c) = cong (_,- var₀) (trans (selL-wk c idS) (cong wkSub (selL-idS c)))
  selL-idS (c's c) = trans (selL-wk c idS) (cong wkSub (selL-idS c))
  selR-idS : ∀ {sₗ sᵣ Γ}(cv : Cover sₗ sᵣ Γ) → selR cv idS ≡ idEmb (thinR cv)
  selR-idS czz     = refl
  selR-idS (css c) = cong (_,- var₀) (trans (selR-wk c idS) (cong wkSub (selR-idS c)))
  selR-idS (cs' c) = trans (selR-wk c idS) (cong wkSub (selR-idS c))
  selR-idS (c's c) = cong (_,- var₀) (trans (selR-wk c idS) (cong wkSub (selR-idS c)))

-- idS ↾ θ = idEmb θ   (restriction of the identity is its embedding)
opaque
  unfolding wkSub idEmb idS thinL thinR
  idS↾-idEmb : ∀ {sup Δ}(θ : sup ⊑ Δ) → idS ↾ θ ≡ idEmb θ
  idS↾-idEmb oz     = refl
  idS↾-idEmb (os θ) = cong (_,- var₀) (trans (wk-↾ idS θ) (cong wkSub (idS↾-idEmb θ)))
  idS↾-idEmb (o' θ) = trans (wk-↾ idS θ) (cong wkSub (idS↾-idEmb θ))

-- selecting idEmb along a cover (general; uses cover-thinning composition)
selL-idEmb : ∀ {sₗ sᵣ sup Δ}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ) → selL cv (idEmb θ) ≡ idEmb (thinL cv ⨾ θ)
selL-idEmb cv θ = trans (cong (selL cv) (idEmb-thinSub θ))
                  (trans (selL-thin cv θ idS) (trans (cong (thinSub θ) (selL-idS cv)) (thinSub-idEmb θ (thinL cv))))
selR-idEmb : ∀ {sₗ sᵣ sup Δ}(cv : Cover sₗ sᵣ sup)(θ : sup ⊑ Δ) → selR cv (idEmb θ) ≡ idEmb (thinR cv ⨾ θ)
selR-idEmb cv θ = trans (cong (selR cv) (idEmb-thinSub θ))
                  (trans (selR-thin cv θ idS) (trans (cong (thinSub θ) (selR-idS cv)) (thinSub-idEmb θ (thinR cv))))
