{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.STLC — the STLC LANGUAGE: its syntax `Tm`, its concrete substitution `sub`,
-- and its σ_SP laws (registered as rewrites, so substitution is DEFINITIONAL).
--
-- All the heavy, syntax-INDEPENDENT machinery lives in the shared library
-- (Sf.Thin, Sf.Scaffold, Sf.Sub).  This file is THIN: it only states the bits
-- that genuinely recurse on the STLC constructors — `sub` and the three "join"
-- lemmas sub-thin / sub-fusion / sub-idS — plus the (necessarily concrete)
-- registration of the σ-laws as rewrites.
--
-- The single sort is `⊤`: STLC has one kind of variable.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.STLC where
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Agda.Builtin.Equality.Rewrite

open import Sf.Scaffold ⊤ public

-- the co-de-Bruijn λ-syntax: a term over EXACTLY its free variables Γ
data Tm : Scope → Set where
  var : Tm (tt ∷ [])
  app : (Tm ×ᴿ Tm) Γ → Tm Γ
  lam : Bind tt Tm Γ → Tm Γ

-- smart constructors (thin wrappers over the generic pairUp/bindUp)
app↑ : ∀ {Δ} → (Tm ↑ Δ) → (Tm ↑ Δ) → Tm ↑ Δ
app↑ A B = app <$> pairUp A B
lam↑ : ∀ {Δ} → Tm ↑ (tt ∷ Δ) → Tm ↑ Δ
lam↑ X = lam <$> bindUp X

-- instantiate the shared substitution CONTAINER with Tm + var.  (Sf.Sub opens
-- Sf.Scaffold non-publicly, so this re-exports only the Sub layer — no clash
-- with the Scaffold names already in scope from the open above.)
open import Sf.Sub ⊤ (λ Γ _ → Tm Γ) var public

-- ── the substitution ACTION (σ_SP `_[_]`).  OPAQUE so IdSubst can register. ──
opaque
  sub : ∀ {Γ Δ} → Tm Γ → Sub Δ Γ → Tm ↑ Δ
  sub var                 ([] ,- u) = u                  -- structural lookup, no σ x
  sub (app (pair l r cv)) σ         = app <$> pairUp (sub l (selL cv σ)) (sub r (selR cv σ))
  sub (lam (use t))       σ         = lam <$> bindUp (sub t (wkSub σ ,- var₀))
  sub (lam (drop t))      σ         = lam <$> (drop <$> sub t σ)

-- apply a substitution to a thing-with-thinning.  OPAQUE so `u ⟪ τ ⟫` is neutral.
opaque
  unfolding sub
  _⟪_⟫ : ∀ {Δ Θ} → Tm ↑ Δ → Sub Θ Δ → Tm ↑ Θ
  (t ⇑ θ) ⟪ τ ⟫ = sub t (τ ↾ θ)
infixl 8 _⟪_⟫

-- substitution composition.  Recurses on the FIRST arg (the cons) = de-Bruijn Map.
_⨟_ : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
[]       ⨟ τ = []
(σ ,- u) ⨟ τ = (σ ⨟ τ) ,- (u ⟪ τ ⟫)
infixl 6 _⨟_

-- ════════════════════════════════════════════════════════════════════════════
-- σ-LAWS, bottom-up.  Each "join" lemma inducts on the TERM (so it cannot live
-- in the library); the generic combinator commutations come from Sf.Scaffold.
-- ════════════════════════════════════════════════════════════════════════════

-- selL/selR commute with composition (structural)
selL-⨟ : ∀ {Γₗ Γᵣ Γ Δ Θ}(cv : Cover Γₗ Γᵣ Γ)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → selL cv (σ ⨟ τ) ≡ (selL cv σ) ⨟ τ
selL-⨟ czz     []       τ = refl
selL-⨟ (css c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫)) (selL-⨟ c σ τ)
selL-⨟ (cs' c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫)) (selL-⨟ c σ τ)
selL-⨟ (c's c) (σ ,- u) τ = selL-⨟ c σ τ
selR-⨟ : ∀ {Γₗ Γᵣ Γ Δ Θ}(cv : Cover Γₗ Γᵣ Γ)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → selR cv (σ ⨟ τ) ≡ (selR cv σ) ⨟ τ
selR-⨟ czz     []       τ = refl
selR-⨟ (css c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫)) (selR-⨟ c σ τ)
selR-⨟ (cs' c) (σ ,- u) τ = selR-⨟ c σ τ
selR-⨟ (c's c) (σ ,- u) τ = cong (_,- (u ⟪ τ ⟫)) (selR-⨟ c σ τ)

-- the SUBSTITUTION coherence (Sub analog of cohL/cohR): split-of-restricted = restrict
opaque
  unfolding cop
  selL-cop : ∀ {sₗ sᵣ Δ Θ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(τ : Sub Θ Δ) → selL (cov (cop θ φ)) (τ ↾ out (cop θ φ)) ≡ τ ↾ θ
  selL-cop oz     oz     []       = refl
  selL-cop (os θ) (os φ) (τ ,- u) = cong (_,- u) (selL-cop θ φ τ)
  selL-cop (os θ) (o' φ) (τ ,- u) = cong (_,- u) (selL-cop θ φ τ)
  selL-cop (o' θ) (os φ) (τ ,- u) = selL-cop θ φ τ
  selL-cop (o' θ) (o' φ) (τ ,- u) = selL-cop θ φ τ
  selR-cop : ∀ {sₗ sᵣ Δ Θ}(θ : sₗ ⊑ Δ)(φ : sᵣ ⊑ Δ)(τ : Sub Θ Δ) → selR (cov (cop θ φ)) (τ ↾ out (cop θ φ)) ≡ τ ↾ φ
  selR-cop oz     oz     []       = refl
  selR-cop (os θ) (os φ) (τ ,- u) = cong (_,- u) (selR-cop θ φ τ)
  selR-cop (os θ) (o' φ) (τ ,- u) = selR-cop θ φ τ
  selR-cop (o' θ) (os φ) (τ ,- u) = cong (_,- u) (selR-cop θ φ τ)
  selR-cop (o' θ) (o' φ) (τ ,- u) = selR-cop θ φ τ

-- ⟪_⟫ distributes over app↑  (uses ONLY the cop coherences, no _⨾_)
opaque
  unfolding _⟪_⟫ sub
  ⟪⟫-app↑ : ∀ {Δ Θ}(A B : Tm ↑ Δ)(υ : Sub Θ Δ) → (app↑ A B) ⟪ υ ⟫ ≡ app↑ (A ⟪ υ ⟫) (B ⟪ υ ⟫)
  ⟪⟫-app↑ (l ⇑ θ) (r ⇑ φ) υ = cong₂ app↑ (cong (sub l) (selL-cop θ φ υ)) (cong (sub r) (selR-cop θ φ υ))

-- app↑ / lam↑ commute with renaming (immediate from the generic pairUp/bindUp)
app↑-⟨⟩ : ∀ {Δ Δ′}(A B : Tm ↑ Δ)(ψ : Δ ⊑ Δ′) → (app↑ A B) ⟨ ψ ⟩ ≡ app↑ (A ⟨ ψ ⟩) (B ⟨ ψ ⟩)
app↑-⟨⟩ A B ψ = trans (<$>-⟨⟩ (Tm ×ᴿ Tm) Tm app (pairUp A B) ψ) (cong (app <$>_) (pairUp-⟨⟩ A B ψ))
lam↑-⟨⟩ : ∀ {Δ Δ′}(X : Tm ↑ (tt ∷ Δ))(ψ : Δ ⊑ Δ′) → (lam↑ X) ⟨ ψ ⟩ ≡ lam↑ (X ⟨ os ψ ⟩)
lam↑-⟨⟩ X ψ = trans (<$>-⟨⟩ (Bind tt Tm) Tm lam (bindUp X) ψ) (cong (lam <$>_) (bindUp-⟨⟩ X ψ))

-- var₀ at the head of a lift commutes with target-thinning
opaque
  unfolding oe _⨾_
  liftThin : ∀ {Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ) → (wkSub (thinSub ψ σ) ,- var₀) ≡ thinSub (os ψ) (wkSub σ ,- var₀)
  liftThin ψ σ = cong₂ _,-_ (wkSub-thinSub ψ σ) (cong (var ⇑_) (cong os (sym (oe⨾ ψ))))
    where oe⨾ : ∀ {Δ Δ′}(ψ : Δ ⊑ Δ′) → oe ⨾ ψ ≡ oe
          oe⨾ oz     = refl
          oe⨾ (os ψ) = cong o' (oe⨾ ψ)
          oe⨾ (o' ψ) = cong o' (oe⨾ ψ)

-- ── SUB COMMUTES WITH RENAMING (McBride §9; `_⨾_` lives here, propositionally) ──
opaque
  unfolding sub
  sub-thin : ∀ {Γ Δ Δ′}(t : Tm Γ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ) → sub t (thinSub ψ σ) ≡ (sub t σ) ⟨ ψ ⟩
  sub-thin var ψ ([] ,- (t ⇑ η)) = refl
  sub-thin (app (pair l r cv)) ψ σ =
    trans (cong₂ app↑ (cong (sub l) (selL-thin cv ψ σ)) (cong (sub r) (selR-thin cv ψ σ)))
    (trans (cong₂ app↑ (sub-thin l ψ (selL cv σ)) (sub-thin r ψ (selR cv σ)))
           (sym (app↑-⟨⟩ (sub l (selL cv σ)) (sub r (selR cv σ)) ψ)))
  sub-thin (lam (use t)) ψ σ =
    trans (cong (λ e → lam↑ (sub t e)) (liftThin ψ σ))
    (trans (cong lam↑ (sub-thin t (os ψ) (wkSub σ ,- var₀)))
           (sym (lam↑-⟨⟩ (sub t (wkSub σ ,- var₀)) ψ)))
  sub-thin (lam (drop t)) ψ σ = cong (λ Z → lam (drop (thing Z)) ⇑ thn Z) (sub-thin t ψ σ)

-- sub t (wkSub σ) = wk↑ (sub t σ)  (special case used by the cons-laws)
sub-wk : ∀ {s Γ Δ}(t : Tm Γ)(ρ : Sub Δ Γ) → sub t (wkSub {s} ρ) ≡ wk↑ s (sub t ρ)
sub-wk {s} t ρ = trans (cong (sub t) (wkSub≡thin ρ)) (trans (sub-thin t (o' oi) ρ) (sym (wk↑≡⟨⟩ s (sub t ρ))))

-- ⟪_⟫ distributes over lam↑ (use via wk-↾; drop via sub-wk)
opaque
  unfolding _⟪_⟫ sub
  ⟪⟫-lam↑ : ∀ {Δ Θ}(X : Tm ↑ (tt ∷ Δ))(υ : Sub Θ Δ) → (lam↑ X) ⟪ υ ⟫ ≡ lam↑ (X ⟪ wkSub υ ,- var₀ ⟫)
  ⟪⟫-lam↑ (t ⇑ os ξ) υ = cong (λ e → lam↑ (sub t (e ,- var₀))) (sym (wk-↾ υ ξ))
  ⟪⟫-lam↑ (t ⇑ o' ξ) υ = sym (trans (cong (λ e → lam↑ (sub t e)) (wk-↾ υ ξ)) (cong lam↑ (sub-wk t (υ ↾ ξ))))

-- weakened composition (binder-lift fusion)
opaque
  unfolding _⟪_⟫ sub wkSub
  wkSub-⨟ : ∀ {s Γ Δ Θ}(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (wkSub {s} σ) ⨟ (wkSub υ ,- var₀) ≡ wkSub (σ ⨟ υ)
  wkSub-⨟ []             υ = refl
  wkSub-⨟ (σ ,- (t ⇑ ξ)) υ = cong₂ _,-_ (wkSub-⨟ σ υ) (trans (cong (sub t) (wk-↾ υ ξ)) (sub-wk t (υ ↾ ξ)))
opaque
  unfolding _⟪_⟫ sub
  lift-⨟ : ∀ {Γ Δ Θ}(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (wkSub σ ,- var₀) ⨟ (wkSub υ ,- var₀) ≡ wkSub (σ ⨟ υ) ,- var₀
  lift-⨟ σ υ = cong₂ _,-_ (wkSub-⨟ σ υ) (cong (λ e → sub var (e ,- var₀)) (↾-oe (wkSub υ)))

-- restriction commutes with composition
↾-⨟ : ∀ {Δ Δ′ Θ sup}(τ : Sub Δ′ Δ)(θ : sup ⊑ Δ)(υ : Sub Θ Δ′) → (τ ↾ θ) ⨟ υ ≡ (τ ⨟ υ) ↾ θ
↾-⨟ []       oz     υ = refl
↾-⨟ (τ ,- u) (os θ) υ = cong (_,- (u ⟪ υ ⟫)) (↾-⨟ τ θ υ)
↾-⨟ (τ ,- u) (o' θ) υ = ↾-⨟ τ θ υ

-- ══ Clos: substitution fusion  (e[σ])[υ] = e[σ⨟υ] ══
opaque
  unfolding _⟪_⟫ sub
  sub-fusion : ∀ {Γ Δ Θ}(t : Tm Γ)(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (sub t σ) ⟪ υ ⟫ ≡ sub t (σ ⨟ υ)
  sub-fusion var ([] ,- u) υ = refl
  sub-fusion (app (pair l r cv)) σ υ =
    trans (⟪⟫-app↑ (sub l (selL cv σ)) (sub r (selR cv σ)) υ)
    (trans (cong₂ app↑ (sub-fusion l (selL cv σ) υ) (sub-fusion r (selR cv σ) υ))
           (cong₂ app↑ (cong (sub l) (sym (selL-⨟ cv σ υ))) (cong (sub r) (sym (selR-⨟ cv σ υ)))))
  sub-fusion (lam (use t)) σ υ =
    trans (⟪⟫-lam↑ (sub t (wkSub σ ,- var₀)) υ)
          (cong lam↑ (trans (sub-fusion t (wkSub σ ,- var₀) (wkSub υ ,- var₀)) (cong (sub t) (lift-⨟ σ υ))))
  sub-fusion (lam (drop t)) σ υ = cong (λ Z → lam (drop (thing Z)) ⇑ thn Z) (sub-fusion t σ υ)

-- ⟪⟫-fusion: Clos packaged for a cons-entry
opaque
  unfolding _⟪_⟫
  ⟪⟫-fusion : ∀ {Δ Δ′ Θ}(u : Tm ↑ Δ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (u ⟪ τ ⟫) ⟪ υ ⟫ ≡ u ⟪ τ ⨟ υ ⟫
  ⟪⟫-fusion (t ⇑ θ) τ υ = trans (sub-fusion t (τ ↾ θ) υ) (cong (sub t) (↾-⨟ τ θ υ))

Ass : ∀ {Γ Δ Δ′ Θ}(σ : Sub Δ Γ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
Ass []       τ υ = refl
Ass (σ ,- u) τ υ = cong₂ _,-_ (Ass σ τ υ) (⟪⟫-fusion u τ υ)

-- ── REWRITE GROUP: COMPOSITION MONOID (1/3) ── Clos + associativity
{-# REWRITE ⟪⟫-fusion Ass #-}

-- weakening absorbs a cons (a LEMMA, NOT a rewrite — uses wkSub ∉ σ_SP, overlaps SCons)
opaque
  unfolding _⟪_⟫ sub wkSub
  wk-⨟-cons : ∀ {s Γ Δ Θ}(σ : Sub Δ Γ)(τ : Sub Θ Δ)(u : Tm ↑ Θ) → wkSub {s} σ ⨟ (τ ,- u) ≡ σ ⨟ τ
  wk-⨟-cons []             τ u = refl
  wk-⨟-cons (σ ,- (t ⇑ ξ)) τ u = cong (_,- sub t (τ ↾ ξ)) (wk-⨟-cons σ τ u)

-- ══ IdL: idS ⨟ σ = σ ══
opaque
  unfolding _⟪_⟫ idS sub wkSub
  IdL : ∀ {Γ Δ}(σ : Sub Δ Γ) → idS ⨟ σ ≡ σ
  IdL []             = refl
  IdL (σ ,- (t ⇑ ξ)) =
    cong₂ _,-_ (trans (wk-⨟-cons idS σ (t ⇑ ξ)) (IdL σ)) (cong (sub var) (cong (_,- (t ⇑ ξ)) (↾-oe σ)))
-- ── REWRITE GROUP: COMPOSITION MONOID (2/3) ── left identity
{-# REWRITE IdL #-}

-- ══ VarCons is definitional ══
opaque
  unfolding sub
  VarCons-z : ∀ {Δ}(u : Tm ↑ Δ) → sub var ([] ,- u) ≡ u
  VarCons-z u = refl
{-# REWRITE VarCons-z #-}

-- restricting by oe kills the env (registered here where Tm is concrete; in the
-- generic Sf.Sub the phantom sort left an unsolved meta)
↾-oe-Tm : ∀ {Θ Δ}(τ : Sub Θ Δ) → τ ↾ oe ≡ []
↾-oe-Tm = ↾-oe
{-# REWRITE ↾-oe-Tm #-}

-- ══ IdSubst:  sub t idS  =  t ⇑ oi ══  (uses the library idEmb/selL-idS spine lemmas)
opaque
  unfolding idS sub wkSub oe oi
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

-- sub t (idEmb θ) = t ⇑ θ   (general right-identity along a thinning)
sub-idEmb : ∀ {sup Δ}(t : Tm sup)(θ : sup ⊑ Δ) → sub t (idEmb θ) ≡ (t ⇑ θ)
sub-idEmb t θ = trans (cong (sub t) (idEmb-thinSub θ)) (trans (sub-thin t θ idS) (cong (_⟨ θ ⟩) (sub-idS t)))

-- ⟪_⟫-id:  u ⟪ idS ⟫ = u
opaque
  unfolding _⟪_⟫ sub
  ⟪⟫-id : ∀ {Δ}(u : Tm ↑ Δ) → u ⟪ idS ⟫ ≡ u
  ⟪⟫-id (t ⇑ θ) = trans (cong (sub t) (idS↾-idEmb θ)) (sub-idEmb t θ)

-- ══ IdR:  σ ⨟ idS  =  σ ══
IdR : ∀ {Γ Δ}(σ : Sub Δ Γ) → σ ⨟ idS ≡ σ
IdR []       = refl
IdR (σ ,- u) = cong₂ _,-_ (IdR σ) (⟪⟫-id u)

-- ── REWRITE GROUP: COMPOSITION MONOID (3/3) + INSTANTIATION ──
{-# REWRITE ⟪⟫-id IdR sub-idS #-}

-- ── Inst-· / Inst-ƛ are PROVEN here as lemmas (sub's clauses, exposed).  Their
-- REGISTRATION as rewrites — together with the coproduct-algebra completion
-- needed to JOIN them against IdSubst (cop-thin/cop-thin-⨾) — lives in the
-- separate Sf.STLCInst, because that completion's `cop θ φ` rewrite would race
-- the CONTEXT coherence cohL in the typing layer.  The SR proof never needs Inst
-- as a rewrite, so the typing layer (Sf.STLCTyping) imports THIS module only. ──
opaque
  unfolding sub lift
  Inst-· : ∀ {sₗ sᵣ Γ Δ}(l : Tm sₗ)(r : Tm sᵣ)(cv : Cover sₗ sᵣ Γ)(σ : Sub Δ Γ)
         → sub (app (pair l r cv)) σ ≡ app↑ (sub l (selL cv σ)) (sub r (selR cv σ))
  Inst-· l r cv σ = refl
  Inst-ƛ : ∀ {Γ Δ}(t : Tm (tt ∷ Γ))(σ : Sub Δ Γ) → sub (lam (use t)) σ ≡ lam↑ (sub t (lift σ))
  Inst-ƛ t σ = refl

-- ════════════════════════════════════════════════════════════════════════════
-- THE CONS-LAWS on the opaque `∙` (the σ_SP completion).  Stripping the
-- non-primitive `wk-⨟-cons` from the rewrite set leaves `↑ ⨟ σ` STUCK (⨟ on the
-- opaque `wkSub idS`), so SCons-∙ has no competing redex; ShiftCons is a lemma.
-- ════════════════════════════════════════════════════════════════════════════
-- VarCons:  var₀ ⟪ u ∙ σ ⟫ = u
opaque
  unfolding _⟪_⟫ _∙_
  VarCons-∙ : ∀ {Γ Δ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → var₀ ⟪ u ∙ σ ⟫ ≡ u
  VarCons-∙ u σ = refl
-- Map:  (u ∙ σ) ⨟ τ = u⟪τ⟫ ∙ (σ ⨟ τ)
opaque
  unfolding _∙_
  Map-∙ : ∀ {Γ Δ Θ}(u : Tm ↑ Δ)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → (u ∙ σ) ⨟ τ ≡ (u ⟪ τ ⟫) ∙ (σ ⨟ τ)
  Map-∙ u σ τ = refl
-- ShiftCons:  ↑ ⨟ (u ∙ σ) = σ
opaque
  unfolding _∙_ ↑ₛ
  ShiftCons-∙ : ∀ {Γ Δ}(u : Tm ↑ Δ)(σ : Sub Δ Γ) → ↑ₛ ⨟ (u ∙ σ) ≡ σ
  ShiftCons-∙ u σ = trans (wk-⨟-cons idS σ u) (IdL σ)
-- SCons / η:  (var₀ ⟪ σ ⟫) ∙ (↑ ⨟ σ) = σ
opaque
  unfolding _⟪_⟫ sub _∙_ ↑ₛ
  SCons-∙ : ∀ {Γ Δ}(σ : Sub Δ (tt ∷ Γ)) → (var₀ ⟪ σ ⟫) ∙ (↑ₛ ⨟ σ) ≡ σ
  SCons-∙ (σ ,- u) = cong (_,- u) (trans (wk-⨟-cons idS σ u) (IdL σ))
-- IdCons:  var₀ ∙ ↑ = idS
opaque
  unfolding _∙_ ↑ₛ idS
  IdCons-∙ : ∀ {Γ} → var₀ ∙ (↑ₛ {Γ = Γ}) ≡ idS {tt ∷ Γ}
  IdCons-∙ = refl
-- ── REWRITE GROUP: CONS / η laws (the opaque-∙ σ_SP completion) ──
{-# REWRITE Map-∙ VarCons-∙ SCons-∙ ShiftCons-∙ IdCons-∙ #-}

-- ════════════════════════════════════════════════════════════════════════════
-- FAITHFULNESS: wkSub and lift are DERIVED from the σ_SP shift primitive ↑ₛ,
-- not new primitives.  wkSub σ ≡ σ ⨟ ↑ₛ ;  lift σ ≡ var₀ ∙ (σ ⨟ ↑ₛ).
-- ════════════════════════════════════════════════════════════════════════════
opaque
  unfolding _⟪_⟫ sub wkSub ↑ₛ
  wkSub≡⨟↑ : ∀ {s Γ Δ}(σ : Sub Δ Γ) → wkSub {s} σ ≡ σ ⨟ ↑ₛ
  wkSub≡⨟↑ []             = refl
  wkSub≡⨟↑ (σ ,- (t ⇑ θ)) =
    cong₂ _,-_ (wkSub≡⨟↑ σ)
      (sym (trans (cong (sub t) (trans (wk-↾ idS θ) (cong wkSub (idS↾-idEmb θ))))
           (trans (sub-wk t (idEmb θ)) (cong (wk↑ _) (sub-idEmb t θ)))))
opaque
  unfolding lift _∙_
  lift≡⇑ : ∀ {s Γ Δ}(σ : Sub Δ Γ) → lift {s} σ ≡ var₀ ∙ (σ ⨟ ↑ₛ)
  lift≡⇑ σ = cong (_,- var₀) (wkSub≡⨟↑ σ)

-- ════════════════════════════════════════════════════════════════════════════
-- ∙ / ↾ INTERACTION (the core laws that REPLACE wk-↾): restricting a cons reduces
-- structurally — `os` keeps the head, `o'` drops it.  Registrable because `∙` is
-- opaque, so `(u ∙ σ) ↾ θ` is neutral (↾ cannot fire on the opaque cons).  These
-- let the binder distribution go through the registered σ-core, NOT through wk-↾.
-- ════════════════════════════════════════════════════════════════════════════
opaque
  unfolding _∙_
  ∙-↾os : ∀ {s Γ Δ Θ}(u : Exp^ s ↑ Θ)(σ : Sub Θ Γ)(ξ : Δ ⊑ Γ) → (u ∙ σ) ↾ os ξ ≡ u ∙ (σ ↾ ξ)
  ∙-↾os u σ ξ = refl
  ∙-↾o' : ∀ {s Γ Δ Θ}(u : Exp^ s ↑ Θ)(σ : Sub Θ Γ)(ξ : Δ ⊑ Γ) → (u ∙ σ) ↾ o' ξ ≡ σ ↾ ξ
  ∙-↾o' u σ ξ = refl
{-# REWRITE ∙-↾os ∙-↾o' #-}

-- wk-↾ + its completion.  PROVEN registrable conf-0 (the wkSub-[] completion joins
-- the ↾-oe critical pair) — see Sf.STLCInst where they ARE registered.  NOT global
-- here: as a global rewrite `wkSub σ ↾ θ` overlaps the substitution-coherence
-- `selL-cop` of the typing layer (same isolation reason as Inst-ƛ ∉ this module).
wk-↾-Tm : ∀ {s Θ sup Δ}(τ : Sub Θ Δ)(θ : sup ⊑ Δ) → (wkSub {s} τ) ↾ θ ≡ wkSub (τ ↾ θ)
wk-↾-Tm = wk-↾
wkSub-[]-Tm : ∀ {s Δ} → wkSub {s} ([] {Δ}) ≡ []
wkSub-[]-Tm = wkSub-[]

