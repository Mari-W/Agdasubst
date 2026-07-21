{-# OPTIONS --rewriting --local-confluence-check #-}
-- ════════════════════════════════════════════════════════════════════════════
-- Sf.SystemF — the System F LANGUAGE: one SORTED syntax `Exp : Scope → Sort`
-- (Sort = ty | tm), its uniform substitution `sub`, and its σ_SP laws.
--
-- Single-sorted: ONE substitution maps each Γ-variable of sort s to a thing of
-- sort s in Δ, and the lift under EVERY binder (∀, λ, Λ) is the same o'-based
-- wkSub.  So the type-into-term commutation that makes de-Bruijn System F hard
-- never appears at the substitution level — the σ-engine is MECHANICALLY the
-- STLC one (the laws do not care about sorts), just with more constructors.
-- ════════════════════════════════════════════════════════════════════════════
module Sf.SystemF where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Agda.Builtin.Equality.Rewrite
open import Function using (_∘_)

data Sort : Set where ty tm : Sort
open import Sf.Scaffold Sort public
variable r b : Sort

-- single-sorted System F: types and terms in one family.  Forward-declare `Exp`
-- so the sort-projections `Exp^ s`/`Ty`/`Tm` can be used in the constructor
-- signatures, making them read like the paper grammar.
data Exp : Scope → Sort → Set
Exp^ : Sort → Scope → Set
Exp^ s Γ = Exp Γ s
Ty Tm : Scope → Set
Ty = Exp^ ty
Tm = Exp^ tm
data Exp where
  var  : Exp^ r (r ∷ [])
  -- types
  _`→_ : (Ty ×ᴿ Ty) Γ          → Ty Γ
  `∀   : Bind ty Ty Γ           → Ty Γ
  -- terms
  `app : (Tm ×ᴿ Tm) Γ          → Tm Γ
  `lam : (Ty ×ᴿ Bind tm Tm) Γ  → Tm Γ   -- λ(x:A). e
  `Lam : Bind ty Tm Γ           → Tm Γ   -- Λα. e
  `App : (Tm ×ᴿ Ty) Γ          → Tm Γ   -- e [A]

-- instantiate the shared substitution CONTAINER with Exp + var
open import Sf.Sub Sort Exp var public hiding (Exp^)

-- ── the uniform substitution ACTION (σ_SP `_[_]`).  OPAQUE so IdSubst registers. ──
opaque
  sub  : ∀ {Γ Δ s} → Exp Γ s → Sub Δ Γ → Exp^ s ↑ Δ
  -- a tm-binder body (the λ binds a tm-var); the only mutually-recursive helper
  subB : ∀ {Γ Δ} → Bind tm Tm Γ → Sub Δ Γ → (Bind tm Tm) ↑ Δ
  sub var                    ([] ,- u) = u                  -- structural lookup
  sub (_`→_ (pair a₁ a₂ cv)) σ = _`→_ <$> pairUp (sub a₁ (selL cv σ)) (sub a₂ (selR cv σ))
  sub (`∀ (use t))           σ = `∀   <$> bindUp (sub t (wkSub σ ,- var₀))
  sub (`∀ (drop t))          σ = `∀   <$> (drop <$> sub t σ)
  sub (`app (pair e₁ e₂ cv)) σ = `app <$> pairUp (sub e₁ (selL cv σ)) (sub e₂ (selR cv σ))
  sub (`lam (pair a bnd cv)) σ = `lam <$> pairUp (sub a (selL cv σ)) (subB bnd (selR cv σ))
  sub (`Lam (use t))         σ = `Lam <$> bindUp (sub t (wkSub σ ,- var₀))
  sub (`Lam (drop t))        σ = `Lam <$> (drop <$> sub t σ)
  sub (`App (pair e a cv))   σ = `App <$> pairUp (sub e (selL cv σ)) (sub a (selR cv σ))
  subB (use t)  σ = bindUp (sub t (wkSub σ ,- var₀))
  subB (drop t) σ = drop <$> sub t σ

-- apply a substitution to a thing-with-thinning.  OPAQUE so `u ⟪ τ ⟫` is neutral.
opaque
  unfolding sub
  _⟪_⟫ : ∀ {Δ Θ s} → Exp^ s ↑ Δ → Sub Θ Δ → Exp^ s ↑ Θ
  (t ⇑ θ) ⟪ τ ⟫ = sub t (τ ↾ θ)
infixl 8 _⟪_⟫

-- substitution composition.  Recurses on the FIRST arg (the cons) = de-Bruijn Map.
_⨟_ : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
[]       ⨟ τ = []
(σ ,- u) ⨟ τ = (σ ⨟ τ) ,- (u ⟪ τ ⟫)
infixl 6 _⨟_

-- ════════════════════════════════════════════════════════════════════════════
-- σ-LAWS for the uniform System F `sub`.  Mechanically the STLC development; the
-- two combinator shapes (pairUp, bindUp) factor the per-constructor cases, so the
-- 7 constructors collapse to "apply the matching distribution lemma".
-- ════════════════════════════════════════════════════════════════════════════

-- selL/selR commute with composition (structural — spine only)
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

-- ════════════════════════════════════════════════════════════════════════════
-- The three term-recursive σ-base-lemmas (sub-thin, sub-fusion, sub-idS), each
-- with its mutual binder-body companion.  Per-constructor cases are uniform
-- chains of: spine commutation (selL/R-thin, selL/R-⨟, selL/R-cop) + recursive
-- IH + smart-constructor commutation (<$>-⟨⟩ / pairUp-⟨⟩ / bindUp-⟨⟩).
-- ════════════════════════════════════════════════════════════════════════════

-- renaming commutes with the System F constructor shapes (immediate from Scaffold).
-- The field families S T are passed EXPLICITLY so inference never floats.
P⟨⟩ : ∀ (S T : Scope → Set){s Δ Δ′}(f : ∀ {Γ} → (S ×ᴿ T) Γ → Exp Γ s)(A : S ↑ Δ)(B : T ↑ Δ)(ψ : Δ ⊑ Δ′)
    → (f <$> pairUp A B) ⟨ ψ ⟩ ≡ (f <$> pairUp (A ⟨ ψ ⟩) (B ⟨ ψ ⟩))
P⟨⟩ S T f A B ψ = trans (<$>-⟨⟩ (S ×ᴿ T) _ f (pairUp A B) ψ) (cong (f <$>_) (pairUp-⟨⟩ A B ψ))
B⟨⟩ : ∀ (T : Scope → Set){s Δ Δ′}(f : ∀ {Γ} → Bind ty T Γ → Exp Γ s)(X : T ↑ (ty ∷ Δ))(ψ : Δ ⊑ Δ′)
    → (f <$> bindUp X) ⟨ ψ ⟩ ≡ (f <$> bindUp (X ⟨ os ψ ⟩))
B⟨⟩ T f X ψ = trans (<$>-⟨⟩ (Bind ty T) _ f (bindUp X) ψ) (cong (f <$>_) (bindUp-⟨⟩ X ψ))

-- var₀ at the head of a lift commutes with target-thinning (shared helper).
-- `s` = the sort of the NEW binder (ty for ∀/Λ, tm for λ); passed explicitly.
opaque
  unfolding oe _⨾_
  liftThin : ∀ s {Δ Δ′ Γ}(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ)
           → (wkSub {s} (thinSub ψ σ) ,- var₀) ≡ thinSub (os ψ) (wkSub {s} σ ,- var₀)
  liftThin s ψ σ = cong₂ _,-_ (wkSub-thinSub ψ σ) (cong (var ⇑_) (cong os (sym (oe⨾ ψ))))
    where oe⨾ : ∀ {Δ Δ′}(ψ : Δ ⊑ Δ′) → oe ⨾ ψ ≡ oe
          oe⨾ oz = refl ; oe⨾ (os ψ) = cong o' (oe⨾ ψ) ; oe⨾ (o' ψ) = cong o' (oe⨾ ψ)

-- ══ sub-thin:  sub t (thinSub ψ σ) ≡ (sub t σ) ⟨ ψ ⟩ ══
opaque
  unfolding sub
  sub-thin  : ∀ {Γ Δ Δ′ s}(t : Exp Γ s)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ) → sub t (thinSub ψ σ) ≡ (sub t σ) ⟨ ψ ⟩
  subB-thin : ∀ {Γ Δ Δ′}(t : Bind tm Tm Γ)(ψ : Δ ⊑ Δ′)(σ : Sub Δ Γ)
            → subB t (thinSub ψ σ) ≡ (subB t σ) ⟨ ψ ⟩
  sub-thin var ψ ([] ,- (t ⇑ η)) = refl
  sub-thin (_`→_ (pair a b cv)) ψ σ =
    trans (cong₂ (λ X Y → _`→_ <$> pairUp X Y) (cong (sub a) (selL-thin cv ψ σ)) (cong (sub b) (selR-thin cv ψ σ)))
    (trans (cong₂ (λ X Y → _`→_ <$> pairUp X Y) (sub-thin a ψ (selL cv σ)) (sub-thin b ψ (selR cv σ)))
           (sym (P⟨⟩ Ty Ty _`→_ (sub a (selL cv σ)) (sub b (selR cv σ)) ψ)))
  sub-thin (`∀ (use t)) ψ σ =
    trans (cong (λ e → `∀ <$> bindUp (sub t e)) (liftThin ty ψ σ))
    (trans (cong (λ Z → `∀ <$> bindUp Z) (sub-thin t (os ψ) (wkSub σ ,- var₀)))
           (sym (B⟨⟩ Ty `∀ (sub t (wkSub σ ,- var₀)) ψ)))
  sub-thin (`∀ (drop t)) ψ σ = cong (λ Z → `∀ (drop (thing Z)) ⇑ thn Z) (sub-thin t ψ σ)
  sub-thin (`app (pair a b cv)) ψ σ =
    trans (cong₂ (λ X Y → `app <$> pairUp X Y) (cong (sub a) (selL-thin cv ψ σ)) (cong (sub b) (selR-thin cv ψ σ)))
    (trans (cong₂ (λ X Y → `app <$> pairUp X Y) (sub-thin a ψ (selL cv σ)) (sub-thin b ψ (selR cv σ)))
           (sym (P⟨⟩ Tm Tm `app (sub a (selL cv σ)) (sub b (selR cv σ)) ψ)))
  sub-thin (`lam (pair a bnd cv)) ψ σ =
    trans (cong₂ (λ X Y → `lam <$> pairUp X Y) (cong (sub a) (selL-thin cv ψ σ)) (cong (subB bnd) (selR-thin cv ψ σ)))
    (trans (cong₂ (λ X Y → `lam <$> pairUp X Y) (sub-thin a ψ (selL cv σ)) (subB-thin bnd ψ (selR cv σ)))
           (sym (P⟨⟩ Ty (Bind tm Tm) `lam (sub a (selL cv σ)) (subB bnd (selR cv σ)) ψ)))
  sub-thin (`Lam (use t)) ψ σ =
    trans (cong (λ e → `Lam <$> bindUp (sub t e)) (liftThin ty ψ σ))
    (trans (cong (λ Z → `Lam <$> bindUp Z) (sub-thin t (os ψ) (wkSub σ ,- var₀)))
           (sym (B⟨⟩ Tm `Lam (sub t (wkSub σ ,- var₀)) ψ)))
  sub-thin (`Lam (drop t)) ψ σ = cong (λ Z → `Lam (drop (thing Z)) ⇑ thn Z) (sub-thin t ψ σ)
  sub-thin (`App (pair a b cv)) ψ σ =
    trans (cong₂ (λ X Y → `App <$> pairUp X Y) (cong (sub a) (selL-thin cv ψ σ)) (cong (sub b) (selR-thin cv ψ σ)))
    (trans (cong₂ (λ X Y → `App <$> pairUp X Y) (sub-thin a ψ (selL cv σ)) (sub-thin b ψ (selR cv σ)))
           (sym (P⟨⟩ Tm Ty `App (sub a (selL cv σ)) (sub b (selR cv σ)) ψ)))
  subB-thin (use t) ψ σ =
    trans (cong (λ e → bindUp (sub t e)) (liftThin tm ψ σ))
    (trans (cong bindUp (sub-thin t (os ψ) (wkSub σ ,- var₀)))
           (sym (bindUp-⟨⟩ (sub t (wkSub σ ,- var₀)) ψ)))
  subB-thin (drop t) ψ σ = cong (λ Z → drop (thing Z) ⇑ thn Z) (sub-thin t ψ σ)

-- sub t (wkSub σ) = wk↑ (sub t σ)  (special case used by fusion's binder cases)
sub-wk : ∀ {s' Γ Δ s}(t : Exp Γ s)(ρ : Sub Δ Γ) → sub t (wkSub {s'} ρ) ≡ wk↑ s' (sub t ρ)
sub-wk {s'} t ρ = trans (cong (sub t) (wkSub≡thin ρ)) (trans (sub-thin t (o' oi) ρ) (sym (wk↑≡⟨⟩ s' (sub t ρ))))

-- ── distribution of ⟪_⟫ over the constructor shapes (the ⟪⟫-app↑/⟪⟫-lam↑ analogs).
-- Stated PER CONSTRUCTOR: the concrete head lets `sub`'s clause fire (an abstract
-- head `f` would block reduction).  Pair shapes use selL-cop/selR-cop; binder
-- shapes split on the body thinning and use wk-↾ / sub-wk.  All one-liners. ──
opaque
  unfolding _⟪_⟫ sub
  -- the three pure-pair shapes:
  ⟪⟫-→ : ∀ {Δ Θ}(A B : Ty ↑ Δ)(υ : Sub Θ Δ) → (_`→_ <$> pairUp A B) ⟪ υ ⟫ ≡ (_`→_ <$> pairUp (A ⟪ υ ⟫) (B ⟪ υ ⟫))
  ⟪⟫-→ (a ⇑ θ) (b ⇑ φ) υ = cong₂ (λ X Y → _`→_ <$> pairUp X Y) (cong (sub a) (selL-cop θ φ υ)) (cong (sub b) (selR-cop θ φ υ))
  ⟪⟫-app : ∀ {Δ Θ}(A B : Tm ↑ Δ)(υ : Sub Θ Δ) → (`app <$> pairUp A B) ⟪ υ ⟫ ≡ (`app <$> pairUp (A ⟪ υ ⟫) (B ⟪ υ ⟫))
  ⟪⟫-app (a ⇑ θ) (b ⇑ φ) υ = cong₂ (λ X Y → `app <$> pairUp X Y) (cong (sub a) (selL-cop θ φ υ)) (cong (sub b) (selR-cop θ φ υ))
  ⟪⟫-App : ∀ {Δ Θ}(A : Tm ↑ Δ)(B : Ty ↑ Δ)(υ : Sub Θ Δ) → (`App <$> pairUp A B) ⟪ υ ⟫ ≡ (`App <$> pairUp (A ⟪ υ ⟫) (B ⟪ υ ⟫))
  ⟪⟫-App (a ⇑ θ) (b ⇑ φ) υ = cong₂ (λ X Y → `App <$> pairUp X Y) (cong (sub a) (selL-cop θ φ υ)) (cong (sub b) (selR-cop θ φ υ))
  -- the lam shape (right field is a tm-binder, substituted by subB):
  ⟪⟫-lam : ∀ {Δ Θ sl sr}(a : Ty sl)(θ : sl ⊑ Δ)(β : Bind tm Tm sr)(φ : sr ⊑ Δ)(υ : Sub Θ Δ)
         → (`lam <$> pairUp (a ⇑ θ) (β ⇑ φ)) ⟪ υ ⟫ ≡ (`lam <$> pairUp (sub a (υ ↾ θ)) (subB β (υ ↾ φ)))
  ⟪⟫-lam a θ β φ υ = cong₂ (λ X Y → `lam <$> pairUp X Y) (cong (sub a) (selL-cop θ φ υ)) (cong (subB β) (selR-cop θ φ υ))
  -- the two ty-binder shapes (split on the body thinning):
  ⟪⟫-∀ : ∀ {Δ Θ}(X : Ty ↑ (ty ∷ Δ))(υ : Sub Θ Δ) → (`∀ <$> bindUp X) ⟪ υ ⟫ ≡ (`∀ <$> bindUp (X ⟪ wkSub υ ,- var₀ ⟫))
  ⟪⟫-∀ (t ⇑ os ξ) υ = cong (λ e → `∀ <$> bindUp (sub t (e ,- var₀))) (sym (wk-↾ υ ξ))
  ⟪⟫-∀ (t ⇑ o' ξ) υ = sym (trans (cong (λ e → `∀ <$> bindUp (sub t e)) (wk-↾ υ ξ)) (cong (λ Z → `∀ <$> bindUp Z) (sub-wk t (υ ↾ ξ))))
  ⟪⟫-Lam : ∀ {Δ Θ}(X : Tm ↑ (ty ∷ Δ))(υ : Sub Θ Δ) → (`Lam <$> bindUp X) ⟪ υ ⟫ ≡ (`Lam <$> bindUp (X ⟪ wkSub υ ,- var₀ ⟫))
  ⟪⟫-Lam (t ⇑ os ξ) υ = cong (λ e → `Lam <$> bindUp (sub t (e ,- var₀))) (sym (wk-↾ υ ξ))
  ⟪⟫-Lam (t ⇑ o' ξ) υ = sym (trans (cong (λ e → `Lam <$> bindUp (sub t e)) (wk-↾ υ ξ)) (cong (λ Z → `Lam <$> bindUp Z) (sub-wk t (υ ↾ ξ))))

-- restriction commutes with composition (spine)
↾-⨟ : ∀ {Δ Δ′ Θ sup}(τ : Sub Δ′ Δ)(θ : sup ⊑ Δ)(υ : Sub Θ Δ′) → (τ ↾ θ) ⨟ υ ≡ (τ ⨟ υ) ↾ θ
↾-⨟ []       oz     υ = refl
↾-⨟ (τ ,- u) (os θ) υ = cong (_,- (u ⟪ υ ⟫)) (↾-⨟ τ θ υ)
↾-⨟ (τ ,- u) (o' θ) υ = ↾-⨟ τ θ υ

-- weakened composition + binder-lift fusion (spine + sub-wk)
opaque
  unfolding _⟪_⟫ sub wkSub
  wkSub-⨟ : ∀ {s Γ Δ Θ}(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (wkSub {s} σ) ⨟ (wkSub υ ,- var₀) ≡ wkSub (σ ⨟ υ)
  wkSub-⨟ []             υ = refl
  wkSub-⨟ (σ ,- (t ⇑ ξ)) υ = cong₂ _,-_ (wkSub-⨟ σ υ) (trans (cong (sub t) (wk-↾ υ ξ)) (sub-wk t (υ ↾ ξ)))
opaque
  unfolding _⟪_⟫ sub
  lift-⨟ : ∀ {s Γ Δ Θ}(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (wkSub {s} σ ,- var₀) ⨟ (wkSub υ ,- var₀) ≡ wkSub (σ ⨟ υ) ,- var₀
  lift-⨟ σ υ = cong₂ _,-_ (wkSub-⨟ σ υ) (cong (λ e → sub var (e ,- var₀)) (↾-oe (wkSub υ)))

-- resubstitute a tm-binder thing-with-thinning (the Bind analog of _⟪_⟫)
_⟪_⟫B : ∀ {Δ Θ} → Bind tm Tm ↑ Δ → Sub Θ Δ → Bind tm Tm ↑ Θ
(β ⇑ φ) ⟪ υ ⟫B = subB β (υ ↾ φ)
infixl 8 _⟪_⟫B

-- ══ Clos: substitution fusion  (e[σ])[υ] = e[σ⨟υ] ══
opaque
  unfolding _⟪_⟫ sub
  sub-fusion  : ∀ {Γ Δ Θ s}(t : Exp Γ s)(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (sub t σ) ⟪ υ ⟫ ≡ sub t (σ ⨟ υ)
  subB-fusion : ∀ {Γ Δ Θ}(t : Bind tm Tm Γ)(σ : Sub Δ Γ)(υ : Sub Θ Δ) → (subB t σ) ⟪ υ ⟫B ≡ subB t (σ ⨟ υ)
  sub-fusion var ([] ,- u) υ = refl
  sub-fusion (_`→_ (pair a b cv)) σ υ =
    trans (⟪⟫-→ (sub a (selL cv σ)) (sub b (selR cv σ)) υ)
    (trans (cong₂ (λ X Y → _`→_ <$> pairUp X Y) (sub-fusion a (selL cv σ) υ) (sub-fusion b (selR cv σ) υ))
           (cong₂ (λ X Y → _`→_ <$> pairUp X Y) (cong (sub a) (sym (selL-⨟ cv σ υ))) (cong (sub b) (sym (selR-⨟ cv σ υ)))))
  sub-fusion (`∀ (use t)) σ υ =
    trans (⟪⟫-∀ (sub t (wkSub σ ,- var₀)) υ)
          (cong (λ Z → `∀ <$> bindUp Z) (trans (sub-fusion t (wkSub σ ,- var₀) (wkSub υ ,- var₀)) (cong (sub t) (lift-⨟ σ υ))))
  sub-fusion (`∀ (drop t)) σ υ = cong (λ Z → `∀ (drop (thing Z)) ⇑ thn Z) (sub-fusion t σ υ)
  sub-fusion (`app (pair a b cv)) σ υ =
    trans (⟪⟫-app (sub a (selL cv σ)) (sub b (selR cv σ)) υ)
    (trans (cong₂ (λ X Y → `app <$> pairUp X Y) (sub-fusion a (selL cv σ) υ) (sub-fusion b (selR cv σ) υ))
           (cong₂ (λ X Y → `app <$> pairUp X Y) (cong (sub a) (sym (selL-⨟ cv σ υ))) (cong (sub b) (sym (selR-⨟ cv σ υ)))))
  sub-fusion (`lam (pair a bnd cv)) σ υ =
    trans (⟪⟫-lam (thing (sub a (selL cv σ))) (thn (sub a (selL cv σ))) (thing (subB bnd (selR cv σ))) (thn (subB bnd (selR cv σ))) υ)
    (trans (cong₂ (λ X Y → `lam <$> pairUp X Y) (sub-fusion a (selL cv σ) υ) (subB-fusion bnd (selR cv σ) υ))
           (cong₂ (λ X Y → `lam <$> pairUp X Y) (cong (sub a) (sym (selL-⨟ cv σ υ))) (cong (λ s' → subB bnd s') (sym (selR-⨟ cv σ υ)))))
  sub-fusion (`Lam (use t)) σ υ =
    trans (⟪⟫-Lam (sub t (wkSub σ ,- var₀)) υ)
          (cong (λ Z → `Lam <$> bindUp Z) (trans (sub-fusion t (wkSub σ ,- var₀) (wkSub υ ,- var₀)) (cong (sub t) (lift-⨟ σ υ))))
  sub-fusion (`Lam (drop t)) σ υ = cong (λ Z → `Lam (drop (thing Z)) ⇑ thn Z) (sub-fusion t σ υ)
  sub-fusion (`App (pair a b cv)) σ υ =
    trans (⟪⟫-App (sub a (selL cv σ)) (sub b (selR cv σ)) υ)
    (trans (cong₂ (λ X Y → `App <$> pairUp X Y) (sub-fusion a (selL cv σ) υ) (sub-fusion b (selR cv σ) υ))
           (cong₂ (λ X Y → `App <$> pairUp X Y) (cong (sub a) (sym (selL-⨟ cv σ υ))) (cong (sub b) (sym (selR-⨟ cv σ υ)))))
  subB-fusion (use t) σ υ =
    trans (⟪⟫B-use (sub t (wkSub σ ,- var₀)) υ)
          (cong bindUp (trans (sub-fusion t (wkSub σ ,- var₀) (wkSub υ ,- var₀)) (cong (sub t) (lift-⨟ σ υ))))
    where -- (bindUp X) ⟪υ⟫B = bindUp (X ⟪ wkSub υ , var₀ ⟫), split on the body thinning
      ⟪⟫B-use : ∀ {Δ Θ}(X : Tm ↑ (tm ∷ Δ))(υ : Sub Θ Δ) → (bindUp X) ⟪ υ ⟫B ≡ bindUp (X ⟪ wkSub υ ,- var₀ ⟫)
      ⟪⟫B-use (t ⇑ os ξ) υ = cong (λ e → bindUp (sub t (e ,- var₀))) (sym (wk-↾ υ ξ))
      ⟪⟫B-use (t ⇑ o' ξ) υ = sym (trans (cong (λ e → bindUp (sub t e)) (wk-↾ υ ξ)) (cong bindUp (sub-wk t (υ ↾ ξ))))
  subB-fusion (drop t) σ υ = cong (λ Z → drop (thing Z) ⇑ thn Z) (sub-fusion t σ υ)

-- ⟪⟫-fusion: Clos packaged for a cons-entry
opaque
  unfolding _⟪_⟫
  ⟪⟫-fusion : ∀ {Δ Δ′ Θ s}(u : Exp^ s ↑ Δ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (u ⟪ τ ⟫) ⟪ υ ⟫ ≡ u ⟪ τ ⨟ υ ⟫
  ⟪⟫-fusion (t ⇑ θ) τ υ = trans (sub-fusion t (τ ↾ θ) υ) (cong (sub t) (↾-⨟ τ θ υ))

Ass : ∀ {Γ Δ Δ′ Θ}(σ : Sub Δ Γ)(τ : Sub Δ′ Δ)(υ : Sub Θ Δ′) → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
Ass []       τ υ = refl
Ass (σ ,- u) τ υ = cong₂ _,-_ (Ass σ τ υ) (⟪⟫-fusion u τ υ)

-- ── REWRITE GROUP: COMPOSITION MONOID (1/3) ── Clos + associativity
{-# REWRITE ⟪⟫-fusion Ass #-}

-- weakening absorbs a cons (LEMMA, not a rewrite — uses wkSub ∉ σ_SP, overlaps SCons)
opaque
  unfolding _⟪_⟫ sub wkSub
  wk-⨟-cons : ∀ {s Γ Δ Θ}(σ : Sub Δ Γ)(τ : Sub Θ Δ)(u : Exp^ s ↑ Θ) → wkSub {s} σ ⨟ (τ ,- u) ≡ σ ⨟ τ
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

-- VarCons is definitional
opaque
  unfolding sub
  VarCons-z : ∀ {Δ s}(u : Exp^ s ↑ Δ) → sub var ([] ,- u) ≡ u
  VarCons-z u = refl
{-# REWRITE VarCons-z #-}

-- restricting by oe kills the env (registered here where Exp is concrete)
↾-oe-Exp : ∀ {Θ Δ}(τ : Sub Θ Δ) → τ ↾ oe ≡ []
↾-oe-Exp = ↾-oe
{-# REWRITE ↾-oe-Exp #-}

-- substituting a field along idS, then thinning by the cover-thinning: the field
-- comes back over its own support.  `subF-idS` packages the per-field chain
-- (selL-idS → idEmb-thinSub → sub-thin → IH) shared by all pair cases.
opaque
  unfolding idS sub wkSub oe oi
  subF-idS-L : ∀ {sₗ sᵣ Γ s}(cv : Cover sₗ sᵣ Γ)(a : Exp sₗ s) → sub a idS ≡ (a ⇑ oi) → sub a (selL cv idS) ≡ (a ⇑ thinL cv)
  subF-idS-L cv a ih = trans (cong (sub a) (trans (selL-idS cv) (idEmb-thinSub (thinL cv))))
                             (trans (sub-thin a (thinL cv) idS) (cong (_⟨ thinL cv ⟩) ih))
  subF-idS-R : ∀ {sₗ sᵣ Γ s}(cv : Cover sₗ sᵣ Γ)(b : Exp sᵣ s) → sub b idS ≡ (b ⇑ oi) → sub b (selR cv idS) ≡ (b ⇑ thinR cv)
  subF-idS-R cv b ih = trans (cong (sub b) (trans (selR-idS cv) (idEmb-thinSub (thinR cv))))
                             (trans (sub-thin b (thinR cv) idS) (cong (_⟨ thinR cv ⟩) ih))
  subFB-idS-R : ∀ {sₗ sᵣ Γ}(cv : Cover sₗ sᵣ Γ)(b : Bind tm Tm sᵣ) → subB b idS ≡ (b ⇑ oi) → subB b (selR cv idS) ≡ (b ⇑ thinR cv)
  subFB-idS-R cv b ih = trans (cong (subB b) (trans (selR-idS cv) (idEmb-thinSub (thinR cv))))
                              (trans (subB-thin b (thinR cv) idS) (cong (_⟨ thinR cv ⟩) ih))

-- ══ IdSubst:  sub t idS  =  t ⇑ oi ══  (uses the library idEmb/selL-idS spine lemmas)
opaque
  unfolding idS sub wkSub oe oi
  sub-idS  : ∀ {sup s}(t : Exp sup s) → sub t idS ≡ (t ⇑ oi)
  subB-idS : ∀ {sup}(t : Bind tm Tm sup) → subB t idS ≡ (t ⇑ oi)
  sub-idS var = refl
  sub-idS (_`→_ (pair a b cv)) =
    trans (cong₂ (λ X Y → _`→_ <$> pairUp X Y) (subF-idS-L cv a (sub-idS a)) (subF-idS-R cv b (sub-idS b)))
          (cong (λ c → _`→_ (pair a b (cov c)) ⇑ out c) (cop-thin cv))
  sub-idS (`app (pair a b cv)) =
    trans (cong₂ (λ X Y → `app <$> pairUp X Y) (subF-idS-L cv a (sub-idS a)) (subF-idS-R cv b (sub-idS b)))
          (cong (λ c → `app (pair a b (cov c)) ⇑ out c) (cop-thin cv))
  sub-idS (`App (pair a b cv)) =
    trans (cong₂ (λ X Y → `App <$> pairUp X Y) (subF-idS-L cv a (sub-idS a)) (subF-idS-R cv b (sub-idS b)))
          (cong (λ c → `App (pair a b (cov c)) ⇑ out c) (cop-thin cv))
  sub-idS (`lam (pair a bnd cv)) =
    trans (cong₂ (λ X Y → `lam <$> pairUp X Y) (subF-idS-L cv a (sub-idS a)) (subFB-idS-R cv bnd (subB-idS bnd)))
          (cong (λ c → `lam (pair a bnd (cov c)) ⇑ out c) (cop-thin cv))
  sub-idS (`∀ (use t))   = cong (λ Z → `∀   <$> bindUp Z) (sub-idS t)
  sub-idS (`∀ (drop t))  = cong (λ Z → `∀ (drop (thing Z)) ⇑ thn Z) (sub-idS t)
  sub-idS (`Lam (use t)) = cong (λ Z → `Lam <$> bindUp Z) (sub-idS t)
  sub-idS (`Lam (drop t))= cong (λ Z → `Lam (drop (thing Z)) ⇑ thn Z) (sub-idS t)
  subB-idS (use t)  = cong bindUp (sub-idS t)
  subB-idS (drop t) = cong (λ Z → drop (thing Z) ⇑ thn Z) (sub-idS t)

-- sub t (idEmb θ) = t ⇑ θ   (general right-identity along a thinning)
sub-idEmb : ∀ {sup Δ s}(t : Exp sup s)(θ : sup ⊑ Δ) → sub t (idEmb θ) ≡ (t ⇑ θ)
sub-idEmb t θ = trans (cong (sub t) (idEmb-thinSub θ)) (trans (sub-thin t θ idS) (cong (_⟨ θ ⟩) (sub-idS t)))

-- ⟪_⟫-id:  u ⟪ idS ⟫ = u
opaque
  unfolding _⟪_⟫ sub
  ⟪⟫-id : ∀ {Δ s}(u : Exp^ s ↑ Δ) → u ⟪ idS ⟫ ≡ u
  ⟪⟫-id (t ⇑ θ) = trans (cong (sub t) (idS↾-idEmb θ)) (sub-idEmb t θ)

-- ══ IdR:  σ ⨟ idS  =  σ ══
IdR : ∀ {Γ Δ}(σ : Sub Δ Γ) → σ ⨟ idS ≡ σ
IdR []       = refl
IdR (σ ,- u) = cong₂ _,-_ (IdR σ) (⟪⟫-id u)

-- ── REWRITE GROUP: COMPOSITION MONOID (3/3) + IdSubst ──
{-# REWRITE ⟪⟫-id IdR sub-idS #-}

-- ════════════════════════════════════════════════════════════════════════════
-- THE CONS-LAWS on the opaque `∙` (the σ_SP completion).  `wk-⨟-cons` is NOT a
-- rewrite (uses wkSub ∉ σ_SP), so `↑ ⨟ σ` stays stuck and SCons-∙ has no
-- competing redex; ShiftCons is a lemma.
-- ════════════════════════════════════════════════════════════════════════════
opaque
  unfolding _⟪_⟫ _∙_
  VarCons-∙ : ∀ {Γ Δ s}(u : Exp^ s ↑ Δ)(σ : Sub Δ Γ) → var₀ ⟪ u ∙ σ ⟫ ≡ u
  VarCons-∙ u σ = refl
opaque
  unfolding _∙_
  Map-∙ : ∀ {Γ Δ Θ s}(u : Exp^ s ↑ Δ)(σ : Sub Δ Γ)(τ : Sub Θ Δ) → (u ∙ σ) ⨟ τ ≡ (u ⟪ τ ⟫) ∙ (σ ⨟ τ)
  Map-∙ u σ τ = refl
opaque
  unfolding _∙_ ↑ₛ
  ShiftCons-∙ : ∀ {Γ Δ s}(u : Exp^ s ↑ Δ)(σ : Sub Δ Γ) → ↑ₛ ⨟ (u ∙ σ) ≡ σ
  ShiftCons-∙ u σ = trans (wk-⨟-cons idS σ u) (IdL σ)
opaque
  unfolding _⟪_⟫ sub _∙_ ↑ₛ
  SCons-∙ : ∀ {Γ Δ s}(σ : Sub Δ (s ∷ Γ)) → (var₀ ⟪ σ ⟫) ∙ (↑ₛ ⨟ σ) ≡ σ
  SCons-∙ (σ ,- u) = cong (_,- u) (trans (wk-⨟-cons idS σ u) (IdL σ))
opaque
  unfolding _∙_ ↑ₛ idS
  IdCons-∙ : ∀ {s Γ} → var₀ ∙ (↑ₛ {s} {Γ}) ≡ idS {s ∷ Γ}
  IdCons-∙ = refl
-- ── REWRITE GROUP: CONS / η laws (the opaque-∙ σ_SP completion) ──
{-# REWRITE Map-∙ VarCons-∙ SCons-∙ ShiftCons-∙ IdCons-∙ #-}
